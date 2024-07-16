-- vim: set ft=idris2
module Generic

import public Data.Vect

import public QuickCheck


------------------------------------------------------------------------
-- Types

-- Prog

||| The generic type of a program, indexed over the Type of operations
||| permitted, producing a result of some type, starting in a given state, and
||| ending in a state dependent on the result type.
|||
||| @ stT   The Type of the states used in the program
||| @ opT   The Type of operations permitted
||| @ t     The Type of result produced by the program
||| @ from  The initial state of the program
||| @ to    The function describing the end state of the program based on the
|||         result type
public export
data Prog :  {0 stT : _}
          -> (opT : (t' : _) -> stT -> (t' -> stT) -> Type)
          -> (t : Type)
          -> (from : stT)
          -> (to : t -> stT)
          -> Type
  where
    Pure : (x : t) -> Prog opT t (stFn x) stFn

    Op :  {0 opT : (t' : _) -> stT -> (t' -> stT) -> Type}
       -> opT t st stFn
       -> Prog opT t st stFn

    ||| Bind
    (>>=) : Prog opT resT1 st1 stFn1
          -> ((x : resT1) -> Prog opT resT2 (stFn1 x) stFn2)
          -> Prog opT resT2 st1 stFn2

    ||| Seq (as in "sequence")
    (>>) :  Prog opT () st1 stFn1
         -> (Prog opT resT2 (stFn1 ()) stFn2)
         -> Prog opT resT2 st1 stFn2


-- OpRes

||| The generic Type of an operation and the Type of result it produced, along
||| with the state it happened in and the function describing how to process the
||| result to change state.
|||
||| @ stT     The Type of the states used
||| @ opT     The Type of operation permitted in this state
||| @ resT    The Type of result produced by the operations
||| @ currSt  The concrete `stT` which the operation was performed on
||| @ nsFn    The function describing how to move to a new `stT` based on
|||           something given of type `resT`
public export
record OpRes {0 stT : _}
             (opT : (t' : _) -> stT -> (t' -> stT) -> Type)
             (resT : Type)
             (currSt : stT)
             (0 nsFn : resT -> stT) where
  constructor MkOpRes
  ||| The concrete operation (i.e. instance of `opT`) which was used
  op : opT resT currSt nsFn
  ||| The concrete instance of `resT` the operation produced as its result
  res : resT
  {auto opShow : Show (opT resT currSt nsFn)}
  {auto rShow : Show resT}


-- TraceStep

public export
record TraceStep (opT : (t' : _) -> stT -> (t' -> stT) -> Type) where
  constructor MkTS

  -- All of these can be implicitly unified in the specific case, but it seems
  -- Idris struggles in the general case
  --
  {0 stepRT : _}
  {0 stepSt : stT}
  -- next-state function
  {0 stepFn : stepRT -> stT}

  -- the result type must be Show-able
  {auto showStT : Show stT}

  opRes : OpRes opT stepRT stepSt stepFn
  resSt : stT


-- Trace

public export
data Trace :  (opT : (t' : _) -> stT -> (t' -> stT) -> Type)
           -> stT
           -> Nat
           -> Type where
  MkTrace :  Show stT
          => (initSt : stT)
          -> {bound : Nat}
          -> (trace : Vect bound (TraceStep opT))
          -> Trace opT initSt bound


------------------------------------------------------------------------
-- Traceable

----- ||| An operation type is said to be traceable if for some given state, we can
----- ||| produce a list of valid transitions away from that state, along with a
----- ||| result they might have produced. (This result could be `arbitrary` although
----- ||| it does not have to be.)
----- public export
----- interface Traceable (0 opT : (t' : _) -> stT -> (t' -> stT) -> Type) where
----- ---  options :  (st : stT)
----- ---          -> List (Nat, Gen (resT : Type ** nsFn : resT -> stT ** OpRes opT resT st nsFn))
-----   options :  (st : stT)
-----           -> Gen (resT : Type ** nsFn : resT -> stT ** OpRes opT resT st nsFn)


||| When there is only a singular option, wrap it in a `pure` call with a
||| frequency of 1/1.
public export
singular :  {0 stT : _}
         -> {0 opT : (t' : _) -> stT -> (t' -> stT) -> Type}
         -> {st : stT}
         -> (resT : Type ** nsFn : resT -> stT ** OpRes opT resT st nsFn)
         -> List (Nat, Gen (resT : Type ** nsFn : resT -> stT ** OpRes opT resT st nsFn))
singular option = [(1, pure option)]


||| Given a list of options, choose one of them at random, i.e. give each option
||| equal weighting.
public export
choice :  {0 stT : _}
       -> {0 opT : (t' : _) -> stT -> (t' -> stT) -> Type}
       -> {st : stT}
       -> List (resT : Type ** nsFn : resT -> stT ** OpRes opT resT st nsFn)
       -> List (Nat, Gen (resT : Type ** nsFn : resT -> stT ** OpRes opT resT st nsFn))
choice xs = map (MkPair 1) (pure <$> xs)


||| Given a number of options and matching number of weights, make the options
||| `pure` generators and pair them with their weigths.
|||
||| @ weights The weighting of each option
||| @ opts    The possible options
public export
weighted :  {0 stT : _}
         -> {0 opT : (t' : _) -> stT -> (t' -> stT) -> Type}
         -> {st : stT}
         -> (weights : Vect nOptions Nat)
         -> (opts : Vect nOptions (resT : Type ** nsFn : resT -> stT ** OpRes opT resT st nsFn))
         -> List (Nat, Gen (resT : Type ** nsFn : resT -> stT ** OpRes opT resT st nsFn))
weighted weights opts = toList $ zip weights (pure <$> opts)


------------------------------------------------------------------------
-- Show

public export
Show (OpRes opT resT currSt nsFn) where
  show (MkOpRes op res) = "<Op '\{show op}' ~ '\{show res}'>"


public export
Show (TraceStep opT) where
  show (MkTS opRes resSt) = "(\{show opRes}, \{show resSt})"


public export
Show (Trace opT iSt _) where
  show (MkTrace iSt trace) = "Starting @ \{show iSt}: \{show trace}"


------------------------------------------------------------------------
-- Arbitrary

----- public export
----- {0 stT : _} -> {0 opT : _} -> {st : stT} -> Traceable opT =>
----- Arbitrary (resT : Type ** nsFn : resT -> stT ** OpRes opT resT st nsFn) where
-----   --- arbitrary {st} = frequency $ options st
-----   arbitrary {st} = options st
----- 
-----   coarbitrary x = assert_total $ idris_crash "coarb: OpRes"

public export
{0 stT : _} -> {iSt : stT} -> {bound : Nat} ->
{opT : (t' : Type) -> stT -> (t' -> stT) -> Type} ->
Show stT =>
----- Traceable opT =>
Arbitrary (resT ** nsFnT ** OpRes opT resT iSt nsFnT) =>
Arbitrary (Trace opT iSt bound) where
  arbitrary {bound = 0} = pure $ MkTrace iSt []
  arbitrary {bound = (S k)} =
    do (_ ** nsFn ** opRes@(MkOpRes op res)) <- the (Gen (rT ** fnT ** OpRes opT rT iSt fnT)) arbitrary
       let fstTraceSt = nsFn res
       let traceHead = MkTS opRes fstTraceSt
       traceTail <- trace k fstTraceSt
       pure (MkTrace iSt (traceHead :: traceTail))
    where
      trace :  (steps : Nat)
            -> (st : stT)
            -> Gen (Vect steps (TraceStep opT))
            {-
      trace 0 _ = pure []
      trace (S j) st =
        do (_ ** stFn ** opR@(MkOpRes op res)) <- the (Gen (x ** y ** OpRes opT x st y)) arbitrary
           let nextSt = stFn res
           pure $ (MkTS opR nextSt) :: !(trace j nextSt)
           -}

  coarbitrary x = assert_total $ idris_crash "coarb: Trace"

