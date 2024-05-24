-- vim: set ft=idris2
||| The ATM model from Type Driven Development with Idris, chapter 14. Contains
||| a subtle bug in the specification/model, which QuickCheck is able to detect.
module ATMErr

import Data.Vect

import QuickCheck

import Deriving.Show
%language ElabReflection

%default total


------------------------------------------------------------------------
-- ATM state- and result-types

||| Possible states for the ATM
public export
data ATMState
  = Ready
  | CardInserted
  | Session

public export
%hint
showATMState : Show ATMState
showATMState = %runElab derive

public export
Eq ATMState where
  (==) Ready        Ready        = True
  (==) CardInserted CardInserted = True
  (==) Session      Session      = True
  (==) _            _            = False


||| PIN input is either correct or incorrect
public export
data PINok
  = Correct
  | Incorrect

public export
%hint
showPINok : Show PINok
showPINok = %runElab derive


------------------------------------------------------------------------
-- ATM ISM Types

public export
ChkPINfn : PINok -> ATMState
ChkPINfn Correct = Session
ChkPINfn Incorrect = CardInserted


||| Indexed State Monad (ISM) describing lawful ATM state transitions
public export
data ATMOp : (t : Type) -> ATMState -> (t -> ATMState) -> Type where
  Insert : ATMOp () Ready (const CardInserted)
  CheckPIN :  (pin : Int)
           -> ATMOp PINok CardInserted ChkPINfn
  Dispense :  (amt : Nat)
           -> ATMOp () Session (const Session)
  Eject : ATMOp () st (const Ready)


public export
Show (ATMOp res st stFn) where
  show Insert = "Insert"
  show (CheckPIN pin) = "CheckPIN \{show pin}"
  show (Dispense amt) = "Dispense \{show amt}"
  show Eject = "Eject"


||| Indexed State Monad (ISM) describing how to chain ATM state transitions
public export
data ATM : (t : Type) -> ATMState -> (t -> ATMState) -> Type where
     Pure : (x : t) -> ATM t (stFn x) stFn
     Op : ATMOp t st st' -> ATM t st st'

     ||| Bind
     (>>=) : ATM a s1 s2f -> ((x : a) -> ATM b (s2f x) s3f) -> ATM b s1 s3f

     ||| Seq (as in "sequence")
     (>>) : ATM () s1 s2f -> (ATM b (s2f ()) s3f) -> ATM b s1 s3f


------------------------------------------------------------------------
-- Next state function

||| We can extract the state function from the type itself, provided we remain
||| at the type-level (Rig0).
public export 0
nextState :  (st : ATMState)
          -> ATMOp t st nsFn
          -> (res : t)
          -> ATMState
nextState st _ res = nsFn res


------------------------------------------------------------------------
-- Supporting types (OpRes, TraceStep, and Trace)

-- `Testable (Fn t Bool)` requires `Show t` (and `Arbitrary t`)
public export
Show (t : Type ** nsFn : t -> ATMState ** ATMOp t st nsFn) where
  show (_ ** _ ** op) = show op


||| A current state paired with a valid operation on the state along with a
||| possible result of the operation.
|||
||| @ resT   The type of the result of the operation.
||| @ currSt The current state of the ATM state machine.
||| @ nsFn   The next-state function, changing states according to the result
|||            of the operation in the current state.
public export
record OpRes (resT : Type) (currSt : ATMState) (nsFn : resT -> ATMState) where
  constructor MkOpRes

  ||| Some operation from the current state `currSt`, producing a thing of type
  ||| `resT`, and changing states according to `nsFn`.
  op : ATMOp resT currSt nsFn

  ||| The result of the operation.
  res : resT

  ||| Results must be `Show`-able for QC to work
  {auto rShow : Show resT}


public export
Show (OpRes t st stFn) where
  show (MkOpRes op res) = "<ATMOp '\{show op}' with res '\{show res}'>"


||| A step in a trace consists of the `OpRes` that led to it, and the resulting
||| `ATMState`
public export
record TraceStep where
  constructor MkTS

  ||| The `ATMOp` along with some result, which took us to the state
  opRes : OpRes rT aSt aStFn

  ||| The `ATMState` we ended up in
  resSt : ATMState


public export
Show TraceStep where
  show (MkTS opRes resSt) = "(\{show opRes}, \{show resSt})"


||| An initial state along with a sequence of states that follow from it via
||| op.s.
public export
data ATMTrace : ATMState -> Nat -> Type where
  MkATMTrace :  (initSt : ATMState)
             -> {bound : Nat}
             -> (trace : Vect bound TraceStep)
             -> ATMTrace initSt bound


public export
Show (ATMTrace iSt _) where
  show (MkATMTrace iSt trace) = "Starting @ \{show iSt}: \{show trace}"


------------------------------------------------------------------------
-- Arbitrary instances

||| We can generate arbitrary `ATMState`s by picking one of the three states. 
public export
Arbitrary ATMState where
  arbitrary = elements [Ready, CardInserted, Session]

  coarbitrary Ready        = variant 0
  coarbitrary CardInserted = variant 1
  coarbitrary Session      = variant 2


||| We can generate arbitrary `PINok` (result of `CheckPIN`) by picking one of
||| `Correct` or `Incorrect`.
public export
Arbitrary PINok where
  arbitrary = elements [Correct, Incorrect]

  coarbitrary Correct   = variant 0
  coarbitrary Incorrect = variant 1


-- How to generate a single operation-result pair (an `OpRes`)
public export
{currSt : ATMState} -> Arbitrary (resT : _ ** nsFn : resT -> ATMState ** OpRes resT currSt nsFn) where
  arbitrary {currSt=Ready} =
    pure (_ ** _ ** MkOpRes Insert ())

  arbitrary {currSt=CardInserted} =
    do let arbPIN = 0     -- we need _a_ PIN, even though we control the result
       let option1 = (_ ** _ ** MkOpRes (CheckPIN arbPIN) Correct)
       let option2 = (_ ** _ ** MkOpRes (CheckPIN arbPIN) Incorrect)
       let option3 = (_ ** _ ** MkOpRes Eject ())
       -- can adjust the frequencies of getting the PIN wrong
       frequency $ [(1, pure option1), (4, pure option2), (1, pure option3)]

  arbitrary {currSt=Session} =
    do arbAmount <- arbitrary
       let option1 = (_ ** _ ** MkOpRes (Dispense arbAmount) ())
       let option2 = (_ ** _ ** MkOpRes Eject ())
       oneof $ map pure [option1, option2]

  coarbitrary _ = assert_total $ idris_crash "OpRes coarb"


public export
traceATM :  {iSt : ATMState}
         -> {bound : Nat}
         -> Gen (ATMTrace iSt bound)
traceATM {bound=0} = pure $ MkATMTrace iSt []   -- bound 0 leads to no trace
traceATM {bound=(S k)} =
  do (_ ** iNSFn ** fstOpR@(MkOpRes _ iRes)) <- the (Gen (a ** b ** OpRes a iSt b)) arbitrary
     let firstTraceState = iNSFn iRes
     let atmTrace = (MkTS fstOpR firstTraceState) :: !(trace k firstTraceState)
     pure (MkATMTrace iSt atmTrace)
  where
    trace :  (steps : Nat)
          -> (currSt : ATMState)
          -> Gen (Vect steps TraceStep)
    trace 0 _ = pure []
    trace (S k) currSt =
      do (_ ** nsFn ** opR@(MkOpRes _ res)) <- the (Gen (x ** y ** OpRes x currSt y)) arbitrary
         let nextState = nsFn res
         pure $ (MkTS opR nextState) :: !(trace k nextState)
         -- The details for how we arrive at this can be found in Section 3.5 of
         -- the paper


public export
{initSt : ATMState} -> {trBound : Nat} -> Arbitrary (ATMTrace initSt trBound) where
  arbitrary = traceATM

  coarbitrary _ = assert_total $ idris_crash "ATMTrace coarb"


------------------------------------------------------------------------
-- Properties

-- need to `:set eval tc` at REPL to inspect result of a Rig0 QC

||| Starting in `Ready` and moving a single state, we should always end up in
||| `CardInserted`
public export 0
PROP_readyInsert : Fn (ATMTrace Ready 1) Bool
PROP_readyInsert =
  MkFn (\case (MkATMTrace _ ((MkTS _ CardInserted) :: trace)) => True
              (MkATMTrace _ _) => False)


||| Starting in `Ready`, we should eventually get back to `Ready` again (i.e.
||| the ATM should become available for another user)
public export 0
PROP_eventuallyReady : Fn (ATMTrace Ready 10) Bool
PROP_eventuallyReady =
  MkFn (\case (MkATMTrace _ trace) => elem Ready (map (.resSt) trace))


------------------------------------------------------------------------
-- Type-level checking of properties

-- We DO always move to `CardInserted` from `Ready`
public export 0
RI_OK : So (QuickCheck False PROP_readyInsert)
RI_OK = Oh


-- We DO NOT always end back up in `Ready` within a reasonable time
failing "Mismatch between: True and False"
  public export 0
  ER_OK : So (QuickCheck False PROP_eventuallyReady)
  ER_OK = Oh


------------------------------------------------------------------------
-- Implementation examples

||| Example of a faulty, but legal, ATM program implementation
public export covering
faultyImpl : ATM () Ready (const Ready)
faultyImpl =
  do Op Insert
     loopCheckPIN 94
  where
    loopCheckPIN : Int -> ATM () CardInserted (const Ready)
    loopCheckPIN pin =
      do Incorrect <- Op $ CheckPIN pin
            | Correct => do Op $ Dispense 1
                            Op Eject
         loopCheckPIN pin


||| Example ATM program implementation
public export
impl : ATM () Ready (const Ready)
impl =
  do Op Insert
     Correct <- Op $ CheckPIN 94
      | Incorrect => Op Eject
     Op $ Dispense 1
     Op Eject

