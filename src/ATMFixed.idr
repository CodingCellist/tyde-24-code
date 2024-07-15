-- vim: set ft=idris2
||| Fixed version of the state machine from `ATMErr`, keeping track of the
||| number of remaining PIN attempts.
module ATMFixed

import Data.Vect

import QuickCheck

import Deriving.Show
%language ElabReflection

%default total


------------------------------------------------------------------------
-- Corrected ATM

||| The corrected version of the ATMState has the `CardInserted`-state track the
||| PIN-retry limit in its type
public export
data ATMState
  = Ready
  | CardInserted Nat
  | Session

public export
Show ATMState where
  show Ready = "Ready"
  show (CardInserted a) = "(CardInserted with \{show a} attempts left)"
  show Session = "Session"

public export
Eq ATMState where
  (==) Ready Ready = True
  (==) Session Session = True
  (==) (CardInserted n1) (CardInserted n2) = n1 == n2
  (==) _ _ = False


public export
data PINok
  = Correct
  | Incorrect

public export
%hint
showPINok : Show PINok
showPINok = %runElab derive


--- ||| Proof that the state is `CardInserted`. Used for Fording.
--- public export
--- data IsCI : ATMState -> Type where
---   ItIsCI : IsCI (CardInserted (S k))


||| ChkPINfn updated to take the retry limit into account, using Fording to
||| limit ourselves to only `CardInserted` states.
public export
--- ChkPINfn : (ciSt : ATMState) -> {auto ford : IsCI ciSt} -> PINok -> ATMState
--- ChkPINfn (CardInserted (S k)) {ford = ItIsCI} Correct = Session
--- ChkPINfn (CardInserted (S 0)) {ford = ItIsCI} Incorrect = Ready
--- ChkPINfn (CardInserted (S (S k))) {ford = ItIsCI} Incorrect = CardInserted (S k)
----- ChkPINfn : (tries : Nat) -> {auto canRetry : IsSucc tries} -> PINok -> ATMState
----- ChkPINfn (S 0) {canRetry=ItIsSucc} Incorrect = Ready
----- ChkPINfn (S 0) {canRetry=ItIsSucc} Correct = Session
----- ChkPINfn (S k) Correct = Session
----- ChkPINfn (S k) Incorrect = CardInserted k
ChkPINfn : (retries : Nat) -> PINok -> ATMState
---ChkPINfn 0 _ = Ready
ChkPINfn 0     Correct   = Session
ChkPINfn 0     Incorrect = Ready
ChkPINfn (S k) Correct   = Session
ChkPINfn (S k) Incorrect = CardInserted k


||| Corrected version of the ISM describing lawful ATM state transitions
public export
data ATMOp : (t : Type) -> ATMState -> (t -> ATMState) -> Type where
  Insert : ATMOp () Ready (const (CardInserted 2))
  CheckPIN :  (pin : Int)
           -> ATMOp PINok (CardInserted tries) (ChkPINfn tries)
  Dispense :  (amt : Nat)
           -> ATMOp () Session (const Session)
  Eject : ATMOp () st (const Ready)

public export
Show (ATMOp res st stFn) where
  show Insert = "Insert"
  show (CheckPIN pin) = "CheckPIN \{show pin}"
  show (Dispense amt) = "Dispense \{show amt}"
  show Eject = "Eject"

{-

||| Corrected version of the ISM describing how to chain ATM state transitions
public export
data ATM : (t : Type) -> ATMState -> (t -> ATMState) -> Type where
  Pure : (x : t) -> ATM t (stFn x) stFn
  Op : ATMOp t st st' -> ATM t st st'
  (>>=) : ATM a s1 sf -> ((x : a) -> ATM b (sf x) s3f) -> ATM b s1 s3f
  (>>) : ATM () s1 sf -> (ATM b (sf ()) s3f) -> ATM b s1 s3f


------------------------------------------------------------------------
-- Newly inadmissible examples

public export
dispense2Eject : ATM () Session (const Ready)
dispense2Eject =
  do Op $ Dispense 2
     Op Eject

failing "Mismatch between: CardInserted ?tries and Ready."
  noLoop : ATM () Ready (const Ready)
  noLoop =
    do Op Insert
       Incorrect <- Op $ CheckPIN 1234
         | Correct => dispense2Eject
       Incorrect <- Op $ CheckPIN 1243
         | Correct => dispense2Eject
       Incorrect <- Op $ CheckPIN 1432
         | Correct => dispense2Eject
       -- at 0 retries we're forced to `Ready`, so can't keep the card in forever
       Incorrect <- Op $ CheckPIN 4231
         | Correct => dispense2Eject
       ?noLoop_rhs

public export
exhaustAttempts : ATM () Ready (const Ready)
exhaustAttempts =
  do Op Insert
     Incorrect <- Op $ CheckPIN 1234
       | Correct => dispense2Eject
     Incorrect <- Op $ CheckPIN 1243
       | Correct => dispense2Eject
     Incorrect <- Op $ CheckPIN 4231
       | Correct => dispense2Eject
     -- ?exhausted   -- : ATM () Ready (\value => Ready)
     -- We're back at `Ready` at this point, the ATM has reset
     Pure ()


------------------------------------------------------------------------
-- Simulating + Tracing

public export
record OpRes (resT : Type) (currSt : ATMState) (nsFn : resT -> ATMState) where
  constructor MkOpRes

  ||| Some operation from the current state `currSt`, producing a thing of type
  ||| `resT`, and changing states according to `nsFn`.
  op : ATMOp resT currSt nsFn

  ||| The result of the operation.
  res : resT

  ||| Results must be `Show`-able
  rShow : Show resT


public export
Show (OpRes t st stFn) where
  show (MkOpRes op res resTShow) = "<ATMOp '\{show op}' with res '\{show res}'>"


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
-- Arbitrary

-- PINok
public export
Arbitrary PINok where
  arbitrary = elements [Correct, Incorrect]

  coarbitrary Correct = variant 0
  coarbitrary Incorrect = variant 1


-- ATMState
public export
Arbitrary ATMState where
  arbitrary = elements [Ready, (CardInserted 3), Session]

  coarbitrary Ready            = variant 0
  coarbitrary Session          = variant 1
  coarbitrary (CardInserted k) = variant (2 + k)


-- OpRes
public export
{currSt : ATMState} -> Arbitrary (resT : _ ** nsFn : resT -> ATMState ** OpRes resT currSt nsFn) where
  arbitrary {currSt=Ready} =
    pure (_ ** _ ** MkOpRes Insert () %search)


  arbitrary {currSt=(CardInserted 0)} =
    pure (_ ** _ ** MkOpRes Eject () %search)

  arbitrary {currSt=(CardInserted (S k))} =
    do let arbPIN = 0     -- we need _a_ PIN, even though we control the result
       let option1 = (_ ** _ ** MkOpRes (CheckPIN arbPIN) Correct %search)
       let option2 = (_ ** _ ** MkOpRes (CheckPIN arbPIN) Incorrect %search)
       let option3 = (_ ** _ ** MkOpRes Eject () %search)
       -- can adjust the frequencies of getting the PIN wrong
       frequency $ [(1, pure option1), (4, pure option2), (1, pure option3)]

  arbitrary {currSt=Session} =
    do arbAmount <- arbitrary
       let option1 = (_ ** _ ** MkOpRes (Dispense arbAmount) () %search)
       let option2 = (_ ** _ ** MkOpRes Eject () %search)
       oneof $ map pure [option1, option2]

  coarbitrary _ = assert_total $ idris_crash "OpRes coarb"


-- ATMTrace
public export
traceATM :  {iSt : ATMState}
         -> {bound : Nat}
         -> Gen (ATMTrace iSt bound)
traceATM {bound=0} = pure $ MkATMTrace iSt []   -- bound 0 leads to no trace
traceATM {bound=(S k)} =
  do (_ ** iNSFn ** fstOpR@(MkOpRes _ iRes _)) <- the (Gen (a ** b ** OpRes a iSt b)) arbitrary
     let firstTraceState = iNSFn iRes
     let atmTrace = (MkTS fstOpR firstTraceState) :: !(trace k firstTraceState)
     pure (MkATMTrace iSt atmTrace)
  where
    trace :  (steps : Nat)
          -> (currSt : ATMState)
          -> Gen (Vect steps TraceStep)
    trace 0 _ = pure []
    trace (S k) currSt =
      do (_ ** nsFn ** opR@(MkOpRes _ res _)) <- the (Gen (x ** y ** OpRes x currSt y)) arbitrary
         let nextState = nsFn res
         pure $ (MkTS opR nextState) :: !(trace k nextState)

public export
{initSt : ATMState} -> {trBound : Nat} -> Arbitrary (ATMTrace initSt trBound) where
  arbitrary = traceATM

  coarbitrary _ = assert_total $ idris_crash "ATMTrace coarb"


------------------------------------------------------------------------
-- Properties

||| Starting in `Ready` and moving a single state, we should always end up in
||| `CardInserted`
public export 0
PROP_readyInsert : Fn (ATMTrace Ready 1) Bool
PROP_readyInsert =
  MkFn (\case (MkATMTrace _ ((MkTS _ (CardInserted _)) :: trace)) => True
              (MkATMTrace _ _) => False)


||| Starting in `Ready`, we should eventually get back to `Ready` again (i.e.
||| the ATM should become available for another user)
public export 0
PROP_eventuallyReady : Fn (ATMTrace Ready 6) Bool
PROP_eventuallyReady =
  MkFn (\case (MkATMTrace _ trace) => elem Ready (map (.resSt) trace))


------------------------------------------------------------------------
-- Type-level QC

-- We STILL always move to `CardInserted` from `Ready`
public export 0
RAI_OK : So (QuickCheck False PROP_readyInsert)
RAI_OK = Oh

-- We now DO end back up in `Ready` thanks to the loop bug being fixed
public export 0
ER_OK : So (QuickCheck False PROP_eventuallyReady)
ER_OK = Oh

