-- vim: set ft=idris2
module ARQ

import Generic

import Data.Nat
import Data.Bits
import Decidable.Equality

import Deriving.Show
%language ElabReflection

%default total


------------------------------------------------------------------------
-- Types

public export
record Pkt where
  constructor MkPkt
  pl : Bits8
  sn : Nat


public export
data WaitRes
  = Ack Nat
  | Timeout


public export
data ARQState
  = Ready Nat
  | Waiting Nat
  | Acked Nat Nat


public export
data IsWaiting : ARQState -> Type where
  ItIsWaiting : IsWaiting (Waiting n)


public export
Next : (st : ARQState) -> {auto ford : IsWaiting st} -> WaitRes -> ARQState
Next (Waiting n) {ford=ItIsWaiting} (Ack a) = Acked n a
Next (Waiting n) {ford=ItIsWaiting} Timeout = Ready n


public export
data ARQOp : (t : _) -> ARQState -> (t -> ARQState) -> Type where
  Send : (pkt : Pkt) -> ARQOp () (Ready pkt.sn) (const $ Waiting (pkt.sn))
  Wait : ARQOp WaitRes (Waiting n) (Next (Waiting n))
  Proceed : (ok : a === n) -> ARQOp () (Acked n a) (const $ Ready (S n))
  Retry : (Not (a === n)) -> ARQOp () (Acked n a) (const $ Ready n)


------------------------------------------------------------------------
-- Interfaces

public export
Show Pkt where
  show (MkPkt pl sn) = "<Pkt \{show pl} \{show sn}>"


public export
%hint
showWR : Show WaitRes
showWR = %runElab derive


public export
Show ARQState where
  show (Ready n) = "(Ready \{show n})"
  show (Waiting n) = "(Waiting \{show n})"
  show (Acked n a) = "(Acked \{show n} with \{show a})"


public export
Eq ARQState where
  (==) (Ready n1) (Ready n2) = n1 == n2
  (==) (Waiting n1) (Waiting n2) = n1 == n2
  (==) (Acked n1 a1) (Acked n2 a2) = n1 == n2 && a1 == a2
  (==) _ _ = False


public export
Show (ARQOp t st stFn) where
  show (Send pkt) = "(Send \{show pkt})"
  show Wait = "(Wait)"
  show (Proceed _) = "(Proceed)"
  show (Retry _) = "(Retry)"


------------------------------------------------------------------------
-- Traceable

public export
Traceable ARQOp where
  options (Ready k) =
    singular (_ ** _ ** MkOpRes (Send (MkPkt 255 k)) ())

  options (Waiting k) =
    -- note: have to do things manually here bc we want to include `Ack n` s.t.
    --       n =/= k
    [ (4, pure (_ ** _ ** MkOpRes Wait Timeout))                -- 20%
    , (1, do pure (_ ** _ ** MkOpRes Wait (Ack !arbitrary)))    --  5%
    , (15, pure (_ ** _ ** MkOpRes Wait (Ack k)))               -- 75%
    ]

  options (Acked n a) =
    case decEq a n of
         (Yes prf) => singular (_ ** _ ** MkOpRes (Proceed prf) ())
         (No contra) => singular (_ ** _ ** MkOpRes (Retry contra) ())


------------------------------------------------------------------------
-- Properties

public export
0 PROP_sendThreeOK : Fn (Trace ARQOp (Ready 0) 20) Bool
PROP_sendThreeOK = MkFn
  (\case (MkTrace _ trace) => elem' (Ready 3) $ (.resSt) <$> trace)
  where
    -- this is (annoyingly) ~1s faster than `Builtin.elem`
    elem' : Eq a => a -> Vect _ a -> Bool
    elem' _ [] = False
    elem' e (x :: xs) = (e == x) || (elem' e xs)


------------------------------------------------------------------------
-- Type-level QC

public export
0 QC_sendThreeOK : So (QuickCheck False PROP_sendThreeOK)
QC_sendThreeOK = Oh


------------------------------------------------------------------------
-- Programs

public export
covering
sendN : (n : Nat) -> Prog ARQOp () (Ready n) (const $ Ready (S n))
sendN n = do
  Op $ Send (MkPkt 255 n)
  (Ack a) <- Op Wait
    | Timeout => sendN n
  case decEq a n of
       (Yes prf) => Op $ Proceed prf
       (No contra) => do
         Op $ Retry contra
         sendN n


public export
covering
prog : Prog ARQOp () (Ready 0) (const $ Ready 3)
prog = do
  sendN 0
  sendN 1
  sendN 2


failing "Mismatch between: 1 and 0"
  bad : Prog ARQOp () (Ready 0) (const $ Ready 2)
  bad = do sendN 1

