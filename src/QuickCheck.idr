-- vim: set ft=idris2
||| A port of the original QuickCheck paper's Appendix A code
||| https://doi.org/10.1145/351240.351266
||| along with the snapshots from
||| https://web.archive.org/web/20010731175214/http://www.cs.chalmers.se/~rjmh/QuickCheck/QuickCheck.hs
||| https://web.archive.org/web/20081207060351/http://www.cs.chalmers.se/~rjmh/QuickCheck/QuickCheck.hs
module QuickCheck


-- N.B. without these `import public`, every module using QC would need to
--      import them for type-level QC to work

import public Data.So
import public Data.Maybe
import public Data.Primitives.Views

import public LCG


import Data.Vect
import Data.List
import Data.List1
import Data.Stream
import Data.String
import Data.SnocList


%default total


------------------------------------------------------------------------
-- 'Random' interface 

||| A value which can be encoded as an `Int` and decoded back to its original
||| type from an `Int`, can be generated randomly using a random number
||| generator.
public export
interface Random a where
  intEncode : a -> Int
  intDecode : Int -> a

  fromRInt : Int -> a
  fromRInt = intDecode

public export
Random Int where
  intEncode = id
  intDecode = id

public export
Random Integer where
  intEncode = cast
  intDecode = cast

public export
Random Nat where
  intEncode = cast
  intDecode = cast


------------------------------------------------------------------------
-- QuickCheck stuff

||| A generator is function which given a bound and the state of a randomness
||| generator returns a random element of the specified type.
public export
data Gen : Type -> Type where
  MkGen : (Int -> LCGState -> a) -> Gen a

||| Choose a random number in an interval.
public export
choose : Random a => (a, a) -> Gen a
choose (lo, hi) =
  MkGen (\n, r => (intDecode . fst) $ boundedInt r (intEncode lo) (intEncode hi))

||| Transform the generator based on the parameter `v`.
public export
variant : (v : Nat) -> Gen a -> Gen a
variant v (MkGen g) =
  MkGen (\n, r => g n (Stream.index (v + 1) $ randS r))
  where
    randS : LCGState -> Stream LCGState
    randS r0 = (\sR0 => (fst sR0) :: (randS (snd sR0))) $ splitLCG r0

||| Wrapper for function types.
||| We cannot solve interfaces for functions since (->) is not a type
||| constructor in Idris, so we need this type for function generators.
public export
data Fn : Type -> Type -> Type where
  MkFn : (a -> b) -> Fn a b

public export
Show (Fn a b) where
  show _ = "<fn>"

||| Similar to `Fn`, but dependent!
public export
data DepFn : (d : Type) -> (d -> Type) -> Type where
  MkDepFn : ((x : d) -> b x) -> DepFn d b

||| Apply a `Fn` to an argument
public export
apply : Fn a b -> a -> b
apply (MkFn f) x = f x

||| Produce a function-generator
public export
promote : (a -> Gen b) -> Gen (Fn a b)
promote f =
  MkGen (\n, r => MkFn (\a => let (MkGen m) = f a in m n r))

||| Given the current size bound, generate an `a` by passing the size bound to
||| the `Gen`'s parameter.
public export
sized : (Int -> Gen a) -> Gen a
sized fgen =
  MkGen (\n, r => let (MkGen m) = fgen n in m n r)

||| Run a generator with a given upper size bound, and an initial PRNG state.
public export
generate : Int -> LCGState -> Gen a -> a
generate n lcgSt (MkGen m) =
  let (size, lcgSt') = boundedInt lcgSt 0 n
  in m size lcgSt'

public export
Functor Gen where
  map f (MkGen g) =
    MkGen (\n, r => f (g n r))

public export
Applicative Gen where
  (<*>) (MkGen f) (MkGen g) =
    MkGen (\n, r => f n r (g n r))

  pure x = MkGen (\n, r => x)

public export
Monad Gen where
  (>>=) (MkGen g1) c =
    MkGen (\n, r0 => let (r1, r2) = splitLCG r0
                         (MkGen g2) = c (g1 n r1)
                     in g2 n r2)


||| Generate an element of the given list
public export
elements : List a -> Gen a
elements xs =
  choose (0, length xs `minus` 1) >>= (\i => pure (unsafe_index xs i))
  where
    unsafe_index : List a -> Nat -> a
    unsafe_index [] _ = assert_total $ idris_crash "elements,unsafe_index reached Nil"
    unsafe_index (x :: xs) 0 = x
    unsafe_index (x :: xs) (S k) = unsafe_index xs k

||| Pick one of the values from a list of generated ones.
public export
oneof : List (Gen a) -> Gen a
oneof gens =
  elements gens >>= id

||| Pick a random value with the given frequency (i.e. a custom probability).
public export
frequency : List (Nat, Gen a) -> Gen a
frequency xs =
  choose (1, sum (fst <$> xs)) >>= (\f => unsafe_pick f xs)
  where
    unsafe_pick : Nat -> List (Nat, Gen a) -> Gen a
    unsafe_pick n [] = assert_total $ idris_crash "frequency,unsafe_pick reached Nil"
    unsafe_pick n ((k, x) :: xs) with (compare n k)
      unsafe_pick n ((k, x) :: xs) | GT = unsafe_pick (n `minus` k) xs
      unsafe_pick n ((k, x) :: xs) | _  = x


------------------------------------------------------------------------
-- Arbitrary and coarbitrary

public export
interface Arbitrary a where
  ||| How to generate an arbitrary element of `a`.
  arbitrary : Gen a

  ||| How to construct a generator transformer based on `a`, s.t. the new
  ||| generator is independent from the old.
  -- note: we do not care about independence of gen.s at this stage...
  coarbitrary : a -> Gen b -> Gen b

public export
Arbitrary () where
  arbitrary = pure ()
  coarbitrary _ = variant 0

public export
Arbitrary Bool where
  arbitrary = elements [True, False]
  coarbitrary b = variant (if b then 0 else 1)

public export
Arbitrary Int where
  arbitrary = sized (\n => choose (-n, n))

  -- HS QC (except with a `cast`; hopefully not important...)
  coarbitrary n = variant (cast $ if n >= 0 then 2*n else 2*(-n) - 1)

public export
Arbitrary Integer where
  arbitrary = sized (\int => choose (- (cast int), cast int))
  coarbitrary n = variant (cast $ if n >= 0 then 2*n else 2*(-n) - 1)

public export
Arbitrary Char where
  arbitrary = do ic <- choose (32, 255)
                 pure (chr $ cast ic)

  coarbitrary n = variant (cast $ ord n)

public export
Arbitrary Nat where
  arbitrary = (cast . abs) <$> the (Gen Int) arbitrary
  coarbitrary n = ?coarb_nat_rhs

public export
Arbitrary a => Arbitrary b => Arbitrary (a, b) where
  arbitrary =
    do arbFst <- arbitrary
       arbSnd <- arbitrary
       pure (arbFst, arbSnd)

  coarbitrary (x, y) = coarbitrary x . coarbitrary y

public export
-- Arbitrary a => Arbitrary b => Arbitrary (a -> b) where
Arbitrary a => Arbitrary b => Arbitrary (Fn a b) where
  arbitrary =
    promote (`coarbitrary` arbitrary)

  coarbitrary f gen =
    arbitrary >>= ((`coarbitrary` gen) . (apply f))

||| Compute ( a  +  b / (|c| + 1) )
public export
fraction : (a, b, c : Integer) -> Double
fraction a b c = cast a + (cast b / ((cast $ abs c) + 1.0))

public export
Arbitrary Double where
  arbitrary =
    do a <- arbitrary
       b <- arbitrary
       c <- arbitrary
       pure $ fraction a b c

  coarbitrary n = ?coarb_double_rhs -- we are missing a `decodeFloat` equivalent


||| Generate a list of n random values.
public export
genArbList : Arbitrary a => Nat -> Gen (List a)
genArbList 0 = pure []
genArbList (S k) =
  do le  <- arbitrary
     les <- genArbList k
     pure (le :: les)

||| Generate a vect of n random values.
public export
genArbVect : Arbitrary a => (n : Nat) -> Gen (Vect n a)
genArbVect 0 = pure []
genArbVect (S k) =
  do ve  <- arbitrary
     ves <- genArbVect k
     pure (ve :: ves)

public export
Arbitrary a => Arbitrary (List a) where
  arbitrary =
    sized (\n => choose (0, n) >>= (\l => genArbList (cast l)))

  coarbitrary []        = variant 0
  coarbitrary (x :: xs) =
    variant 1 . coarbitrary x . coarbitrary xs

public export
Arbitrary a => Arbitrary (List1 a) where
  arbitrary =
    do x  <- the (Gen a) arbitrary
       xs <- the (Gen (List a)) arbitrary
       pure (x ::: xs)

  -- copied from `Arbitrary List`
  coarbitrary (x ::: xs) =
    variant 1 . coarbitrary x . coarbitrary xs

public export
Arbitrary ty => Arbitrary (n : Nat ** (Vect n ty)) where
  arbitrary =
    do l <- the (Gen Nat) arbitrary
       v <- genArbVect l {a=ty}
       pure (MkDPair l v)

  coarbitrary n = ?coarb_vect_rhs

public export
Arbitrary String where
  arbitrary =
    do chars <- the (Gen (List Char)) arbitrary
       pure (pack chars)

  coarbitrary n = ?coarb_string_rhs


------------------------------------------------------------------------
-- Properties and Results

||| The result of running a test:
|||   * the boolean result of testing
|||   * classification of test data
|||   * arguments used in the test case
public export
record Result where
  constructor MkResult
  
  ||| The boolean result of testing.
  ok : Maybe Bool

  ||| The classification of test data.
  stamp : List String

  ||| The arguments used in the test case.
  arguments : List String


||| Some property to be tested
public export
data Property : Type where
  MkProp : (Gen Result) -> Property

||| A completely blank (non-)result.
public export
nothing : Result
nothing = MkResult Nothing [] []

||| A result as a property
public export
result : Result -> Property
result r = MkProp (pure r)

||| Something which can be tested subject to a `Property`.
public export
interface Testable a where
  property : a -> Property

public export
Testable Bool where
  property b = result ({ ok := Just b} nothing)

public export
Testable Property where
  property prop = prop

||| Extract the result from a testable thing by evaluating it.
public export
evaluate : Testable a => a -> Gen Result
evaluate x = let (MkProp gRes) = property x in gRes

||| Test the given generator using a function which returns testable properties
||| for the values it generates, tracking which generated argument was used.
public export
forAll : Show a => Testable prop => Gen a -> (Fn a prop) -> Property
forAll gen fnBody =
  MkProp $ do x   <- gen
              res <- evaluate (apply fnBody x)
              pure ({ arguments $= (::) (show x) } res)

public export
-- Arbitrary a => Show a => Testable b => Testable (a -> b) where
Arbitrary a => Show a => Testable b => Testable (Fn a b) where
  property f = forAll arbitrary f

||| Only test the property if the precondition is satisfied.
public export
implies : Testable prop => Bool -> prop -> Property
implies True p = property p
implies False p = result nothing

export infixr 10 ==>

||| Shorthand for `implies`.
public export
(==>) : Testable prop => Bool -> prop -> Property
(==>) = implies

||| Evaluate the given property, stamping an additional label onto it.
public export
label : Testable prop => (s : String) -> prop -> Property
label s p =
  MkProp $ map (\res => { stamp $= (::) s } res) (evaluate p)

||| If the given boolean is `True`, label the test-case with the given name.
public export
classify : Testable prop => Bool -> (name : String) -> prop -> Property
classify True  name = label name
classify False _    = property

||| Gather the string-representation of the given value in the the given
||| property's label.
public export
collect : Show a => Testable prop => a -> prop -> Property
collect x = label (show x)


------------------------------------------------------------------------
-- Configurations

||| QuickCheck configuration specifies the maximum number of tests to run, fails
||| to accept, the size of the tests, and an `every` function (idk :shrug:).
public export
record Config where
  constructor MkConfig
  maxTest : Int
  maxFail : Int
  size : Int -> Int
  every : Int -> List String -> String

||| A small and quick default config.
public export
%inline %tcinline
quick : Config
quick =
  MkConfig 100                  -- maxTest
           100                  -- maxFail
           ((+ 3) . (`div` 2))  -- size
           -- original HS `every` clutters the log because of lack of string
           -- evaluation at runtime (doesn't handle '\b')
           -- (\n, args => let s = show n in s ++ (concat $ List.replicate (length s) "\b"))
           (\_, _ => "")

||| Same as `quick`, but printing everything.
public export
%inline %tcinline
verbose : Config
verbose = { every := (\n, args => show n ++ ":\n" ++ unlines args) } quick

||| For when `quick` is a bit too big (happens at the REPL)
public export
TinyConf : Config
TinyConf = MkConfig 2 2 ((+ 3) . (`div` 2)) (\_,_ => "")


------------------------------------------------------------------------
-- Testing (running QuickCheck)

||| The result of running QuickCheck. Contains the result of the QC run, as well
||| as the final output message.
public export
record QCRes where
  constructor MkQCRes

  ||| Did we definitely pass the tests?
  |||
  ||| `Nothing` if the arguments were exhausted without being able to tell. IT
  ||| IS UP TO YOU to decide what this means!
  pass : Maybe Bool

  ||| Log of the `every` messages.
  log : SnocList String

  ||| Final test message.
  msg : String

public export
Show QCRes where
  show (MkQCRes pass _ msg) = "MkQCRes (\{show pass}) <.log> \{msg}"


-- Taken from the original QuickCheck source using the Wayback Machine.
-- https://web.archive.org/web/20010731175214/http://www.cs.chalmers.se/~rjmh/QuickCheck/QuickCheck.hs
-- Note: read the HS file from bottom to top.

||| Print the result of the tests we did.
public export
done :  (msg : String)
     -> (nTest : Int)
     -> (log : SnocList String)
     -> (stamps : List (List String))
     -> (pass : Maybe Bool)
     -> QCRes
done msg nTest log stamps pass =
  MkQCRes pass log "\{msg} \{show nTest} tests \{table}"
  where
    percentage : Int -> Int -> String
    percentage n m = "\{show $ (100 * n) `div` m}%"

    entry : (Int, List String) -> String
    entry (n, xs) = percentage n nTest
                    ++ " "
                    ++ concat (intersperse ", " xs)

    -- this function is super odd...
    pairLength : List (List a) -> (Int, List a)
    pairLength [] = assert_total $ idris_crash "pairLength called with Nil"
    pairLength xss@(xs :: _) = (cast (length xss), xs)

    display : List String -> String
    display [] = ".\n"
    display [x] = " (" ++ x ++ ").\n"
    display xs@(_ :: _) = ".\n" ++ unlines (map (++ ".") xs)

    table : String
    table = display
          . map entry
          . reverse
          . sort
          . map pairLength
          . map toList  -- `group` returns a List (List1 a)
          . group
          . sort
          . filter (not . null)
          $ stamps

||| Check a testable property by generating instances using the given random
||| generator.
public export
tests :  (c : Config)
      -> (resGen : Gen Result)
      -> (gen : LCGState)
      -> (nTest : Int)
      -> (nFail : Int)
      -> (log : SnocList String)
      -> (stamps : List (List String))
      -> QCRes
tests c resGen gen nTest nFail log stamps with (intRec nTest) | (intRec nFail)
  tests c resGen gen .(0) nFail log stamps | IntZ | _ =
    done "OK, passed" c.maxTest log stamps (Just True)

  tests c resGen gen nTest .(0) log stamps | (IntSucc x) | IntZ =
    done "Arguments exhausted after" (c.maxTest - nTest) log stamps Nothing

  tests c resGen gen nTest nFail log stamps | (IntSucc x) | (IntSucc y) =
    let log' : SnocList String
        log' = log :< every c nTest result.arguments
    in case ok result of
            Nothing =>
               tests c resGen gen1 nTest (- 1 + nFail) log' stamps | IntSucc x | y
            (Just True) =>
               tests c resGen gen1 (- 1  + nTest) nFail log' (stamp result :: stamps) | x | IntSucc y
            (Just False) =>
               MkQCRes (Just False) log' "Falsifiable, after \{show (c.maxTest - nTest + 1)} tests:\n\{unlines result.arguments}"
    where
      splitGen : (LCGState, LCGState)
      splitGen = splitLCG gen

      gen1 : LCGState
      gen1 = fst splitGen

      gen2 : LCGState
      gen2 = snd splitGen

      result : ?
      result = generate (size c nTest) gen2 resGen

  tests c resGen gen nTest (negate n) log stamps | _ | (IntPred y) =
    assert_total $ idris_crash "tests got a negative nFail"

  tests c resGen gen (negate n) nFail log stamps | (IntPred x) | _ =
    assert_total $ idris_crash "tests got a negative nTest"

||| Check a testable property using the given `Config`.
public export
check : Testable a => Config -> a -> QCRes
check c x =
  let newGen : LCGState
      newGen = initLCG 42
  in tests c (evaluate x) newGen c.maxTest c.maxFail [<] []

||| Check a testable property using the `quick` config.
public export
test : Testable a => a -> QCRes
test = check quick

||| Check a testable property using the `quick` config.
public export
quickCheck : Testable a => a -> QCRes
quickCheck = check quick

||| Check a testable property using the `verbose` config.
public export
verboseCheck : Testable a => a -> QCRes
verboseCheck = check verbose


------------------------------------------------------------------------
-- Testing at the type level

||| Test the given property using the `quick` configuration, specifying whether
||| the test should be considered passed if the arguments were exhausted.
public export
QuickCheck : Testable t => (allowExhaust : Bool) -> (prop : t) -> Bool
QuickCheck allowExhaust prop =
  Maybe.fromMaybe allowExhaust (QuickCheck.quickCheck prop).pass

||| Test the given property using the `quick` configuration, specifying whether
||| the test should be considered passed if the arguments were exhausted.
public export
Test : Testable t => (allowExhaust : Bool) -> (prop : t) -> Bool
Test = QuickCheck

||| Test the given property using the given configuration, specifying whether
||| the test should be considered passed if the arguments were exhausted.
public export
Check :  Testable t
      => (allowExhaust : Bool)
      -> (config : Config)
      -> (prop : t)
      -> Bool
Check allowExhaust config prop =
  Maybe.fromMaybe allowExhaust (QuickCheck.check config prop).pass

public export
data Passes : Testable t => t -> Config -> Type where
  -- undecided is marked as a fail (`fromMaybe False`)
  Passed :  Testable t
         => (prop : t)
         -> (c : Config)
         -> {auto itPassed : So (Check False c prop)}
         -> Passes prop c


------------------------------------------------------------------------
-- Utils

||| Generate an example value using the default PRNG, printing and returning it.
|||
||| @ uSize  Upper size bound, 30 by default
||| @ seed   PRNG seed, 42 by default
public export
example :  (Show a, Arbitrary a)
        => {default 30 uSize : Int}
        -> {default 42 seed  : Int}
        -> IO a
example =
  let ex = generate uSize (initLCG seed) arbitrary
  in do printLn ex
        pure ex


||| A default PRNG state, created by initialising the seed to 42 of course!
public export
DEFAULT_PRNG : LCGState
DEFAULT_PRNG = initLCG 42

