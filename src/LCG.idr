||| Simple Linear Congruential Generator
||| DO NOT USE FOR ANYTHING WHERE THE STRENGTH OF THE CRYPTOGRAPHY OR RANDOM
||| NUMBER DISTRIBUTION MATTERS!
module LCG

import Data.Vect
import Data.SnocList
import public Data.Binary
import public Data.Binary.Digit

%default total

-- Linear Congruential Generator (LCG) parameters
-- Taken from the last row in Table 5 from Steele and Vigna 2021
-- (https://doi.org/10.48550/arXiv.2001.05304)

public export
%inline %tcinline
lcgA : Int
lcgA = 0x93d765dd

public export
%inline %tcinline
lcgC : Int
lcgC = 0

public export
%inline %tcinline
lcgM : Int
lcgM = 4294967296 -- 2 ^ 32

-- Hash function to combine the seed and the path of splits
public export
hash : Int -> List Digit -> Int
hash key path = foldl combine (key * 31) path
  where
    combine : Int -> Digit -> Int
    combine h d = (h * 31) + (case d of
                                   O => 0
                                   I => 1)

-- LCG state
public export
record LCGState where
  constructor MkLCGState
  seed : Int
  path : List Digit

-- Initialize LCG with a seed
public export
initLCG : Int -> LCGState
initLCG seed = MkLCGState seed []

-- Update the path by treating it as a binary counter and incrementing it
public export
updatePath : List Digit -> List Digit
updatePath [] = [I]
updatePath (O :: xs) = I :: xs
updatePath (I :: xs) = O :: updatePath xs

-- Generate the next number in the sequence and update the state
public export
nextLCG : LCGState -> (Int, LCGState)
nextLCG (MkLCGState seed path) =
  let input = hash seed path
      nextSeed = (lcgA * input + lcgC) `mod` lcgM
      nextPath = updatePath path
  in (nextSeed, MkLCGState seed nextPath)

-- Split the generator
public export
splitLCG : LCGState -> (LCGState, LCGState)
splitLCG (MkLCGState seed path) =
  (MkLCGState seed (I :: path), MkLCGState seed (O :: path))

-- Extract the generated number
public export
extractNumber : (Int, LCGState) -> Int
extractNumber (n, _) = n

||| Generate a bounded Int
||| Takes the PRNG state, lower and upper bounds, and returns a random Int
||| within the specified range along with the updated state.
public export
boundedInt :  LCGState
           -> (lower : Int)
           -> (upper : Int)
           -> (Int, LCGState)
boundedInt prng lower upper
    = let (randVal, nextPrng) = nextLCG prng
          rangeSize = upper - lower + 1
      in if rangeSize == 1
            then (lower, nextPrng)
            else (randVal `mod` rangeSize + lower, nextPrng)

||| Generate a bounded Nat
||| Takes the PRNG state, lower and upper bounds, and returns a random Nat
||| within the specified range along with the updated state.
public export
boundedNat :  LCGState
           -> (lower : Nat)
           -> (upper : Nat)
           -> (Nat, LCGState)
boundedNat prng lower upper
  = mapFst cast $ boundedInt prng (cast lower) (cast upper)

||| Generate an arbitrary Double
||| Takes the PRNG state and returns a random Double in the range [0, 1) along
||| with the updated state.
public export
randomDouble : LCGState -> (Double, LCGState)
randomDouble prng =
  let (randInt, nextPrng) = nextLCG prng
      randDouble = cast randInt / cast lcgM
  in (randDouble, nextPrng)

||| Generate a bounded Double
||| Takes the PRNG state, lower and upper bounds, and returns a random Double
||| within the specified range along with the updated state.
public export
boundedDouble :  LCGState
              -> (lower : Double)
              -> (upper : Double)
              -> (Double, LCGState)
boundedDouble prng lower upper =
  let (randDouble, nextPrng) = randomDouble prng
      scaledDouble = lower + randDouble * (upper - lower)
  in (scaledDouble, nextPrng)

||| Generate a List of random values
||| Takes a generator function, the PRNG state, and a length (Nat), and returns
||| a list of random values along with the updated state.
public export
randomList :  (LCGState -> (r, LCGState))
           -> LCGState
           -> Nat
           -> (List r, LCGState)
randomList gen prng n = mapFst toList (randomListHelper gen prng n [<])
  where
    randomListHelper :  (LCGState -> (r, LCGState))
                     -> LCGState
                     -> Nat
                     -> (acc : SnocList r)
                     -> (SnocList r, LCGState)
    randomListHelper _ prng Z acc = (acc, prng)
    randomListHelper gen prng (S k) acc =
      let (val, nextPrng) = gen prng
      in randomListHelper gen nextPrng k (acc :< val)


||| Generate a Vect of random values
||| Takes a generator function, the PRNG state, and a natural number n, and
||| returns a Vect of random values of length n along with the updated state.
public export
randomVect :  (LCGState -> (r, LCGState))
           -> LCGState
           -> (n : Nat)
           -> (Vect n r, LCGState)
randomVect gen prng Z = ([], prng)
randomVect gen prng (S k) =
  let (val, nextPrng) = gen prng
      (rest, finalPrng) = randomVect gen nextPrng k
  in (val :: rest, finalPrng)


-- Example usage
export
example : IO ()
example = do
  let seed = 42
  let prng = initLCG seed
  let (n1, prng1) = nextLCG prng
  let (n2, prng2) = nextLCG prng1
  let (prngLeft, prngRight) = splitLCG prng2
  let (n3, _) = nextLCG prngLeft
  let (n4, _) = nextLCG prngRight
  putStrLn $ "First random number: " ++ show n1
  putStrLn $ "Second random number: " ++ show n2
  putStrLn $ "Random number after splitting left: " ++ show n3
  putStrLn $ "Random number after splitting right: " ++ show n4

