{-# LANGUAGE MultiWayIf #-}
module Lib  where

import Crypto.Number.Basic
import Crypto.Number.F2m
import Crypto.Number.Generate
import Crypto.Number.ModArithmetic
import Crypto.Number.Prime
import Data.Maybe
import Crypto.Hash

someFunc :: IO ()
someFunc = putStrLn "someFunc"


{- Generator (g), q (order of subgroup and it's prime), 
   p (prime such that p = 2 * q + 1; however, make it more general) -}

{- q p g y (= g ^ x) -}
data PubKey = PubKey Integer Integer Integer Integer
  deriving (Show, Eq)

{- private key q p g x -}
data PriKey = PriKey Integer Integer Integer Integer
  deriving (Show, Eq)


groupGen :: Integer -> Integer -> IO Integer
groupGen p q = 
  generateBetween 2 (p - 1) >>= \genCand ->
  if | and [expSafe genCand q p == 1, genCand ^ 2 /= 1] -> return genCand
     | otherwise -> groupGen p q

generateKey :: Int -> IO (PubKey, PriKey)
generateKey bitLength = do
   p <- generateSafePrime bitLength
   let q = div (p - 1) 2
   g <- groupGen p q 
   x <- generateMax q
   let y = expSafe g x p
       pk = PubKey q p g y
       sk = PriKey q p g x
   return (pk, sk)

type Rand = Integer
type PText = Integer
type CText = (Integer, Integer)

{- additive elgamal. r should come from Zq -}
encryptValue :: PubKey -> Rand -> PText -> CText
encryptValue (PubKey q p g y) r m = 
   (expSafe g r p, expSafe g m p * expSafe y r p)


reencryptValue :: PubKey -> Rand -> CText -> CText
reencryptValue (PubKey q p g y) r (alpha, beta) = 
  (alpha * expSafe g r p, beta * expSafe y r p)


{- multiply two ciphertext -}
mulencValue :: PubKey -> CText -> CText -> CText
mulencValue (PubKey q p g y) (a, b) (c, d) = 
  (mod (a * c) p, mod (b * d) p)

{- this would the decyption of g^m -}
decryptValue :: PriKey -> CText -> PText
decryptValue (PriKey q p g x) (alpha, beta) = expSafe (beta * inv) 1 p where
  inv = maybe 0 id (inverse (expSafe alpha x p) p)





   
