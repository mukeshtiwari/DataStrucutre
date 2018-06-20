{-# LANGUAGE MultiWayIf #-}
module Lib where

import Crypto.Number.Basic
import Crypto.Number.F2m
import Crypto.Number.Generate
import Crypto.Number.ModArithmetic
import Crypto.Number.Prime
import Data.Maybe

 
{- In Coq, You need (g (generator), q (order of subgroup and it is prime), p (prime such that p = 2 * q + 1), publickey and private key -}
{- p, q , g, y -}
data PublicKey = PublicKey Integer Integer Integer Integer deriving Show
{- x => y = g^x mod p -}
data PrivateKey = PrivateKey Integer deriving Show


groupGenerator :: Integer -> Integer -> IO Integer
groupGenerator p q = 
  generateBetween 1 (p - 1) >>= \genCand ->
  if | and [expSafe genCand q p == 1, genCand ^ 2 /= 1] -> return genCand
     | otherwise ->  groupGenerator p q 
     

generateKey :: Int -> IO (PublicKey, PrivateKey)
generateKey bitLength = do
   p <- generateSafePrime bitLength
   let q = div (p - 1) 2
   g <- groupGenerator p q 
   x <- generateMax q
   let y = expSafe g x p
       pk = PublicKey q p g y
       sk = PrivateKey x
   return (pk, sk)


encryptValue :: PublicKey -> Integer -> IO (Integer, Integer) 
encryptValue (PublicKey q p g y) t = 
  generateMax q >>= \r ->
  return (expSafe g r p, t * expSafe y r p)


reencryptValue :: PublicKey -> (Integer, Integer) -> IO (Integer, Integer)
reencryptValue (PublicKey q p g y) (c, d) = 
  generateMax q >>= \r ->
  return (c * expSafe g r p, d * expSafe y r p)

decryptValue :: PrivateKey -> PublicKey -> (Integer, Integer) -> Integer
decryptValue (PrivateKey x) (PublicKey q p g y) (c, d) = expSafe (d * inv) 1 p where
   inv = maybe 0 id (inverse (expSafe c x p) p) 



