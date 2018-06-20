{-# LANGUAGE MultiWayIf #-}
module Lib where

import Crypto.Number.Basic
import Crypto.Number.F2m
import Crypto.Number.Generate
import Crypto.Number.ModArithmetic
import Crypto.Number.Prime
import Data.Maybe
import Crypto.Hash
import qualified Data.ByteString.Char8 as BS
import Data.Char

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

parseHex :: String -> Integer
parseHex = parse . reverse where
   parse :: String -> Integer
   parse []     = 0
   parse (x:xs) = toInteger  (digitToInt  x) + 16 * parse xs

-- https://github.com/benadida/helios-server/blob/master/helios/crypto/algs.py#L340
proveDecryption :: PublicKey -> PrivateKey -> (Integer, Integer) -> IO [Integer]
proveDecryption pk@(PublicKey q p g y)  sk@(PrivateKey x) (alpha, beta) = do 
  let m = decryptValue sk pk (alpha, beta)
      beta_over_m = mod (beta * (maybe 0 id (inverse m p))) p
  w <- generateMax q
  let a = expSafe g w p
      b = expSafe alpha w p
      c = parseHex . show $ (hash . BS.pack $ show a ++ show b :: Digest SHA1)
      t = mod (w + x * c) q
  return  [a, b, c, t]
 
   
verifyDecryption :: PublicKey -> Integer -> (Integer, Integer) -> [Integer] -> Bool
verifyDecryption (PublicKey q p g y) m (alpha, beta) [a, b, c, t] = 
  and [expSafe g t p == mod (a * expSafe y c p) p, expSafe alpha t p == mod (b * expSafe (mod (beta * (maybe 0 id (inverse m p))) p) c p) p]






