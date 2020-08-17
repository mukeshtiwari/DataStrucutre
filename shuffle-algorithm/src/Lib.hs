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

{-
Haskell translation of 
  https://github.com/benadida/helios-server/blob/0b7da7a902c988de48846897ee9a88ee447e7e78/helios/crypto/elgamal.py 
-}


type PubKey = Integer
type PriKey = Integer
type Gen = Integer
type PText = Integer
type CText = (Integer, Integer)
type Rand = Integer
type Commitment = Integer

groupGenerator :: Integer -> Integer -> IO Integer
groupGenerator p q = 
  generateBetween 2 (p-1) >>= \gen ->
  if | expSafe gen q p == 1 -> return gen
     | otherwise -> groupGenerator p q


generateKey :: Int -> IO (Integer, Integer, Gen, PriKey, PubKey)
generateKey bitLength  = do 
  p <- generateSafePrime bitLength
  let q = div (p - 1) 2
  g <- groupGenerator p q 
  x <- generateBetween 2 q
  return (p, q, g, x, expSafe g x p)
  
{-
*Lib> generateKey 10
(983,491,158,331,905)
-}

p :: Integer
p = 983

q :: Integer
q = 491

g :: Integer
g = 158

h :: Integer
h = 4

prikey :: Integer
prikey = 331

pubkey :: Integer
pubkey = 905


encryptWithR :: Rand -> PText -> CText
encryptWithR r m = (expSafe g r p, mod (m * expSafe pubkey r p) p)

encryptValue :: PText -> IO CText
encryptValue m = do 
  r <- generateBetween 2 q
  return (encryptWithR r m)

reencryptWithR :: Rand -> CText -> CText
reencryptWithR r (a, b) = (mod (a * expSafe g r p) p, mod (b * expSafe pubkey r p) p)

reencryptValue :: CText -> IO CText
reencryptValue ctext = do 
  r <- generateBetween 2 q
  return (reencryptWithR r ctext)

multencValue :: CText -> CText -> CText 
multencValue (a, b) (c, d) = (mod (a * c) p, mod (b * d) p)

decryptValue :: CText -> PText
decryptValue (alpha, beta) = mod (beta * ret) p where
  ret = fromJust . inverse (expSafe alpha prikey p) $ p

pedCommitment :: PText -> Rand -> Commitment
pedCommitment m r = expSafe g m p * expSafe h r p

vectorPedCommitment :: Rand -> [Gen] -> [PText] -> Commitment
vectorPedCommitment r hs ms = 
    expSafe g r p * (product . zipWith (\h m -> expSafe h m p) hs $ ms)

    
