{-# LANGUAGE MultiWayIf #-}
module KeyGen where 

import Crypto.Number.Generate
import Crypto.Number.ModArithmetic
import Crypto.Number.Prime
import Datastruct ( Pubkey(..), Prikey(..) ) 


groupGenerator :: Integer -> Integer -> IO Integer
groupGenerator q p = 
  generateBetween 1 (p - 1) >>= \genCand ->
  if | (expSafe genCand q p == 1) && (genCand ^ 2 /= 1) -> return genCand
     | otherwise ->  groupGenerator q p
     

generateKey :: Int -> IO (Prikey, Pubkey)
generateKey bitLength = do
   p <- generateSafePrime bitLength
   let q = div (p - 1) 2
   g <- groupGenerator q p 
   x <- generateMax q
   let y = expSafe g x p
       pk = Pubkey g q p y
       sk = Prikey g q p x
   return (sk, pk)


