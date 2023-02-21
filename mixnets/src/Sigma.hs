module Sigma where

import Datastruct
import Crypto.Hash
import Enc
import Crypto.PubKey.DSA (PrivateKey)
import Crypto.Number.ModArithmetic (expFast)
import Data.Char
import qualified Data.ByteString.Char8 as BS


{- ∃ x : h = g^x -}
constructZkp :: Prikey -> Integer -> Integer -> Zkp
constructZkp (Prikey g q p x) r c = 
  Zkp (expFast g r p) c (r + c * x)

parseHex :: String -> Integer
parseHex [] = 0 
parseHex (x:xs) = toInteger  (digitToInt  x) + 16 * parseHex xs

fiatShamir :: Prikey -> Integer -> Zkp
fiatShamir sk@(Prikey g q p x) r = 
    constructZkp sk r (parseHex (show $ hashWith SHA256 (BS.pack (show g ++ show q))))


verifyProof :: Pubkey -> Zkp -> Bool 
verifyProof (Pubkey g q p h) (Zkp com chal res) = 
  expFast g res p == mod (com * expFast h chal p) p

  

