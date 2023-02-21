module Enc where
import Datastruct
import Crypto.Number.ModArithmetic ( expFast, expSafe, inverse )

sk :: Prikey
sk = Prikey 133 419 839 124

pk :: Pubkey 
pk = Pubkey 133 419 839 125


{- m has to be a Group element -}
encMsg :: Pubkey -> Integer -> Integer -> Cipher 
encMsg (Pubkey g q p h) m r = Cipher (expFast g r p) (m * expFast h r p)
    

decCipher :: Prikey -> Cipher -> Integer
decCipher (Prikey g q p x) (Cipher alpha beta) = expSafe (beta * inv) 1 p where
   inv = maybe 0 id (inverse (expSafe alpha x p) p) 
