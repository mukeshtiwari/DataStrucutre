module Datastruct where 
import Crypto.Cipher.Types (Cipher)


{- g q p y : -}
data Pubkey = Pubkey Integer Integer Integer Integer deriving Show

{- g q p x -}
data Prikey = Prikey Integer Integer Integer Integer deriving Show


data Cipher = Cipher Integer Integer deriving Show

data Zkp = Zkp Integer Integer Integer deriving Show