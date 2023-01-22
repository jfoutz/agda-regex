module explore where

open import Agda.Builtin.Char using (Char)
open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤)


postulate putStr : String -> IO ⊤
{-# FOREIGN GHC import qualified Data.Text as T #-}
{-# COMPILE GHC putStr = putStr . T.unpack #-}


postulate getChar : IO Char
{-# FOREIGN GHC import System.IO as S #-}
{-# COMPILE GHC getChar = S.getChar #-}


postulate bindIO    : {A B : Set} -> IO A -> (A -> IO B) -> IO B
{-# COMPILE GHC bindIO = \_ _ -> (>>=) :: IO a -> (a -> IO b) -> IO b #-}

{-
  ok, so that works, cool
  per character requires setting
  buffering onstdin to NoBuffering, which is probably
  too much, but agda --compile explore.agda
  builds and exe and talks and stuff
  see https://github.com/agda/agda/blob/master/examples/simple-lib/Lib/IO.agda
-}

rep : Nat -> String
rep Nat.zero = "\n"
rep (Nat.suc c) = Agda.Builtin.String.primStringAppend "+" (rep c)

mychar = 'a'

main : IO ⊤
main = bindIO getChar (\ c -> bindIO (putStr (rep 2))  (\ _ -> (putStr (rep 3))))

