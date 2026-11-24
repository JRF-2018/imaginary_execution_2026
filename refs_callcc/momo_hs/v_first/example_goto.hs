{- Author:     JRF
   Maintainer: JRF <http://jrf.cocolog-nifty.com/>
   Time-stamp: <2011-01-17T07:04:19Z>
   License:    Public Domain
-}

{- DESCRIPTION

example_goto.hs - an example of continuation.

An example shows anti-intuitive behavior of callCC using "goto".

-}

module Main where
import System
import Control.Monad.Cont

data While a b c = LoopEnd a b
                 | LoopStart a b ((While a b c)->c)
                 | Label1 a b ((While a b c)->c)
                 | Label2 a b ((While a b c)->c)

looper input output
  = (callCC $ \goto ->return (LoopStart input output goto));

testloop input = (looper input "") >>= \z -> case z of
  {
    LoopEnd input output -> case input of
       {
         [] -> return (output ++ " lend ");
         c : r -> return (output ++ c ++ " lastnext ");
       };
    LoopStart input output goto -> case input of
      {
        [] -> goto (LoopEnd [] (output ++ " lse "));
        c : r -> goto (Label1 r (output ++ " lsn " ++ c) goto);
      };
    Label1 input output goto -> case input of
      {
        [] -> goto (LoopEnd [] (output ++ " l1e "));
        c : r -> goto (Label2 r (output ++ " l1n " ++ c) goto);
      };
    Label2 input output goto -> case input of
      {
        [] -> goto (LoopEnd [] (output ++ " l2e "));
        c : r -> goto (LoopStart r (output ++ " l2n " ++ c) goto);
      };
  }

main = do runCont (testloop ["a", "b", "c", "d"]) putStrLn
