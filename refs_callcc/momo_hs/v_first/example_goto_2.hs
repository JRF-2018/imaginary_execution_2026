{- Author:     JRF
   Maintainer: JRF <http://jrf.cocolog-nifty.com/>
   Time-stamp: <2011-01-19T08:08:39Z>
   License:    Public Domain
-}

{- DESCRIPTION

example_goto_2.hs - an example of continuation.

An example shows anti-intuitive behavior of callCC using "goto".

Th code reduces a big loop to a small loop.

-}

module Main where
import System
import Control.Monad.Cont

data While a b c = LoopEnd a b
                 | LoopStart a b ((While a b c)->c)
                 | Label1 a b ((While a b c)->c)
                 | Label2 a b ((While a b c)->c)

data BigWhile a b c = BLoopEnd a b
                    | BLoopStart a b ((Either (While a b c) 
                                               (BigWhile a b c))->c)
                    | BLabel1 a b ((Either (While a b c) 
                                            (BigWhile a b c))->c)
                    | BLabel2 a b ((Either (While a b c) 
                                            (BigWhile a b c))->c)

looper input output
  = (callCC $ \goto ->return (Right (BLoopStart input output goto)));

testloop input = (looper input "") >>= \z -> case z of
  {
    Left z -> case z of
       {
         LoopEnd input output -> case input of
            {
              [] -> return (output ++ " rlend ");
              c : r -> return (output ++ c ++ " rlastnext ");
              };
         LoopStart input output goto -> case input of
           {
             [] -> goto (LoopEnd [] (output ++ " rlse "));
             c : r -> goto (Label1 r (output ++ " rlsn " ++ c) goto);
             };
         Label1 input output goto -> case input of
           {
             [] -> goto (LoopEnd [] (output ++ " rl1e "));
             c : r -> goto (Label2 r (output ++ " rl1n " ++ c) goto);
             };
         Label2 input output goto -> case input of
           {
             [] -> goto (LoopEnd [] (output ++ " rl2e "));
             c : r -> goto (LoopStart r (output ++ " rl2n " ++ c) goto);
             };
         };
    
    Right z -> case z of
      {
        BLoopEnd input output -> case input of
           {
             [] -> return (output ++ " llend ");
             c : r -> return (output ++ c ++ " llastnext ");
             };
        BLoopStart input output goto -> case input of
          {
            [] -> goto (Right (BLoopEnd [] (output ++ " llse ")));
            c : r -> goto (Right (BLabel1 r (output ++ " llsn " ++ c) goto));
            };
        BLabel1 input output goto -> case input of
          {
            [] -> goto (Right (BLoopEnd [] (output ++ " ll1e ")));
            c : r -> goto (Right (BLabel2 r (output ++ " ll1n " ++ c) goto));
            };
        BLabel2 input output goto -> case input of
          {
            [] -> goto (Right (BLoopEnd [] (output ++ " ll2e ")));
            c : r -> goto (Left (LoopStart r (output ++ " ll2n " ++ c)
                                 (\y -> goto (Left y))));
            };
        };
    }

main = do runCont (testloop ["a", "b", "c", "d", "e"]) putStrLn
