{- Author:     JRF
   Maintainer: JRF <http://jrf.cocolog-nifty.com/>
   Time-stamp: <2011-02-14T07:12:02Z>
   License:    Public Domain
-}

{- DESCRIPTION

example_goto_4.hs - an example of continuation.

This example is a more sophisticated version of "example_goto_3.hs"
which expresses uselessness of function-value of "goto" with a type variable.

-}

module Main where
-- import System  (GHC 7.2+ では haskell98 の System が既定で使えないので外した)
import Control.Monad.Cont

data While a b m c d = LoopEnd a b
                       ((While a b m c d)->m (c, a -> b -> (c -> m d) -> m d))
                     | LoopStart a b
                       ((While a b m c d)->m (c, a -> b -> (c -> m d) -> m d))
                     | LoopMain a b
                       ((While a b m c d)->m (c, a -> b -> (c -> m d) -> m d))
                     | Method1 a b (c -> m d)
                       ((While a b m c d)->m (c, a -> b -> (c -> m d) -> m d))
                     | Receive1 a b
                       ((While a b m c d)->m (c, a -> b -> (c -> m d) -> m d))
                     | Dummy


looper input output
  = (callCC $ \goto ->return (LoopStart input output goto));

runserver input = (looper input "") >>= \z -> case z of
  {
    LoopEnd input output goto -> case input of
       {
         [] -> return (Left (output ++ " slend "), 
                       (\x y r -> (goto (Method1 x y r goto)) 
                                  >>= \(Right u, v) -> return u));  -- absurd
         c : r -> return (Left (output ++ c ++ " slastnext "),
                       (\x y r -> (goto (Method1 x y r goto)) 
                                  >>= \(Right u, v) -> return u));  -- absurd
       };
    LoopStart input output goto -> case input of
      {
        [] -> goto (LoopEnd [] (output ++ " slse ") goto);
        c : r -> goto (LoopStart r (output ++ " slsn " ++ c) goto);
      };
    
    {- receive request form client. -}
    Method1 input output ret goto -> case input of
      {
        [] -> goto (LoopEnd [] (output ++ " sm1e ") goto);
        c : r -> (if (c == "stop") then
                    {- Yes, it can go out, but where to go? -}
                   (goto (LoopEnd r (output ++  " sm11e " ++ c) goto))
                 else
                    {- send result to client. -}
                    (ret (Left (output ++ " sm1n " ++ c))) >>= (\y -> goto Dummy));
      };
  }

{- server...or, daemon -}
server = runserver [];

runclient input = (looper input "") >>= \z -> case z of
  {
    LoopEnd input output goto -> case input of
       {
         [] -> return (Left (output ++ " clend "), 
                       (\x y r -> (goto (Method1 x y r goto)) 
                                  >>= \(Right u, v) -> return u)); -- absurd
         c : r -> return (Left (output ++ c ++ " clastnext "),
                       (\x y r -> (goto (Method1 x y r goto)) 
                                  >>= \(Right u, v) -> return u)); -- absurd
       };
    LoopStart input output goto -> 
      {- save output from server. -}
      server >>= (\(Left sout, service)
                  -> goto (LoopMain input (sout ++ output) goto));
    LoopMain input output goto -> case input of
      {
        [] -> goto (LoopEnd [] (output ++ " clme ") goto);
        {- send [c] to server. -}
        c : r -> server >>= (\(sout, service)
                             -> (service [c] (output ++ " clmn " ++ c)
                                 (\(Left y) -> ((goto (Receive1 r y goto))
                                         >>= \(Right u, v) -> return u)))) -- absurd
                 >>= (\y -> goto Dummy);
      };
    
    {- receive response form server. -}
    Receive1 input output goto -> case input of
      {
        [] -> goto (LoopEnd [] (output ++ " cr1e ") goto);
        c : r -> goto (LoopMain r (output ++ " cr1n " ++ c) goto);
      };
  }

main = do runCont ((runclient ["a", "b", "stop", "d", "e"])
                   >>= \(Left u, v) -> return u) putStrLn

{- The code blow fails into infinite loop. -}
-- main = do runCont ((server >>= (\(c, v) ->
--                                if (c == " slse  slend ") then
--                                  (runclient ["a", "b", "stop", "c"])
--                                else
--                                  (runclient ["d", "e", "f"])))
--                    >>= \(Left u, v) -> return u) putStrLn

