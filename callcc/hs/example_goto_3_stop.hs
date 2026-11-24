{- Author:     JRF
   Maintainer: JRF <http://jrf.cocolog-nifty.com/>
   Time-stamp: <2011-01-23T07:58:06Z>
   License:    Public Domain
-}

{- DESCRIPTION

example_goto_3.hs - an example of continuation.

An example shows awkward behavior of callCC using "goto".

The idea was to return "goto" with output, but it couldn't under the
rigid type system.  This code satisfies my intention compromising with it.

-}

module Main where
-- import System  (GHC 7.2+ では haskell98 の System が既定で使えないので外した)
import Control.Monad.Cont

data While a b m c d = LoopEnd a b
                       ((While a b m c d)->m (c, a -> b -> (d -> m d) -> m c))
                     | LoopStart a b
                       ((While a b m c d)->m (c, a -> b -> (d -> m d) -> m c))
                     | LoopMain a b
                       ((While a b m c d)->m (c, a -> b -> (d -> m d) -> m c))
                     | Method1 a b (d -> m d)
                       ((While a b m c d)->m (c, a -> b -> (d -> m d) -> m c))
                     | Receive1 a b
                       ((While a b m c d)->m (c, a -> b -> (d -> m d) -> m c))
                     | Dummy


looper input output
  = (callCC $ \goto ->return (LoopStart input output goto));

runserver input = (looper input "") >>= \z -> case z of
  {
    LoopEnd input output goto -> case input of
       {
         [] -> return (output ++ " slend ", 
                       (\x y r -> (goto (Method1 x y r goto)) 
                                  >>= \(u, v) -> return u));
         c : r -> return (output ++ c ++ " slastnext ",
                       (\x y r -> (goto (Method1 x y r goto)) 
                                  >>= \(u, v) -> return u));
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
                    (ret (output ++ " sm1n " ++ c)) >>= (\y -> goto Dummy));
      };
  }

{- server...or, daemon -}
server = runserver [];

runclient input = (looper input "") >>= \z -> case z of
  {
    LoopEnd input output goto -> case input of
       {
         [] -> return (output ++ " clend ", 
                       (\x y r -> (goto (Method1 x y r goto)) 
                                  >>= \(u, v) -> return u));
         c : r -> return (output ++ c ++ " clastnext ",
                       (\x y r -> (goto (Method1 x y r goto)) 
                                  >>= \(u, v) -> return u));
       };
    LoopStart input output goto -> 
      {- save output from server. -}
      server >>= (\(sout, service)
                  -> goto (LoopMain input (sout ++ output) goto));
    LoopMain input output goto -> case input of
      {
        [] -> goto (LoopEnd [] (output ++ " clme ") goto);
        {- send [c] to server. -}
        c : r -> server >>= (\(sout, service)
                             -> (service [c] (output ++ " clmn " ++ c)
                                 (\y -> ((goto (Receive1 r y goto))
                                         >>= \(u, v) -> return u))))
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
                   >>= \(u, v) -> return u) putStrLn

{- The code blow fails into infinite loop. -}
-- main = do runCont ((server >>= (\(c, v) ->
--                                if (c == " slse  slend ") then
--                                  (runclient ["a", "b", "stop", "c"])
--                                else
--                                  (runclient ["d", "e", "f"])))
--                    >>= \(u, v) -> return u) putStrLn

