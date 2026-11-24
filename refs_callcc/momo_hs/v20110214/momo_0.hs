{- Author:     JRF
   Maintainer: JRF <http://jrf.cocolog-nifty.com/>
   Time-stamp: <2011-01-21T06:49:53Z>
   License:    Public Domain
-}

{- DESCRIPTION

momo_0.hs - a story of continuation.

An example shows anti-intuitive behavior of callCC.

-}

{-# LANGUAGE GADTs, RankNTypes, TypeFamilies, ScopedTypeVariables #-}

module Momo where
import System
import Control.Monad.Cont

-- higher order logical definition doesn't work in this context.
--type Absurd = forall a. a
--type Not a = a -> Absurd

-- Explanatory (re)definition:
--  "Sum x y" is the same as "Either a b", and
--  "Prod x y" is the same as Tuple "(a, b)".

data Sum x y = InLeft x | InRight y

data Prod a b = Prod a b
first :: Prod a b -> a
first (Prod x y) = x
second :: Prod a b -> b
second (Prod x y) = y

-- The story begins.

data Special = SomethingSpecial deriving (Eq, Show)
data Ordinary = SomethingOrdinary deriving (Eq, Show)

-- The law of excluded middle.
gigi :: (forall a b r. Cont r (Sum a (a -> Cont r b)))
gigi = callCC(\k -> return (InRight (\x -> k(InLeft(x)))));

liliana :: (forall r. Cont r Ordinary)
liliana = return SomethingOrdinary

nino :: (forall b r. Cont r String)
nino = gigi >>= \s -> case s of
  {
    InRight(query) -> let {
       experience = "Search Something...\n"
       } in liliana >>= (\answer -> return(Prod answer experience))
            >>= \(x :: Prod Ordinary String)
                -> return (experience 
                           ++ "Unhappy End. Got "
                           ++ (show (first x)));
    InLeft(x:: Prod Special String) ->
      return ((second x) ++ "Happy End. Got " ++ (show (first x)));
  }


hora :: (forall r. Cont r Special)
hora = return SomethingSpecial

nicola :: (forall r. Cont r String)
nicola = gigi >>= \s -> case s of
  {
    InRight(query) -> let {
       experience = "Search Something...\n"
       } in hora >>= (\answer -> query(Prod answer experience))
            >>= \(x :: Prod Ordinary String)
                -> return (experience 
                           ++ "Unhappy End. Got "
                           ++ (show (first x)));
    InLeft(x :: Prod Special String) ->
      return ((second x) ++ "Happy End. Got " ++ (show (first x)));
  }

main = do
  runCont nino putStrLn
  runCont nicola putStrLn

