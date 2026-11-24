{- Author:     JRF
   Maintainer: JRF <http://jrf.cocolog-nifty.com/>
   Time-stamp: <2011-01-21T06:50:22Z>
   License:    Public Domain
-}

{- DESCRIPTION

momo.hs - a story of continuation.

An example shows anti-intuitive behavior of callCC with double negative.

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
gigi = callCC (\k -> return (InRight (\x -> k (InLeft x))));

liliana :: (forall r. Cont r Ordinary)
liliana = return SomethingOrdinary

type Service = Prod Ordinary String
type Love = Prod Special String

nino :: (forall a b r. String->(Prod (Service->Cont r a) b)->Cont r a)
nino spice claimant
  = liliana >>= \dish -> ((first claimant) (Prod dish spice))

finish ishappy experience gotten = let {
    dish = first gotten;
    spice = second gotten;
    happiness = if ishappy then "Happy" else "Unhappy";
  } in return (spice ++ experience
               ++ happiness ++ " End. Got "
               ++ (show dish) ++ ".");

resistant proof truth
  = Prod (\claim -> return (Prod proof (second claim))) truth

--beppo :: (forall r. ? -> Cont r String)
beppo = \s -> case s of
  {
    InRight(query) -> let {
       experience = "Search Something...\n";
       } in liliana >>= (\answer -> return (resistant answer experience))
            >>= (nino "Beg to ")
            >>= \(g :: Service) -> finish False experience g;
    InLeft(momo) -> let {
      experience = second momo;
      } in (nino "Order to " momo)
           >>= \(g :: Love) -> finish True experience g;
  }


hora :: (forall r. Cont r Special)
hora = return SomethingSpecial

--kassiopeia :: (forall r. ? -> Cont r String)
kassiopeia = \s -> case s of
  {
    InRight(query) -> let {
       experience = "Search Something...\n";
       } in hora >>= (\answer -> query (resistant answer experience))
            >>= (nino "Beg to ") 
            >>= \(g :: Service) -> finish False experience g;
    InLeft(momo) -> let {
      experience = second momo;
      } in (nino "Order to " momo)
           >>= \(g :: Love) -> finish True experience g;
  }

main = do
  runCont (gigi >>= beppo) putStrLn
  runCont (gigi >>= kassiopeia) putStrLn
