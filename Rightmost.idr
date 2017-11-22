module Rightmost

import Category
import Funnel
import Functorial

%default total
%access public export

data Rightmost x = MkRightmost x | Missing

Functor Rightmost  where
  map _ Missing       = Missing
  map f (MkRightmost a) = MkRightmost (f a)

Applicative Rightmost where
  pure = MkRightmost
  (MkRightmost f)  <*> m  = map f m
  Missing <*> _m      = Missing

Monad Rightmost where
  (MkRightmost x) >>= f = f x
  Missing >>= f     = Missing

Monoidal (Rightmost x) where
  m0 = Missing
  x <++> Missing         = x
  _ <++> x@(MkRightmost _) = x

Fun f => Funnel f (Rightmost x) (f (Rightmost x)) where
  fun    = eta
  funnel = id

Fun f => Funnel f (x -> Rightmost x) (f x -> f (Rightmost x)) where
    funnel fg fx = funnel (fg <$$> fx)
    fun g = funnel {f = f} {s = s} (eta g) where
      s : Type
      s = x -> Rightmost x

Functorial Rightmost where
  (<^>) {f} g Missing         = fun {f = f} Missing
  (<^>) {f} g (MkRightmost x) = fun {f = f} MkRightmost (g x)

Fun Rightmost where
  eta    = pure
  (<$$>) = monadDollar

replacement : x -> Rightmost x -> x
replacement x Missing = x
replacement _ (MkRightmost x) = x
