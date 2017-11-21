module Monadics

import Category
import Funnel
import Functorial

%default total
%access public export
-- %auto_implicits off

infixl 9 =<<

(=<<) : Monad m => (s -> m t) -> m s -> m t
(=<<) = flip (>>=)

infixr 6 <.>
(<.>) : Monad m => (b -> m c) -> (a -> m b) -> a -> m c
f <.> g = \a => do b <- g a; f b

Applicative Id where
  pure = MkId
  (MkId f) <*> m  = map f m

Monad Id where
  (MkId s) >>= f = f s

Fun Maybe where
  eta   = pure
  (<$$>) = monadDollar

Monoidal (Maybe x) where
  m0 = Nothing
  Nothing    <++> x = x
  x@(Just _) <++> _ = x

unjust : Maybe x -> x -- very sorry folks
unjust (Just x) = x
unjust Nothing = idris_crash "unjust unjustified"

ensure : Monad m => Bool -> m ()
ensure True  = pure ()
ensure False = idris_crash ""

guard : (Monad m, Monoidal (m s)) => (s -> Bool) -> s -> m s
guard p x = if (p x) then pure x else m0

seek : (Functorial g, Monad m, Monoidal (m s)) => (s -> Bool) -> g s -> m s
seek = (<!>) . guard

prefer : Maybe x -> x -> x
prefer (Just x) _ = x
prefer _        x = x

try : (x -> Maybe x) -> x -> x
try f x = prefer (f x) x

Trans : Type -> Type
Trans x = x -> Maybe x

-- not total
-- TODO - put annotation here
repeatedly : Trans x -> x -> x
repeatedly f = try effing
  where effing = (effing <++> pure) <.> f

repeatUntil : Trans x -> Trans x -> Trans x
repeatUntil step stop = stop <++> (repeatUntil step stop <.> step)
