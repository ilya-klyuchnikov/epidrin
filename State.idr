module State

import Category
import Monadics

%default total
%access public export

record StateT (m : Type -> Type) (stateType : Type) (a : Type) where
  constructor ST
  runStateT : stateType -> m (a, stateType)

Functor f => Functor (StateT f stateType) where
    map f (ST g) = ST (\st => map (mapFst f) (g st)) where
       mapFst : (a -> x) -> (a, s) -> (x, s)
       mapFst fn (a, b) = (fn a, b)

Monad f => Applicative (StateT f stateType) where
    pure x = ST (\st => pure (x, st))

    (ST f) <*> (ST a) = ST (\st => do (g, r) <- f st
                                      (b, t) <- a r
                                      pure (g b, t))

Unpack (StateT m s a) (s -> m (a,s)) where
  un = runStateT
  nu = ST

Monad m => Monad (StateT m stateType) where
    (ST f) >>= k = ST (\st => do (v, st') <- f st
                                 let ST kv = k v
                                 kv st')

get : Monad m => (s -> a) -> StateT m s a
get f = ST $ \ s => pure (f s,s)

set : Monad m => s -> StateT m s ()
set s = ST $ \ _ => pure ((),s)

tweak : Monad m => (s -> s) -> StateT m s ()
tweak f = do s' <- get f; set s'

doo : Monad m => m a -> StateT m s a
doo ma = ST $ \ s => do a <- ma ; pure (a,s)

effect : Monad m => s -> StateT m s () -> m s
effect start prog =
  do (_, s) <- un prog start
     pure s

tryThis : s -> StateT Maybe s () -> s
tryThis start prog = flip prefer start $
  do (_, s) <- un prog start
     pure $ s

result : Monad m => s -> StateT m s x -> m x
result start prog =
  do (x, _) <- un prog start
     pure x

locally : Monad m => StateT m s x -> StateT m s x
locally this =
  do s <- get id
     x <- this
     set s
     pure x

Monad m => Fun (StateT m s) where
  eta = pure
  (<$$>) = monadDollar

using (m : Type -> Type)
  (Monoidal (m (x,s)), Monad m) => Monoidal (StateT m s x) where
    m0 = ST $ m0
    tx <++> ty = ST $ runStateT tx <++> runStateT ty
