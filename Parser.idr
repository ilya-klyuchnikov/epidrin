module Monadics

import Category
import Funnel
import Functorial
import Monadics
import State
import StateExtra

%default total
%access public export

Parser : (Type -> Type) -> Type -> Type -> Type
Parser m i = StateT m (List i)

--- Some basic combinators

pE : Monad m => Parser m i ()
pE = fun {f = Parser m i} ()

pT : Monad m => (i -> m o) -> Parser m i o
pT g = nu f where
  f : (List i) -> m (o, List i)
  f (i :: is) = do o <- g i; pure (o,is)
  f [] = idris_crash ""

pEmpty : Monad m => Parser m i ()
pEmpty = nu f where
  f : (List i) -> m ((), List i)
  f [] = pure ((),[])
  f _  = idris_crash ""

pI : Monad m => Parser m i i
pI = pT pure

pCon : (Monad m, Eq i) => i -> Parser m i ()
pCon i = pT (ensure . (i ==))

pSeq1 : Monad m =>
        Monoidal (m (List x, List i)) =>
        StateT m (List i) x ->
        StateT m (List i) y ->
        StateT m (List i) (List x)
pSeq1 p sep = fun
              {f = StateT m (List i)}
              {s = x -> (List x) -> (List x)}
              {t = StateT m (List i) x -> StateT m (List i) (List x) -> StateT m (List i) (List x)}
              ((::) {elem = x})
              p
              ((sep <\> (assert_total (pSeq1 p sep))) <++> fun {f = StateT m (List i)} [])

pSeq0 : Monad m =>
        Monoidal (m ((List x), (List i))) =>
        StateT m (List i) x ->
        StateT m (List i) y ->
        StateT m (List i) (List x)
pSeq0 p sep = pSeq1 p sep <++> fun {f = StateT m (List i)} []

pMay : Monad m =>
       Monoidal (m (Maybe x, (List i))) =>
       StateT m (List i) x ->
       StateT m (List i) (Maybe x)
pMay p = fun {f = StateT m (List i)} Just p
         <++>
         fun {f = StateT m (List i)} Nothing

pSkipTo : Monad m =>
          Eq i =>
          (Monoidal (m ()) , Monoidal (m ((), (List i)))) =>
          i -> StateT m (List i) ()
pSkipTo i = pT noti </> (assert_total (pSkipTo i)) <++> pE where
  noti j = if (i == j) then m0 else pure ()

-------- Computing parsers from types

mapParseResult : Monad m => (a -> b) -> m (a, s) -> m (b, s)
mapParseResult f ms = ms >>= (\ (x, y) => pure (f x, y))

-- It is like MonadState from State.idr from std library
interface Monad m => Parse (m : Type -> Type) i x where
  blah : StateT m (List i) x

Monad m => Parse m i () where
  blah = pE

Parse m i x => Parse m i (K x y) where
  blah = ST $ (mapParseResult MkK) . (runStateT blah)

Parse m i x => Parse m i (Id x) where
  blah = ST $ (mapParseResult MkId) . (runStateT blah)

gimme : Parse m i x => List i -> m x
gimme {m} {i} {x} is = do (xv, _) <- un (blah {m = m} {i = i} {x = x}) is; pure xv

commit : a -> List b -> a
commit xv [] = xv
commit xv _  = idris_crash "non-empty rest"

reading : Monad m => StateT m (List i) x -> (List i) -> m x
reading p is = do (xv, rest) <- un p is; pure (commit xv rest)

interface Monad m => ParseFrom (m : Type -> Type) t i x | m, t where
  pF : t -> StateT m (List i) x

-- after adding this definition, checking of Parser.idr is really slow
using (m : Type -> Type)
  (ParseFrom m s i (), Monoidal (m (t, List i))) => ParseFrom m (List (s,t)) i t where
    pF = (<!>) (\ (sv, tv) => eta tv </> pF sv )
