module Monadics

import Category
import Funnel
import Functorial
import Monadics
import State
import StateExtra
import Utils

--%default total
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

eol1 : Parser Maybe Char ()
eol1 = fun {f = StateT Maybe (List Char)} () </> (pCon '\n' </> pMay (pCon '\r') <++> pCon '\r' </> pMay (pCon '\n'))

------------------------
-- For some strange reason, if those defs are put into a separate file,
-- they don't work (some instances of interfaces are not found).

data Bracket = ROUND | SQUARE

Fun f => Funnel f Bracket (f Bracket) where
  fun    = eta
  funnel = id

data Sep
  = OpenSep Bracket
  | CloseSep Bracket
  | Tab
  | EoL

Fun f => Funnel f Sep (f Sep) where
  fun    = eta
  funnel = id

Fun f => Funnel f (Bracket -> Sep) (f Bracket -> f Sep) where
    funnel fg fx = funnel (fg <$$> fx)
    fun g = funnel {f = f} {s = s} (eta g) where
      s : Type
      s = Bracket -> Sep

Show Sep where
  show (OpenSep  ROUND)  = "("
  show (CloseSep ROUND)  = ")"
  show (OpenSep  SQUARE) = "["
  show (CloseSep SQUARE) = "]"
  show Tab            = "!"
  show EoL            = "\n"

eol : Parser Maybe Char ()
eol = eol1

Parse Maybe Char Sep where
  blah = p1 <++> p2 <++> p3 <++> p4 where
          p01 : StateT Maybe (List Char) Bracket
          p01 = fun {f = StateT Maybe (List Char)} ROUND </> pCon '('
          p02 : StateT Maybe (List Char) Bracket
          p02 = fun {f = StateT Maybe (List Char)} SQUARE </> pCon '['
          p0  : StateT Maybe (List Char) Bracket
          p0  = (p01 <++> p02)
          p1  : StateT Maybe (List Char) Sep
          p1  = fun {f = StateT Maybe (List Char)} OpenSep p0
          p21 : StateT Maybe (List Char) Bracket
          p21 = fun {f = StateT Maybe (List Char)} ROUND </> pCon ')'
          p22 : StateT Maybe (List Char) Bracket
          p22 = fun {f = StateT Maybe (List Char)} SQUARE </> pCon ']'
          p2  : StateT Maybe (List Char) Sep
          p2  = fun {f = StateT Maybe (List Char)} CloseSep (p21 <++> p22)
          p3  : StateT Maybe (List Char) Sep
          p3  = fun {f = StateT Maybe (List Char)} Tab </> pCon '!'
          p4  : StateT Maybe (List Char) Sep
          p4  = fun {f = StateT Maybe (List Char)} EoL </> eol

Body : Type
Body = Either Nat String

nSpaces : Nat -> List Char
nSpaces i = take i spaces

bcons : Char -> Body -> Body
bcons ' ' (Left i)   = Left (i + 1)
bcons  c  (Left i)   = Right (cast cs') where
  cs' : List Char
  cs' = c :: (nSpaces i)
bcons  c  (Right cs) = Right (cast cs') where
  cs' : List Char
  cs' = c :: (cast cs)

-- questionable
Fun f => Funnel f ((Body, b) -> (Body, b)) (f (Body, b) -> f (Body, b)) where
  funnel fg fx = funnel (fg <$$> fx)
  fun g = funnel {f = f} {s = s} (eta g) where
    s : Type
    s = (Body, b) -> (Body, b)

Fun f => Funnel f (Char -> (Body, b) -> (Body, b)) (f Char -> f (Body, b) -> f (Body, b)) where
  funnel fg fx = funnel (fg <$$> fx)
  fun g = funnel {f = f} {s = s} (eta g) where
    s : Type
    s = Char -> (Body, b) -> (Body, b)

mkPair : x -> y -> (x,y)
mkPair x' y' = (x', y')

-- TODO - totality
Parse Maybe Char (Body, Sep) where
  blah = p1 <++> p2 where
       b : StateT Maybe (List Char) Sep
       b = blah
       a : z -> (Body, z)
       a x = ((Left 0), x)
       f1 : (Sep -> (Body, Sep)) -> StateT Maybe (List Char) Sep -> StateT Maybe (List Char) (Body, Sep)
       f1 = fun {f = StateT Maybe (List Char)}
       p1 : StateT Maybe (List Char) (Body, Sep)
       p1 = f1 a b
       f2 : (Char -> (Body, Sep) -> (Body, Sep)) -> (StateT Maybe (List Char) Char -> StateT Maybe (List Char) (Body, Sep) -> StateT Maybe (List Char) (Body, Sep))
       f2 = fun {f = StateT Maybe (List Char)}
       p2 : StateT Maybe (List Char) (Body, Sep)
       p2 = f2 f' pI blah where
         f' : Char -> (Body, Sep) -> (Body, Sep)
         f' c (b, s) = (bcons c b,s)

chunk : String -> Maybe (List (Body,Sep))
chunk = reading (psq b p) . (cast {from = String} {to = List Char})  where
  p : StateT Maybe (List Char) ()
  p = pE
  b : StateT Maybe (List Char) (Body, Sep)
  b = blah
  psq : StateT Maybe (List Char) (Body, Sep) -> StateT Maybe (List Char) () -> StateT Maybe (List Char) (List (Body, Sep))
  psq = pSeq0
