module Zip

import Category
import Funnel
import Functorial
import Rightmost
import Monadics


-- %default total
%access public export

--- Zip ---

infixl 6 :<:
data Zip s = MkZip | (:<:) (Zip s) s --deriving Eq

Eq s => Eq (Zip s) where
  MkZip == MkZip = True
  (x1 :<: y1) == (x2 :<: y2) = x1 == x2 && y1 == y2
  _ == _ = False

Show x => Show (Zip x) where
  show MkZip = ""
  show (xz :<: x) = show xz ++ "< " ++ show x ++ "\n"

Fun f => Funnel f (Zip s) (f (Zip s)) where
  fun    = eta
  funnel = id

Fun f => Funnel f (x -> Zip x) (f x -> f (Zip x)) where
  funnel fg fx = funnel (fg <$$> fx)
  fun g = funnel {f = f} {s = s} (eta g) where
    s : Type
    s = x -> Zip x

Fun f => Funnel f (Zip x -> x -> Zip x) (f (Zip x) -> f x -> f (Zip x)) where
  funnel fg fx = funnel (fg <$$> fx)
  fun g = funnel {f = f} {s = s} (eta g) where
    s : Type
    s = Zip x -> x -> Zip x

Functor Zip where
  map g  MkZip       = MkZip
  map g (xz :<: x)   = (:<:) (map g xz) (g x)

Monoidal (Zip s) where
  m0 = MkZip
  xz <++>     MkZip  = xz
  xz <++> (yz :<: y) = (xz <++> yz) :<: y

Functorial Zip where
  (<^>) {f} g MkZip      = fun {f = f} MkZip
  (<^>) {f} g (xz :<: x) = fun {f = f} (:<:) (g <^> xz) (g x)

zOne : x -> Zip x
zOne = (MkZip :<:)

zPost : (b -> a -> b) -> b -> Zip a -> b
zPost app t MkZip = t
zPost app f (sz :<: s) = app (zPost app f sz) s

zCache : Zip s -> (Zip (Zip s, s))
zCache MkZip = MkZip
zCache (xz :<: x) = zCache xz :<: (xz,x)

zosh : Show x => String -> Zip x -> String
zosh cap MkZip = ""
zosh cap xz = concat (the (List String) [cap, "[\n", show xz, "]", cap, "\n"])

zlen : Zip x -> Int
zlen MkZip = 0
zlen (z :<: _) = 1 + zlen z

--- Tip, UTip ---

infixr 6 :>:
data Tip t s = MkTip t | (:>:) s (Tip t s) -- deriving Eq

Show s => Show (Tip t s) where
  show (MkTip _) = ""
  show (x :>: xs) = "> " ++ show x ++ "\n" ++ show xs

(Eq t, Eq s) => Eq (Tip t s) where
  (MkTip t1) == (MkTip t2) = t1 == t2
  (t1 :>: ts1) == (t2 :>: ts2) = (t1 == t2) && (ts1 == ts2)
  tip1 == tip2 = False

Fun f => Funnel f (Tip t s) (f (Tip t s)) where
  fun    = eta
  funnel = id

Fun f => Funnel f ((Tip t' s') -> (Tip t' s')) (f (Tip t' s') -> f (Tip t' s')) where
  funnel fg fx = funnel (fg <$$> fx)
  fun g = funnel {f = f} {s = s} (eta g) where
    s : Type
    s = Tip t' s' -> Tip t' s'

Fun f => Funnel f (s' -> (Tip t' s') -> (Tip t' s')) (f s' -> f (Tip t' s') -> f (Tip t' s')) where
  funnel fg fx = funnel (fg <$$> fx)
  fun g = funnel {f = f} {s = s} (eta g) where
    s : Type
    s = s' -> Tip t' s' -> Tip t' s'

Functor (Tip t) where
  map g (x :>: xs) = (:>:) (g x) (map g xs)
  map g (MkTip t')      = MkTip t'

Functorial (Tip t) where
  (<^>) {f} g (x :>: xs) = fun {f = f} (:>:) (g x) (g <^> xs)
  (<^>) {f} g (MkTip t)  = fun {f = f} (MkTip t)

infixr 6 >>>
(>>>) : Tip lost s -> Tip t s -> Tip t s
(x :>: xs) >>> ys = x :>: xs >>> ys
_          >>> ys = ys

UTip : Type -> Type
UTip = Tip ()

nil : UTip tp
nil = MkTip ()

Monoidal (UTip s) where
  m0 = nil
  (<++>) = (>>>)

Unpack (UTip x) (List x) where
  un = (<!>) (:: [])
  nu = (<!>) (:>: nil)

losh : Show x => String -> UTip x -> String
losh cap (MkTip _) = ""
losh cap xs = concat [cap, "[\n", show xs, "]", cap, "\n"]

-- Shuffling --

infixr 6 <>>

(<>>) : Zip x -> Tip t x -> Tip t x
MkZip <>> xs = xs
(xz :<: x) <>> xs = xz <>> (x :>: xs)

infixl 6 <><.

(<><.) : Zip x -> Tip t x -> (Zip x,t)
xz <><. (MkTip t) = (xz, t)
xz <><. (x :>: xs) = xz :<: x <><. xs

infixl 6 <><

(<><) : Zip x -> Tip a x -> Zip x
xz <>< xs = fst (xz <><. xs)

zippy : (List x) -> Zip x
zippy = zz (MkZip {s = x}) where
  zz : Zip x -> List x -> Zip x
  zz xz [] = xz
  zz xz (x :: xs) = zz (xz :<: x) xs

yppiz : Zip x -> List x
yppiz xz = yy xz [] where
  yy : Zip x -> List x -> List x
  yy MkZip xs = xs
  yy (xz :<: x) xs = yy xz (x :: xs)

-- Unsafe stack operations --
zTop : Zip s -> s
zTop (_ :<: s) = s

zPop : Int -> Zip s -> Zip s
zPop 0     zz     = zz
zPop n (zz :<: _) = zPop (n - 1) zz

zCrop : Int -> Zip s -> Zip s
zCrop 0     zz     = MkZip
zCrop n (zz :<: z) = zCrop (n - 1) zz :<: z

tTop : Tip t s -> s
tTop (s :>: _) = s

tPop : Int -> Tip t s -> Tip t s
tPop 0     ss     = ss
tPop n (_ :>: ss) = tPop (n - 1) ss

lCrop : Int -> UTip s -> UTip s
lCrop 0     ss        = nil
lCrop n (s :>: ss) = s :>: lCrop (n - 1) ss

-- Search in a list --

index : Eq x => Tip t (x, z) -> x -> Maybe (Int, z)
index ((x', z') :>: xs) y = if (x' == y) then Just (0, z') else m' (index xs y) where
  m' : (Maybe (Int, z)) -> (Maybe (Int, z))
  m' (Just (i, z')) = Just (i + 1, z')
  m' _ = Nothing
index _ _ = Nothing

-- Fun instances --

-- they are infinite - TODO - handle it later!
Fun Zip where
  (fz :<: f) <$$> (sz :<: s) = fz <$$> sz :<: f s
  _          <$$> _          = MkZip
  eta x = (eta x) :<: x

Fun UTip where
  (f :>: fs) <$$> (s :>: ss) = f s :>: fs <$$> ss
  _          <$$> _          = nil
  eta x = x :>: eta x

-- Lookup operations --

infixr 4 :=:
infixr 4 :==:
data (:==:) x t = (:=:) x t

key : (x :==: t) -> x
key (x :=: _) = x

Fun f => Funnel f (x :==: t) (f (x :==: t)) where
  fun    = eta
  funnel = id

Fun f => Funnel f (t' -> x :==: t') (f t' -> f (x :==: t')) where
  funnel fg fx = funnel (fg <$$> fx)
  fun g = funnel {f = f} {s = s} (eta g) where
    s : Type
    s = t' -> x :==: t'

Fun f => Funnel f (x -> t' -> x :==: t') (f x -> f t' -> f (x :==: t')) where
  funnel fg fx = funnel (fg <$$> fx)
  fun g = funnel {f = f} {s = s} (eta g) where
    s : Type
    s = x -> t' -> x :==: t'

Functorial ((:==:) x) where
  (<^>) {f} g (x' :=: t) = fun {f = f} ((:=:) x') (g t)

-- This is very interesting!
Eq x => Eq (x :==: t) where
  (x' :=: _) == (y :=: _) = x' == y


isIt : (Fun f, Monoidal (f t), Eq x) => x -> (x :==: t) -> f t
isIt x1 (x2 :=: t') = Category.when (x1 == x2) (eta t')
-- Idris halts without explitic Category.when

zAssoc : Eq p => Zip (p :==: t) -> p -> Rightmost t
zAssoc ptz p = isIt p <!> ptz

-- Prefix comparability --

commonPrefix : Eq x => Tip t x -> Tip t x -> (Zip x,Tip t x,Tip t x)
commonPrefix t1 t2 = cp (MkZip {s=x}) t1 t2 where
  cp : Zip x -> Tip t x -> Tip t x -> (Zip x, Tip t x, Tip t x)
  cp xz (x1 :>: t1) (x2 :>: t2) = if x1 == x2 then cp (xz :<: x1) t1 t2 else (xz,t1,t2)
  cp xz t1 t2 = (xz,t1,t2)

Eq x => Ord (UTip x) where
  compare l1 l2 = f (commonPrefix l1 l2) where
    f (_,MkTip _,MkTip _) = EQ
    f (_,MkTip _,_)     = LT
    f _               = GT

-- Cursors --
Cursor : Type -> Type
Cursor = Cross Zip UTip

cur0 : Cursor x
cur0 = MkZip :*: nil

curUp : Trans (Cursor x)
curUp (xz :<: y :*: zs) = eta (xz :*: y :>: zs)
curUp _ = m0

curDown : Trans (Cursor x)
curDown (xz :*: y :>: zs) = eta (xz :<: y :*: zs)
curDown _ = m0

curList : Cursor x -> UTip x
curList (xz :*: xs) = xz <>> xs

curIns : x -> Cursor x -> Cursor x
curIns x (xz :*: es) = xz :<: x :*: es

Unpack (Cursor x) (List x) where
  un (xz :*: xs) = un (xz <>> xs)
  nu xs          = (MkZip :*: nu xs)
