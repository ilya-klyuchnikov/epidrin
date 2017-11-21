module Category

%default total
%access public export
%auto_implicits off

interface Unpack s t where
  un : {s : Type} -> {t : Type} -> s -> t
  nu : {t : Type} -> {s : Type} -> t -> s

--------- Id ------------

data Id : Type -> Type where
  MkId : {x : Type} -> x -> Id x

Functor Id where
  map f (MkId x) = MkId (f x)

using (x : Type)
  Unpack (Id x) x where
    un (MkId x) = x
    nu x = (MkId x)

--------- K ------------

data K : Type -> Type -> Type where
  MkK : {s : Type} -> {t : Type} -> s -> K s t

using (s : Type)
  Functor (K s) where
    map f (MkK x) = MkK x

using (s: Type, t: Type)
  Unpack (K s t) s where
    un (MkK x) = x
    nu x = (MkK x)

--------- Cross ---------

infixr 5 :*:

data Cross : (Type -> Type) -> (Type -> Type) -> Type -> Type where
  (:*:) : {f : Type -> Type} -> {g : Type -> Type } -> {x : Type} -> (f x) -> (g x) -> Cross f g x

-- alias
MkCross : {f : Type -> Type} -> {g : Type -> Type } -> {x : Type} -> (f x) -> (g x) -> Cross f g x
MkCross = (:*:)

using (f : Type -> Type, g: Type -> Type)
  (Functor f, Functor g) => Functor (Cross f g) where
    map f (x :*: y) = (map f x) :*: (map f y)

-- some examples:

cross1 : Cross List Maybe Nat
cross1 = [1] :*: (Just 1)

cross2 : Cross List Maybe Nat
cross2 = (:*:) {f = List} {g = Maybe} {x = Nat} [1] (Just 1)

--------- Endo ---------

data Endo : Type -> Type where
  MkEndo: {x : Type} -> (x -> x) -> Endo x

using (x : Type)
  Unpack (Endo x) (x -> x) where
    un (MkEndo x) = x
    nu x = (MkEndo x)

-- example
endo1 : Endo Nat
endo1 = MkEndo S

--------- Endo ---------

data Odne : Type -> Type where
  MkOdne: {x : Type} -> (x -> x) -> Odne x

using (x : Type)
  Unpack (Odne x) (x -> x) where
    un (MkOdne x) = x
    nu x = (MkOdne x)

--------- Fun ---------------
infixl 9 <$$>
interface Functor f => Fun (f : Type -> Type) where
  -- pure in Applicative
  eta    : {x : Type} -> x -> f x
  -- <*> in applicative, but nevertheless - also apply, f_apply?
  (<$$>) : {s : Type} -> {t : Type} -> f (s -> t) -> f s -> f t

--
infixl 9 </>

(</>) : {f : Type -> Type} -> Fun f => {s : Type} -> {t : Type} -> f s -> f t -> f s -- (<*) in idris
fs </> ft = eta const <$$> fs <$$> ft

infixl 9 <\>
(<\>) : {f : Type -> Type} -> Fun f => {s : Type} -> {t : Type} -> f s -> f t -> f t -- (*>) in idris
fs <\> ft = eta (const id) <$$> fs <$$> ft

funMap : {f : Type -> Type} -> Fun f => {s : Type} -> {t : Type} -> (s -> t) -> f s -> f t
funMap f a = eta f <$$> a

Fun Id where
  eta = nu
  (MkId f) <$$> (MkId s) = MkId (f s)

using (f : Type -> Type, g : Type -> Type)
  (Fun f, Fun g) => Fun (Cross f g) where
    eta x = (eta x) :*: (eta x)
    (f :*: g) <$$> (x :*: y) = (f <$$> x) :*: (g <$$> y)

--------------------------------------------------------------
-- Monoidal (monoid, really)
--------------------------------------------------------------

infixr 5 <++>
interface Monoidal x where
  m0 : x
  (<++>) : x -> x -> x

using (t : Type, s : Type)
  Monoidal t => Monoidal (s -> t) where
    m0 = const m0
    f <++> g = \x => (f x) <++> (g x)

to : {s : Type} -> {t : Type} -> s -> (s -> t) -> t
to a f = f a

using (s : Type)
  Monoidal s => Fun (K s) where
    eta _ = MkK m0
    (MkK x) <$$> (MkK y) = MkK (x <++> y)

using (x : Type)
  Monoidal (Endo x) where
    m0 = MkEndo id
    (MkEndo f) <++> (MkEndo g) = MkEndo (f . g)

using (x : Type)
  Monoidal (Odne x) where
    m0 = MkOdne id
    (MkOdne f) <++> (MkOdne g) = MkOdne (f . g)

when : {s : Type} -> Monoidal s => Bool -> s -> s
when False = m0
when True = id

Monoidal () where
  m0 = ()
  _ <++> _ =()

using (x : Type)
  Monoidal (List x) where
    m0 = []
    (<++>) = (++)

using (x : Type, y: Type)
  (Monoidal x, Monoidal y) => Monoidal (x, y) where
    m0 = (m0, m0)
    (x1, y1) <++> (x2, y2) = (x1 <++> x2, y1 <++> y2)

Monoidal Int where
  m0 = 0
  (<++>) = (+)

using (f : Type -> Type, g: Type -> Type, x : Type)
  (Monoidal (f x), Monoidal (g x)) => Monoidal (Cross f g x) where
    m0 = m0 :*: m0
    (x1 :*: y1) <++> (x2 :*: y2) = (x1 <++> x2) :*: (y1 <++> y2)
