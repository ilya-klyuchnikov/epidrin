module Funnel

import Category

%default total
%access public export
%auto_implicits off

--------------------------------------------------------------
-- Funnel
--------------------------------------------------------------

interface Fun f => Funnel (f : Type -> Type) s t where
  fun : s -> t
  funnel : f s -> t

using (f : Type -> Type, x : Type)
  Fun f => Funnel f (Id x) (f (Id x)) where
    fun = eta
    funnel = id

using (f : Type -> Type, s : Type, t : Type)
  Fun f => Funnel f (K s t) (f (K s t)) where
    fun    = eta
    funnel = id

----- Funnels for base datatypes -----

----- () -----------------------

using (f : Type -> Type)
  Fun f => Funnel f () (f ()) where
    fun    = eta
    funnel = id

----- List ---------------------------

using (f : Type -> Type, x : Type)
  Fun f => Funnel f (List x) (f (List x)) where
    fun    = eta
    funnel = id

  Fun f => Funnel f ((List x) -> (List x)) (f (List x) -> f (List x)) where
    funnel fg fx = funnel (fg <$$> fx)
    fun g = funnel {f = f} {s = s} (eta g) where
      s : Type
      s = (List x) -> (List x)

  Fun f => Funnel f (x -> (List x) -> (List x)) (f x -> f (List x) -> f (List x)) where
    funnel fg fx = funnel (fg <$$> fx)
    fun g = funnel {f = f} {s = s} (eta g) where
      s : Type
      s = x -> (List x) -> (List x)

----- Maybe ---------------------------

using (f : Type -> Type, x : Type)
  Fun f => Funnel f (Maybe x) (f (Maybe x)) where
    fun    = eta
    funnel = id

  Fun f => Funnel f (x -> (Maybe x)) (f x -> (f (Maybe x))) where
    funnel fg fx = funnel (fg <$$> fx)
    fun g = funnel {f = f} {s = s} (eta g) where
      s : Type
      s = x -> (Maybe x)

----- (x, y) ---------------------------

using (f : Type -> Type, x : Type, y : Type)
  Fun f => Funnel f (x, y) (f (x, y)) where
    fun    = eta
    funnel = id

  Fun f => Funnel f (y -> (x, y)) (f y -> f (x, y)) where
    funnel fg fx = funnel (fg <$$> fx)
    fun g = funnel {f = f} {s = s} (eta g) where
      s : Type
      s = y -> (x, y)

  Fun f => Funnel f (x -> y -> (x, y)) (f x -> f y -> f (x, y)) where
    funnel fg fx = funnel (fg <$$> fx)
    fun g = funnel {f = f} {s = s} (eta g) where
      s : Type
      s = x -> y -> (x, y)

----- Either ---------------------------

using (f : Type -> Type, x : Type, y : Type)
  Fun f => Funnel f (Either x y) (f (Either x y)) where
    fun    = eta
    funnel = id

  Fun f => Funnel f (x -> Either x y) (f x -> f (Either x y)) where
    funnel fg fx = funnel (fg <$$> fx)
    fun g = funnel {f = f} {s = s} (eta g) where
      s : Type
      s = x -> Either x y

  Fun f => Funnel f (y -> Either x y) (f y -> f (Either x y)) where
    funnel fg fx = funnel (fg <$$> fx)
    fun g = funnel {f = f} {s = s} (eta g) where
      s : Type
      s = y -> Either x y
