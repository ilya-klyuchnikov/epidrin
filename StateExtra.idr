module State

-- For some strange reason, Idris halts (or becomes extremely slow)
-- if this code is put directly into State.idr.
-- So, putting it into a separate module.

import State
import Category
import Funnel
import Functorial

%default total
%access public export

Fun f => Funnel f (StateT m s a) (f (StateT m s a)) where
  fun    = eta
  funnel = id

sequentially : (Functorial g, Monoidal y, Monad m) =>
  (x -> StateT m s y) -> g x -> StateT m s y
sequentially f gx = noitca step (pure m0) gx where
  step s x = eta (<++>) <$$> s <$$> f x
