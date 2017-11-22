module Logic

import Category
import Funnel

%default total
%access public export

data Might = MkMight Bool

Unpack Might Bool where
  un (MkMight p) = p
  nu p = (MkMight p)

Monoidal Might where
  m0 = MkMight False
  (MkMight p) <++> (MkMight q) = MkMight (p || q)

Fun f => Funnel f Might (f Might) where
  fun    = eta
  funnel = id

data Must = MkMust Bool

Unpack Must Bool where
  un (MkMust p) = p
  nu p = (MkMust p)

Monoidal Must where
  m0 = MkMust True
  (MkMust p) <++> (MkMust q) = MkMust (p && q)

Fun f => Funnel f Must (f Must) where
  fun    = eta
  funnel = id
