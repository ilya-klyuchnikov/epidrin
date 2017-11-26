module MonadicsExtra

import Category
import Funnel
import Functorial
import Monadics

%default total
%access public export

-- not total
-- TODO - put annotation here

repeatedly : Trans x -> x -> x
repeatedly f = try effing
  where effing = (effing <++> pure) <.> f

repeatUntil : Trans x -> Trans x -> Trans x
repeatUntil step stop = stop <++> (repeatUntil step stop <.> step)
