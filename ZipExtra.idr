module ZipExtra

import Category
import Funnel
import Zip

%access public export

-- Fun instances --
-- this stuff should be potentially rewritten into Streams or something else

Fun Zip where
  (fz :<: f) <$$> (sz :<: s) = fz <$$> sz :<: f s
  _          <$$> _          = MkZip
  eta x = (eta x) :<: x

Fun UTip where
  (f :>: fs) <$$> (s :>: ss) = f s :>: fs <$$> ss
  _          <$$> _          = nil
  eta x = x :>: eta x
