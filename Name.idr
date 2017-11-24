module Name

import Category
import Funnel
import Functorial
import Utils
import Zip

%default total
%access public export

-- LName

Name : Type
Name = Zip (String, Int)

data LName = Long Name

Eq LName where
  (Long n1) == (Long n2) = n1 == n2

Fun f => Funnel f LName (f LName) where
  fun    = eta
  funnel = id

Show LName where
  show (Long MkZip) = ""
  show (Long (siz :<: (s,i))) = (show siz') ++ s ++ show i where
    siz' : LName
    siz' = assert_smaller (Long (siz :<: (s,i)))
                          (Long siz)

infixl 9 ///

interface Localize x where
  (///) : LName -> x -> LName

Localize LName where
  (Long nz1) /// (Long nz2) = Long (nz1 <++> nz2)

Localize (String, Int) where
  (Long nz) /// si = Long (nz :<: si)

Localize String where
  (Long nz) /// s = Long (nz :<: (s, 0))

Ord LName where
  compare (Long nom) (Long nam) = compare (nom <>> nil) (nam <>> nil)

relName : LName -> LName -> LName
relName (Long root) (Long nom) =
  case (commonPrefix (root <>> nil) (nom <>> nil)) of
    (_, outs, ins) => Long ((MkZip <>< (up (const ("^", 0)) outs)) <>< ins)

-- UName

data UName = UN String

Eq UName where
  (UN n1) == (UN n2) = n1 == n2

Show UName where
  show (UN s) = s

Alpha : Type
Alpha = List (Char, String)

coAlpha : Alpha -> Alpha -> Alpha
coAlpha = flip (++)

alpha : Alpha -> UName -> UName
alpha css (UN s) = UN (blat (cast {to = List Char} s) []) where
  blat : List Char -> List Char ->  String
  blat [] x = cast {to=String} x
  blat (c :: cs) x = case (lookup c css) of
                                       Just s' => s' ++ (blat cs x)
                                       Nothing => (cast c) ++ (blat cs x)

mkAlpha : UName -> UName -> Alpha
mkAlpha (UN p) (UN t) = let p1 = reverse (filter isAlpha (cast {to = List Char} p))
                            t1 = reverse (filter isAlpha (cast {to = List Char} p))
                        in  mk p1 t1 where
    mk : (List Char) -> (List Char) -> Alpha
    mk _ [] = []
    mk [] _ = []
    mk (p :: ps) ts1@(t :: ts) =
      if p == t then mk ps ts else (if ps == []
                                    then [(p, cast {to = String} (reverse ts1))]
                                    else (p, cast {to = String} [t]) :: (mk ps ts))


scPrefix' : List (List Char) -> List Char
scPrefix' [] = []
scPrefix' (s :: ss) = foldr inStep s ss where
  inStep : List Char -> List Char -> List Char
  inStep (c :: cs) (d :: ds) = if c == d then c :: (inStep cs ds) else []
  inStep _         _         = []

-- find a commonPrefix
scPrefix : List String -> String
scPrefix = (cast {to = String}) . scPrefix' .  (map (cast {to = List Char}))


rootName : List String -> String
rootName [] = "x"
rootName ss = if ps == "" then "" else ps where
  pref : String
  pref = scPrefix ss
  suff : String
  suff = scPrefix (map ((cast {to = String}) . (List.reverse) . drop (length pref) . (cast {to = List Char})) ss)
  ps : String
  ps = pref ++ (reverse suff)

data IndElim = ICase | IView | IMemo | IRec | IGen

Eq IndElim where
  ICase == ICase = True
  IView == IView = True
  IMemo == IMemo = True
  IRec == IRec = True
  IGen == IGen = True
  _ == _ = False
