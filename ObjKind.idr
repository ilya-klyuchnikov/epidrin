module Zip

import Category
import Funnel
import Name

%default total
%access public export

data Bind = Lam | All | Ex

Eq Bind where
  Lam == Lam = True
  All == All = True
  Ex  == Ex  = True
  _   == _   = False

Show Bind where
  show Lam = "lam"
  show All = "all"
  show Ex  = "ex"

data Visibility = NormV | UnifV

Eq Visibility where
  NormV == NormV = True
  UnifV == UnifV = True
  _     == _     = False

Show Visibility where
  show NormV = ""
  show UnifV = "_"

data Con = TypeCon | DataCon LName

Eq Con where
  TypeCon == TypeCon = True
  (DataCon ln1) == (DataCon ln2) = ln1 == ln2
  _ == _ = False

Show Con where
  show TypeCon = "TypeCon"
  show (DataCon d) = "(DataCon " ++ (show d) ++ ")"

data ObjKind
  = ObjAbst Bind Visibility
  | ObjWit Visibility
  | ObjDefn
  | ObjDecl Con
  | ObjPar
  | ObjBad
  | ObjRec

Eq ObjKind where
  (ObjAbst b1 v1) == (ObjAbst b2 v2) = b1 == b2 && v1 == v2
  (ObjWit v1)     == (ObjWit v2)     = v1 == v2
  (ObjDecl c1)    == (ObjDecl c2)    = c1 == c2
  ObjDefn == ObjDefn = True
  ObjPar  == ObjPar  = True
  ObjBad  == ObjBad  = True
  ObjRec  == ObjRec  = True
  _       == _       = False

Show ObjKind where
  show (ObjAbst b v) = show b ++ show v
  show (ObjWit v) = "wit" ++ show v
  show ObjDefn = "let"
  show (ObjDecl TypeCon) = "data"
  show (ObjDecl _) = "con"
  show ObjPar = ""
  show ObjBad = "bad"
  show ObjRec = "rec"

Fun f => Funnel f Con (f Con) where
  fun    = eta
  funnel = id

instance Fun f => Funnel f ObjKind (f ObjKind) where
  fun    = eta
  funnel = id

Desc : Type
Desc = (UName,       -- user's preferred name
        Visibility)  -- instruction to the elaborator

dull : Desc
dull = (UN "", NormV)
