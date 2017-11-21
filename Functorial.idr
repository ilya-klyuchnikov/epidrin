module Functorial

import Category
import Funnel

%default total
%access public export
%auto_implicits off

infixl 9 <^>
interface Functorial (g : Type -> Type) where
  (<^>) : {f : Type -> Type} ->
          Fun f =>
          {s : Type} ->
          {t : Type} ->
          (s -> f t) -> (g s) -> f (g t)

infixl 9 <^^>
(<^^>) : {f : Type -> Type} ->
         {g : Type -> Type} ->
         {h : Type -> Type} ->
         (Fun f, Functorial g, Functorial h) =>
         {s : Type} ->
         {t : Type} ->
         (s -> f t) -> g (h s) -> f (g (h t))
f <^^> ghs = (f <^>) <^> ghs

up : {g : Type -> Type} ->
     Functorial g =>
     {s : Type} ->
     {t : Type} ->
     (s -> t) -> g s -> g t
up g gs = un ((MkId . g) <^> gs)

up2 : {g : Type -> Type} ->
      {h : Type -> Type} ->
      (Functorial h, Functorial g) =>
      {s : Type} ->
      {t : Type} ->
      (s -> t) -> g (h s) -> g (h t)
up2 = up . up

using (g : Type -> Type, h : Type -> Type)
  (Functorial g, Functorial h) => Functorial (Cross g h) where
    g <^> (x :*: y) = (eta (:*:) <$$> (g <^> x)) <$$> (g <^> y)

infixl 9 <!>
(<!>) : {g : Type -> Type} ->
        (Functorial g) =>
        {s : Type} ->
        (Monoidal s) =>
        {x : Type} ->
        (x -> s) -> g x -> s
(<!>) {g} {s} {x} f = un {s = K s (g x)} {t = s} . ((MkK {s = s} {t = x} . f) <^>)

action : {g : Type -> Type} ->
         Functorial g =>
         {y : Type} ->
         {x : Type} ->
         (x -> y -> y) -> g x -> y -> y
action {g} {x} {y} f gx = (un {s = Endo y} {t = y -> y}) ((<!>) {x = x} {s = Endo y} (MkEndo . f) gx)

noitca : {g : Type -> Type} ->
         Functorial g =>
         {y : Type} ->
         {x : Type} ->
         (y -> x -> y) -> y -> g x -> y
noitca {g} {x} {y} f y' gx = (un {s = Odne y} {t = y -> y}) (((<!>) {g = g} {x = x} {s = Odne y}) (MkOdne {x = y} . (flip f)) gx) y'


Functorial Maybe where
  (<^>) {f} g (Nothing) = fun {f=f} Nothing
  (<^>) {f} g (Just x)  = fun {f=f} Just (g x)

using (f : Type -> Type)
  Fun f => Functorial List where
    (<^>) {f} {s} {t} g []        = fun {f = f} []
    (<^>) {f} {s} {t} g (x :: xs) = fun {f = f} {s = (t -> (List t) -> (List t))} (::) (g x) (g <^> xs)
