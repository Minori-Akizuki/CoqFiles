module Qst where

import qualified Prelude

__ = Prelude.error "Logical or arity value used"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

and_rec :: (() -> () -> a1) -> a1
and_rec f =
  and_rect f

data Bool =
   True
 | False

negb :: Bool -> Bool
negb b =
  case b of {
   True -> False;
   False -> True}

data Nat =
   O
 | S Nat

data List a =
   Nil
 | Cons a (List a)

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

type Sig a =
  a
  -- singleton inductive, whose constructor was exist
  
sig_rect :: (a1 -> () -> a2) -> a1 -> a2
sig_rect f s =
  f s __

sig_rec :: (a1 -> () -> a2) -> a1 -> a2
sig_rec =
  sig_rect

leb :: Nat -> Nat -> Bool
leb m x =
  case m of {
   O -> True;
   S m' ->
    case x of {
     O -> False;
     S n' -> leb m' n'}}

filter :: (a1 -> Bool) -> (List a1) -> List a1
filter f l =
  case l of {
   Nil -> Nil;
   Cons x l0 ->
    case f x of {
     True -> Cons x (filter f l0);
     False -> filter f l0}}

qsort_terminate :: (List Nat) -> (List Nat)
qsort_terminate =
  and_rec (\_ _ l ->
    let {
     hrec l0 =
       case l0 of {
        Nil -> Nil;
        Cons x xs ->
         sig_rec (\rec_res _ ->
           sig_rec (\rec_res0 _ -> app rec_res (app (Cons x Nil) rec_res0))
             (hrec (filter (\t -> negb (leb x t)) xs)))
           (hrec (filter (leb x) xs))}}
    in hrec l)

qsort :: (List Nat) -> List Nat
qsort x =
  qsort_terminate x

