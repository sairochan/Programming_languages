module Main

import Data.List
import Data.Vect
import Data.Nat

%default total

append_assoc : (xs, ys, zs : List a) -> xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
append_assoc [] ys zs = Refl
append_assoc (x :: xs) ys zs = cong (x ::) (append_assoc xs ys zs)

list_ind : (0 p : List a -> Type) -> 
           p [] -> 
           ((x : a) -> {xs : List a} -> p xs -> p (x :: xs)) -> 
           (xs : List a) -> p xs
list_ind p nil_case cons_case [] = nil_case
list_ind p nil_case cons_case (x :: xs) = cons_case x (list_ind p nil_case cons_case xs)

append_assoc2 : (xs, ys, zs : List a) -> xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
append_assoc2 xs ys zs = list_ind (\xs => xs ++ (ys ++ zs) = (xs ++ ys) ++ zs)
                                  Refl
                                  (\x => \pxs => cong (x ::) pxs)
                                  xs

append_nil : (xs : List a) -> xs ++ [] = xs
append_nil = list_ind (\xs => xs ++ [] = xs)
                      Refl -- [] ++ [] = []
                      (\x => \pxs {- : xs ++ [] -} => cong (x ::) pxs)

len : List a -> Nat
len = list_ind (\_ => Nat)
               0
               (\_ => \n => S n)

data BTree : Type -> Type where
  Leaf : BTree a
  Branch :  (l : BTree a) -> a -> (r : BTree a) -> BTree a

%name BTree t

flip : BTree a -> BTree a 
flip Leaf = Leaf
flip (Branch l x r) = Branch (flip r) x (flip l)

flipflip : (t : BTree a) -> t = flip (flip t)
flipflip Leaf = Refl
flipflip (Branch l x r) = 
  rewrite sym (flipflip l) in
  rewrite sym (flipflip r) in
  Refl
  
btree_ind : (0 p : BTree a -> Type) ->
            p Leaf ->
            ({l : BTree a} -> (x : a) -> {r : BTree a} ->
             p l -> p r ->
             p (Branch l x r)) ->
            (t : BTree a) ->
            p t
btree_ind p leaf_case branch_case Leaf = leaf_case
btree_ind p leaf_case branch_case (Branch l x r) = branch_case x (btree_ind p leaf_case branch_case l)
                                                                 (btree_ind p leaf_case branch_case r)

flipflip2 : (t : BTree a) -> flip (flip t) = t
flipflip2 = btree_ind _
            Refl
            (\x => \pl => \pr => rewrite pl in rewrite pr in Refl)

data NEBTree : Type -> Type where
  Singleton : a -> NEBTree a
  LBranch : (l : NEBTree a) -> a -> NEBTree a
  RBranch : a -> (r : NEBTree a) -> NEBTree a
  LRBranch : (l : NEBTree a) -> a -> (r : NEBTree a) -> NEBTree a

%name NEBTree t

ne_flip : NEBTree a -> NEBTree a
ne_flip (Singleton x) = Singleton x
ne_flip (LBranch l x) = RBranch x (ne_flip l)
ne_flip (RBranch x r) = LBranch (ne_flip r) x
ne_flip (LRBranch l x r) = LRBranch (ne_flip r) x (ne_flip l)

ne_flipflip : (t : NEBTree a) -> ne_flip (ne_flip t) = t
ne_flipflip (Singleton x) = Refl
ne_flipflip (LBranch l x) = cong (\t => LBranch t x) (ne_flipflip l)
ne_flipflip (RBranch x r) = cong (\t => RBranch x t) (ne_flipflip r)
ne_flipflip (LRBranch l x r) = rewrite ne_flipflip l in rewrite ne_flipflip r in Refl

nebtree_ind : (0 p : NEBTree a -> Type) ->
              ((x : a) -> p (Singleton x)) ->
              ({l : NEBTree a} -> (x : a) ->
                p l ->
                p (LBranch l x)) ->
              ((x : a) -> {r : NEBTree a} ->
                p r ->
                p (RBranch x r)) ->
              ({l : NEBTree a} -> (x : a) -> {r : NEBTree a} ->
                p l -> p r ->
                p (LRBranch l x r)) ->
              (t : NEBTree a) -> p t
nebtree_ind p s_case l_case r_case lr_case (Singleton x) = 
  s_case x
nebtree_ind p s_case l_case r_case lr_case (LBranch l x) = 
  l_case x (nebtree_ind p s_case l_case r_case lr_case l)
nebtree_ind p s_case l_case r_case lr_case (RBranch x r) =
  r_case x (nebtree_ind p s_case l_case r_case lr_case r)
nebtree_ind p s_case l_case r_case lr_case (LRBranch l x r) =
  lr_case x (nebtree_ind p s_case l_case r_case lr_case l)
            (nebtree_ind p s_case l_case r_case lr_case r)
            
ne_flipflip2 : (t : NEBTree a) -> ne_flip (ne_flip t) = t
ne_flipflip2 = nebtree_ind _
                           (\x => Refl)
                           (\x => \eq => cong (\t => LBranch t x) eq)
                           (\x => \eq => cong (\t => RBranch x t) eq)
                           (\x => \eql => \eqr => rewrite eql in rewrite eqr in Refl)


vect_len : Vect n a -> Nat
vect_len [] = 0
vect_len (_ :: xs) = S (vect_len xs)

vect_len_spec : (xs : Vect n a) -> vect_len xs = n
vect_len_spec [] = Refl
vect_len_spec (_ :: xs) = cong S (vect_len_spec xs)


vect_ind : (0 p : (n : Nat) -> Vect n a -> Type) ->
           (p 0 []) ->
           ({n : Nat} -> (x : a) -> {xs : Vect n a} -> 
             p n xs ->
             p (S n) (x :: xs)) ->
           (n : Nat) -> (xs : Vect n a) -> p n xs
vect_ind p nil_case cons_case 0 [] = nil_case
vect_ind p nil_case cons_case (S len) (x :: xs) = cons_case x (vect_ind p nil_case cons_case len xs)

vect_len_spec2 : (n : Nat) -> (xs : Vect n a) -> vect_len xs = n
vect_len_spec2 = vect_ind _ Refl (\_ => \pxs => cong S pxs)

nat_ind : (0 p : Nat -> Type) ->
          p 0 ->
          ((n : Nat) -> p n -> p (S n)) ->
          (n : Nat) -> p n
nat_ind p z_case s_case 0 = z_case
nat_ind p z_case s_case (S k) = s_case k (nat_ind p z_case s_case k)

lteTrans : {x, y, z : Nat} -> LTE x y -> LTE y z -> LTE x z
lteTrans LTEZero prf2 = LTEZero
lteTrans (LTESucc {left = x'} {right = y'} prf1) (LTESucc {right = z'} prf2) = LTESucc (lteTrans prf1 prf2)

lte_ind : (0 p : (x, y : Nat) -> LTE x y -> Type) ->
          ((y : Nat) -> p 0 y LTEZero) ->
          ((x, y : Nat) -> (prf : LTE x y) -> p x y prf -> p (S x) (S y) (LTESucc prf)) ->
          (x, y : Nat) -> (prf : LTE x y) -> p x y prf
lte_ind p z_case s_case 0 y LTEZero = z_case y
lte_ind p z_case s_case (S left) (S right) (LTESucc prf) = 
  s_case left right prf (lte_ind p z_case s_case left right prf)

lteTrans'_helper : (x, y : Nat) -> LTE x y -> (z : Nat) -> LTE y z -> LTE x z
lteTrans'_helper = lte_ind (\x => \y => \prf1 => (z: Nat) -> LTE y z -> LTE x z)
                   (\y => \z => \prf => LTEZero)
                   (\x => \y => \prf1 => \rec => \z => \(LTESucc prf2) => LTESucc (rec _ prf2))
                   
lteTrans' : {x, y, z : Nat} -> LTE x y -> LTE y z -> LTE x z
lteTrans' prf1 prf2 = lteTrans'_helper x y prf1 z prf2
