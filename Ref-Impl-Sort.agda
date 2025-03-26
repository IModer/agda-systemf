{-
    This is just me remembering how to do things via iterators/recursors, and then implement treesort via them
-}

-- These can all be Church encoded
open import Data.Nat hiding (pred)
open import Data.Product
open import Data.Sum
open import Data.Tree.Binary renaming (foldr to foldrT)
open import Relation.Binary.PropositionalEquality
open import Data.List
open import Data.Bool
open import Data.Unit
open import Function

iteNat : {C : Set} → C → (C → C) → ℕ → C
iteNat z s zero    = z
iteNat z s (suc n) = s (iteNat z s n)


{-

iteNat2 z z = a
iteNat2 z s = b
iteNat2 s z = c
iteNat2 s s = d

compare      0       0  = EQ
compare (suc n)      0  = LT
compare      0  (suc m) = GT
compare (suc n) (suc m) = compare n m
-}

isZero : ℕ → Bool
isZero = iteNat true (λ _ → false)

recNat : {C : Set} → C → (ℕ → C → C) → ℕ → C
recNat z s zero    = z
recNat z s (suc n) = s n (recNat z s n)

pred : ℕ → ℕ
pred n = recNat zero (λ n r → n) n

eq : ℕ → ℕ → Bool
eq n = recNat {ℕ → Bool} (isZero) (λ x' r y → if (isZero y) then false else (r (pred y))) n

eq-t1 : eq 10 10 ≡ true
eq-t1 = refl
eq-t2 : eq 0 10 ≡ false
eq-t2 = refl
eq-t3 : eq 10 0 ≡ false
eq-t3 = refl

data Ord : Set where
    LT GT EQ : Ord

cmp : ℕ → ℕ → Ord
cmp n = 
    recNat {ℕ → Ord} 
    (λ x → if isZero x then EQ else GT) 
    (λ x' r y → if (isZero y) then LT else r (pred y)) 
    n

cmp-t1 : cmp 20 20 ≡ EQ
cmp-t1 = refl
cmp-t2 : cmp 0 20 ≡ GT
cmp-t2 = refl
cmp-t3 : cmp 20 0 ≡ LT
cmp-t3 = refl

{-
lte      0       0  = true
lte (suc n)      0  = false
lte      0  (suc m) = true
lte (suc n) (suc m) = lte n m
-}

lte : ℕ → ℕ → Bool
lte n = recNat (λ _ → true) (λ x' r y → if (isZero y) then false else (r (pred y))) n

lte-t1 : lte 0 20 ≡ true
lte-t1 = refl
lte-t2 : lte 0 0  ≡ true
lte-t2 = refl
lte-t3 : lte 20 0 ≡ false
lte-t3 = refl
lte-t4 : lte 6 5 ≡ false
lte-t4 = refl

BinTree : Set
BinTree = Tree ℕ ⊤

recTree : {A : Set} → (BinTree → BinTree → A → ℕ → A → A) → (⊤ → A) → BinTree → A
recTree f g (leaf x)     = g x
recTree f g (node l m r) = f l r (recTree f g l) m (recTree f g r)

-- First we do it via pattern matching

-- Flatten, turn a tree into a list in preorder
flatten' : BinTree → List ℕ
flatten' (leaf tt) = []
flatten' (node l n r) = flatten' l ++ (n ∷ []) ++ (flatten' r)

insert' : ℕ → BinTree → BinTree
insert' a (leaf tt)     = node (leaf tt) a (leaf tt) 
insert' a (node l i r) = if (a ≤ᵇ i) then (node (insert' a l) i r) else (node l i (insert' a r))

testTree : BinTree
testTree = node (node (leaf tt) 1 (leaf tt)) 2 (node (leaf tt) 3 (leaf tt))

treesort'-s : BinTree → List ℕ → BinTree
treesort'-s acc []       = acc 
treesort'-s acc (x ∷ xs) = treesort'-s (insert' x acc) xs

treesort' : List ℕ → List ℕ
treesort' = flatten' ∘ (treesort'-s (leaf tt))

testList : List ℕ
testList = 10 ∷ 4 ∷ 4 ∷ 2 ∷ 3 ∷ []


-- With eleminators
-- we use: 
--   recTree is the recursor for BinTree
--   foldrT is the fold (non dependant eleminator) for BinTree
--   foldr is the fold for List 

{-
foldr : (List ℕ → ℕ → List ℕ → List ℕ) → (⊤ → List ℕ) → BinTree → List ℕ
foldr f g (leaf x)     = g x
foldr f g (node l m r) = f (foldr f g l) m (foldr f g r)
-}

flatten : BinTree → List ℕ
flatten = foldrT (λ lacc n racc → lacc ++ n ∷ [] ++ racc) (λ _ → [])

insert : ℕ → BinTree → BinTree
insert n = recTree (λ l r lacc i racc → if (n ≤ᵇ i) then (node lacc i r) else (node l i racc)) (λ _ → node (leaf tt) n (leaf tt))

treesort : List ℕ → List ℕ
treesort = flatten ∘ (foldr insert (leaf tt))

-- So minimally we need
-- Types:
--  Bool                  -- ite
--  Natural numbers       -- fold, rec, isZero
--  BinTree               -- fold, rec
--  List                  -- fold, _++_

-- Functions:
--  ≤ : ℕ → ℕ → Bool
--  flatten : BinTree ℕ → List
--  insert  : ℕ → BinTree ℕ → BinTree ℕ