{-# OPTIONS --rewriting  #-}

module SystemF-SecondOrder where

open import Agda.Primitive
open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_⊔_;zero;suc;Ordering;compare;pred)
open import Agda.Builtin.Equality.Rewrite
open import Function

module _ where
    record Times(A B : Set) : Set where
        constructor pair
        field
            fst : A
            snd : B
    
    data Nat' : Set where
        zero' : Nat'
        suc' : Nat' → Nat'
    
    iteNat' : {C : Set} → C → (C → C) → Nat' → C
    iteNat' f g zero' = f
    iteNat' f g (suc' n) = g (iteNat' f g n)

    recNat' : {C : Set} → C → (Nat' → C → C) → Nat' → C
    recNat' {C} f g n = 
        Times.fst 
        (iteNat' {Times C Nat'} 
        (pair f zero') 
        (λ {(pair c m) → pair (g m c) (suc' m)}) 
        n)
    
    plus' : Nat' → Nat' → Nat'
    plus' n m = iteNat' m suc' n

    _ : plus' (suc' (suc' (suc' zero'))) (suc' (suc' (suc' zero'))) ≡ 
        (suc' (suc' (suc' (suc' (suc' (suc' zero'))))))
    _ = refl

    test : Nat' → Nat'
    test zero' = zero'
    test (suc' x) = plus' x (test x)

    test' : Nat' → Nat'
    test' = recNat' zero' λ n acc → plus' n acc

    -- test m = (m-1) + ((m-2) + ...)
    -- test 4 = 3 + 2 + 1 + 0 = 6
    _ : test (suc' (suc' (suc' (suc' zero')))) ≡ test' (suc' (suc' (suc' (suc' zero'))))
    _ = refl

    data BinTree'(A : Set) : Set where
        leaf' : A → BinTree' A
        node' : BinTree' A → BinTree' A → BinTree' A
    
    iteTree' : {A C : Set} → (A → C) → (C → C → C) → BinTree' A → C
    iteTree' l n (leaf' a) = l a
    iteTree' l n (node' b j) = n (iteTree' l n b) (iteTree' l n j)

    recTree' : {A C : Set} → (A → C) → (BinTree' A → BinTree' A → C → C → C) → BinTree' A → C
    recTree' f g (leaf' a) = f a
    recTree' f g (node' l r) = g l r (recTree' f g l) (recTree' f g r)

    recTreeP : {A C : Set} → (A → C) → (BinTree' A → BinTree' A → C → C → C) → BinTree' A → C
    recTreeP {A}{C} l n t = 
        Times.fst (iteTree' {A} {Times C (BinTree' A)} 
        (λ a → pair (l a) (leaf' a)) 
        (λ {(pair c b) (pair c' j) → pair (n b j c c') (node' b j)})
        t)

    test1 : {A : Set} → BinTree' A → A
    test1 (leaf' x) = x
    test1 (node' l _) = test1 l

    test1' : {A : Set} → BinTree' A → A
    test1' = recTreeP (λ x → x) λ x x₁ x₂ x₃ → x₂
    {-
    data Bool : Set where
        true false : Bool

    t : BinTree' Bool
    t = node' (node' (leaf' false) (leaf' true)) (leaf' false)

    _ : test1 t ≡ test1' t
    _ = refl
    -}

record Model(i j : Level) : Set (lsuc (i ⊔ j)) where
    infixr 6 _⇒_
    infixl 6 _∙_
    infixl 7 _•_
    field
        Ty : Set i
        Tm : Ty → Set j
        
        ∀' : (Ty → Ty) → Ty
        Lam : {F : Ty → Ty} → ((X : Ty) → Tm (F X)) → Tm (∀' F)
        _•_ : {F : Ty → Ty} → Tm (∀' F) → (X : Ty) → Tm (F X)
        ∀β : {F : Ty → Ty}{t : (X : Ty) → Tm (F X)}{X : Ty} → (Lam t) • X ≡ t X
        ∀η : {F : Ty → Ty} (f : Tm (∀' F)) → f ≡ Lam(λ X → f • X) 

        _⇒_ : Ty → Ty → Ty
        lam : {A B : Ty} → (Tm A → Tm B) → Tm (A ⇒ B)
        _∙_ : {A B : Ty} → Tm (A ⇒ B) → Tm A → Tm B
        ⇒β : {A B : Ty}{f : Tm A → Tm B}{x : Tm A} → lam f ∙ x ≡ f x
        ⇒η : {A B : Ty}{f : Tm (A ⇒ B)} → f ≡ lam (λ x → f ∙ x)
    
{-
private module _(i j : Level)(M : Model i j) where
    module M' = Model M
    open M'

    --  Helpers for working with lambdas

    lam2 : {A B C : Ty} → (Tm A → Tm B → Tm C) → Tm (A ⇒ B ⇒ C)
    lam2 f = lam (λ a → lam (λ b → f a b))

    lam3 : {A B C D : Ty} → (Tm A → Tm B → Tm C → Tm D) → Tm (A ⇒ B ⇒ C ⇒ D)
    lam3 f = lam (λ a → lam (λ b → lam (λ c → f a b c)))


    postulate
        funext : {A : Set}{B : A → Set} → (f g : (a : A) → B a) → (∀ x → f x ≡ g x) → f ≡ g

    ⊥ : Ty
    ⊥ = ∀' (λ X → X)

    exfalso : {A : Ty} → Tm ⊥ → Tm A
    exfalso {A} b = b • A

    ⊤ : Ty
    ⊤ = ∀' λ X → (X ⇒ X)

    tt : Tm ⊤
    tt = Lam (λ X → lam (λ x → x))

    -- We can church encode type formers using forall
    infixl 10 _×_
    _×_ : Ty → Ty → Ty
    A × B = ∀' (λ X → (A ⇒ B ⇒ X) ⇒ X)

    _,_ : {A B : Ty} → Tm A → Tm B → Tm (A × B)
    a , b = Lam (λ X → lam (λ f → f ∙ a ∙ b))

    fst : {A B : Ty} → Tm (A × B) → Tm A
    fst {A}{B} x = x • A ∙ lam (λ a → lam (λ b → a))

    snd : {A B : Ty} → Tm (A × B) → Tm B
    snd {A}{B} x = x • B ∙ lam (λ a → lam (λ b → b))

    ×β₁ : {A B : Ty}{a : Tm A}{b : Tm B} → fst (a , b) ≡ a
    ×β₁ {A}{B}{a}{b} = 
        trans (cong (_∙ lam (λ a → lam (λ b → a))) ∀β) 
        (trans ⇒β 
        (trans (cong (_∙ b) ⇒β) 
        ⇒β))
    
    ×β₂ : {A B : Ty}{a : Tm A}{b : Tm B} → snd (a , b) ≡ b
    ×β₂ {A}{B}{a}{b} = 
        trans (cong (_∙ lam (λ a → lam (λ b → b))) ∀β) 
        (trans ⇒β 
        (trans (cong (_∙ b) ⇒β) 
        ⇒β))

    _⊎_ : Ty → Ty → Ty
    A ⊎ B = ∀' (λ X → (A ⇒ X) ⇒ (B ⇒ X) ⇒ X)

    inl : {A B : Ty} → Tm A → Tm (A ⊎ B)
    inl {A}{B} a = Lam (λ X → lam (λ f → lam (λ g → f ∙ a)))
    inr : {A B : Ty} → Tm B → Tm (A ⊎ B)
    inr {A}{B} b = Lam (λ X → lam (λ f → lam (λ g → g ∙ b)))
    
    case : {A B C : Ty} → (Tm A → Tm C) → (Tm B → Tm C) → Tm (A ⊎ B) → Tm C
    case {A}{B}{C} f g s = s • C ∙ lam (λ a → f a) ∙ lam (λ b → g b)

    -- We can prove βs

    -- Do we need funext?
    {-
    ×η : {A B : Ty}{t : Tm (A × B)} → (fst t , snd t) ≡ t
    ×η {A}{B}{t} = ?
    -}

    -- Exists
    Exists : (Ty → Ty) → Ty
    Exists F = ∀' (λ X → (∀' (λ A → (F A ⇒ X))) ⇒ X) 

    mkExists : {F : Ty → Ty} → (X : Ty) → Tm (F X) → Tm (Exists F)
    mkExists X t = Lam (λ Y → lam (λ f → f • X ∙ t))

    caseExists : {F : Ty → Ty}{C : Ty} → ((X : Ty) → Tm (F X) → Tm C) → Tm (Exists F) → Tm C
    caseExists {F}{C} f e = e • C ∙ Lam (λ X → lam (λ fx → f X fx))

    Existsβ : {F : Ty -> Ty}{C : Ty} → (t : (X : Ty) → Tm (F X) → Tm C)(X : Ty)(w : Tm (F X)) → caseExists t (mkExists X w) ≡ t X w
    Existsβ t X w = 
        trans (cong (_∙ Lam (λ Y → lam (t Y))) ∀β) 
        (trans ⇒β 
        (trans (cong (_∙ w) ∀β) 
        ⇒β))

    -- We can also church encode coinductive types using Exists
    Stream : Ty → Ty
    Stream A = Exists (λ X → (X ⇒ A) × (X ⇒ X) × X)

    head : {A : Ty} → Tm (Stream A) → Tm A
    head {A} xs = (xs • A) ∙ Lam (λ X → lam (λ t → t • A ∙ lam (λ t' → lam (λ x → t' • A ∙ lam (λ f → lam (λ g → f ∙ x))))))

    tail : {A : Ty} → Tm (Stream A) → Tm (Stream A)
    tail {A} xs = 

    -- We give treesort, a sorting algorihms

    -- Natural numbers

    Nat : Ty
    Nat = ∀' λ X → X ⇒ (X ⇒ X) ⇒ X

    zero : Tm Nat
    zero = Lam (λ X → lam (λ z → lam (λ s → z)))

    suc : Tm Nat → Tm Nat
    suc n = Lam (λ X → lam (λ z → lam (λ s → s ∙ (n • X ∙ z ∙ s))))

    iteNat : {A : Ty} → Tm A → (Tm A → Tm A) → Tm Nat → Tm A
    iteNat {A} z s n = n • A ∙ z ∙ lam (λ x → s x)

    iteNat2 : {A : Ty} → Tm A → Tm A → (Tm A → Tm A) → (Tm A → Tm A) → Tm Nat → Tm Nat → Tm A
    iteNat2 z z' s s' n m = 
        iteNat 
            (iteNat z s m) 
            (λ a → iteNat z' s' m) 
        n

    [_]↑ : ℕ → Tm Nat
    [ ℕ.zero ]↑ = zero
    [ ℕ.suc x ]↑ = suc ([ x ]↑)

    -- We have ordering on Nat
    -- That is : a type data Ordering = LT | GT |EQ
    -- and a function compare : Nat → Nat → Ordering

    Ordering : Ty
    Ordering = ∀' λ X → X ⇒ X ⇒ X ⇒ X

    LT GT EQ : Tm Ordering
    LT = Lam (λ X → lam3 (λ lt gt eq → lt))
    GT = Lam (λ X → lam3 (λ lt gt eq → gt))
    EQ = Lam (λ X → lam3 (λ lt gt eq → eq))

    foldO : {C : Ty} → Tm C → Tm C → Tm C → Tm Ordering → Tm C
    foldO {C} lt gt eq o = o • C ∙ lt ∙ gt ∙ eq
    
    testO : foldO [ 0 ]↑ [ 1 ]↑ [ 2 ]↑ LT ≡ [ 0 ]↑
    --testO = trans ? ? 

    {-
    compare      0       0  = EQ
    compare (suc n)      0  = LT
    compare      0  (suc m) = GT
    compare (suc n) (suc m) = compare n m

    compare      0       m = if m > 0 then GT else EQ
    compare (suc n)      m = ?
    -}
    
    compare : Tm Nat → Tm Nat → Tm Ordering
    compare n m = iteNat2 EQ LT (λ _ → GT) (λ x → LT) n m

    _ : compare zero zero ≡ EQ
    _ =

        -- We have ordering on Nat
    -- That is : a type data Ordering = LT | GT |EQ
    -- and a function compare : Nat → Nat → Ordering

    Ordering : Ty
    Ordering = ∀' λ X → X ⇒ X ⇒ X ⇒ X

    LT GT EQ : Tm Ordering
    LT = Lam (λ X → lam3 (λ lt gt eq → lt))
    GT = Lam (λ X → lam3 (λ lt gt eq → gt))
    EQ = Lam (λ X → lam3 (λ lt gt eq → eq))

    foldO : {C : Ty} → Tm C → Tm C → Tm C → Tm Ordering → Tm C
    foldO {C} lt gt eq o = o • C ∙ lt ∙ gt ∙ eq
    
    testO-t1 : foldO [ 0 ]↑ [ 1 ]↑ [ 2 ]↑ LT ≡ [ 0 ]↑
    testO-t1 = refl
    testO-t2 : foldO [ 0 ]↑ [ 1 ]↑ [ 2 ]↑ GT ≡ [ 1 ]↑
    testO-t2 = refl
    testO-t3 : foldO [ 0 ]↑ [ 1 ]↑ [ 2 ]↑ EQ ≡ [ 2 ]↑
    testO-t3 = refl

    --compare : Tm Nat → Tm Nat → Tm Ordering
    --compare n m = iteNat2 EQ LT (λ _ → GT) (λ x → LT) n m
 
    --_ : compare (suc zero) (suc zero) ≡ EQ
    --_ = ?

    -- We have the type of lists

    List : Ty → Ty
    List A = ∀' (λ X → X ⇒ (A ⇒ X ⇒ X) ⇒ X)

    nil : {A : Ty} → Tm (List A)
    nil {A} = Lam (λ X → lam (λ n → lam (λ c → n)))

    cons : {A : Ty} → Tm A → Tm (List A) → Tm (List A)
    cons {A} a l = Lam (λ X → lam (λ n → lam (λ c → c ∙ a ∙ (l • X ∙ n ∙ c))))

    foldl : {A B : Ty} → Tm B → (Tm A → Tm B → Tm B) → Tm (List A) → Tm B
    foldl {A}{B} b f t = t • B ∙ b ∙ lam (λ a → lam (λ acc → f a acc))

    -- And the type of Binary Trees
    -- We store items in the leafs
    BinTree : Ty → Ty
    BinTree A = ∀' (λ X → (A ⇒ X) ⇒ (X ⇒ X ⇒ X) ⇒ X)

    leaf : {A : Ty} → Tm A → Tm (BinTree A)
    leaf {A} a = Lam (λ X → lam (λ l → lam (λ n → l ∙ a)))

    node : {A : Ty} → Tm (BinTree A) → Tm (BinTree A) → Tm (BinTree A)
    node {A} b j = Lam (λ X → lam (λ l → lam (λ n → n ∙ (b • X ∙ l ∙ n) ∙ (j • X ∙ l ∙ n))))

    iteTree : {A C : Ty} → (Tm A → Tm C) → (Tm C → Tm C → Tm C) → Tm (BinTree A) → Tm C
    iteTree {A} {C} l n t = t • C ∙ (lam λ a → l a) ∙ lam (λ b → lam (λ j → n b j))

    recTree : {A C : Ty} → (Tm A → Tm C) → (Tm (BinTree A) → Tm (BinTree A) → Tm C → Tm C → Tm C) → Tm (BinTree A) → Tm C
    recTree {A}{C} f g t = 
        fst (iteTree {A} {C × (BinTree A)} 
        (λ a → (f a , leaf a)) 
        (λ b j → g (snd b) (snd j) (fst b) (fst j) , node (snd b) (snd j)) 
        t)

    flatten : Tm (BinTree Nat) → Tm (List Nat)
    flatten t = 

    insert : {A : Ty} → Tm A → Tm (BinTree A) → Tm (BinTree A)
    insert {A} t = 

    -- Not positive functor, has no elements
    Weird : Ty
    Weird = ∀' λ X → (X ⇒ X) ⇒ X
-}

module Syntax where
    infixr 6 _⇒_
    infixl 6 _∙_
    infixl 7 _•_
    -- Contains no dependency
    {-# NO_POSITIVITY_CHECK #-}
    data Ty : Set where
        _⇒_ : Ty → Ty → Ty
        ∀' : (Ty → Ty) → Ty

    {-# NO_POSITIVITY_CHECK #-}
    data Tm : Ty → Set where
        lam : {A B : Ty} → (Tm A → Tm B) → Tm (A ⇒ B)
        Lam : {F : Ty → Ty} → ((X : Ty) → Tm (F X)) → Tm (∀' F)
--        _∙_ : {A B : Ty} → Tm (A ⇒ B) → Tm A → Tm B
--        _•_ : {F : Ty → Ty} → Tm (∀' F) → (X : Ty) → Tm (F X)

    _∙_ : {A B : Ty} → Tm (A ⇒ B) → Tm A → Tm B
    lam f ∙ t = f t
    _•_ : {F : Ty → Ty} → Tm (∀' F) → (X : Ty) → Tm (F X)
    Lam F • X = F X

    postulate
--        ∀β : {F : Ty → Ty}{t : (X : Ty) → Tm (F X)}{X : Ty} → (Lam t) • X ≡ t X
        ∀η : {F : Ty → Ty} (f : Tm (∀' F)) → f ≡ Lam(λ X → f • X) 

--        ⇒β : {A B : Ty}{f : Tm A → Tm B}{x : Tm A} → lam f ∙ x ≡ f x
        ⇒η : {A B : Ty}{f : Tm (A ⇒ B)} → f ≡ lam (λ x → f ∙ x)

--        {-# REWRITE ⇒β ∀β #-}

    Syntax : Model lzero lzero
    Model.Ty Syntax = Ty
    Model.Tm Syntax = Tm
    Model.∀' Syntax = ∀'
    Model.Lam Syntax = Lam
    Model._•_ Syntax = _•_
    Model.∀β Syntax = refl -- because of the rewrite rules
    Model.∀η Syntax = ∀η
    Model._⇒_ Syntax = _⇒_
    Model.lam Syntax = lam
    Model._∙_ Syntax = _∙_
    Model.⇒β Syntax = refl -- because of the rewrite rules
    Model.⇒η Syntax = ⇒η
    
    infixl 10 _×_
    _×_ : Ty → Ty → Ty
    A × B = ∀' (λ X → (A ⇒ (B ⇒ X)) ⇒ X)

    _,_ : {A B : Ty} → Tm A → Tm B → Tm (A × B)
    a , b = Lam (λ X → lam (λ f → (f ∙ a) ∙ b))

    fst : {A B : Ty} → Tm (A × B) → Tm A
    fst {A}{B} x = (x • A) ∙ lam (λ a → lam (λ b → a))

    snd : {A B : Ty} → Tm (A × B) → Tm B    
    snd {A}{B} x = (x • B) ∙ lam (λ a → lam (λ b → b))
    
    {-
    ×η : {A B : Ty}{t : Tm (A ×' B)} → (fst' t ,' snd' t) ≡ t
    ×η {A} {B} {t} = ?
    -}

    -- tresort here:

    lam2 : {A B C : Ty} → (Tm A → Tm B → Tm C) → Tm (A ⇒ B ⇒ C)
    lam2 f = lam (λ a → lam (λ b → f a b))

    lam3 : {A B C D : Ty} → (Tm A → Tm B → Tm C → Tm D) → Tm (A ⇒ B ⇒ C ⇒ D)
    lam3 f = lam (λ a → lam (λ b → lam (λ c → f a b c)))

    Bool : Ty
    Bool = ∀' λ X → X ⇒ X ⇒ X

    true : Tm Bool
    true = Lam (λ X → lam (λ t → lam (λ f → t)))
    false : Tm Bool
    false = Lam (λ X → lam (λ t → lam (λ f → f)))

    ite : {A : Ty} → Tm A → Tm A → Tm Bool → Tm A
    ite {A} t f b = b • A ∙ t ∙ f

    Nat : Ty
    Nat = ∀' λ X → X ⇒ (X ⇒ X) ⇒ X

    zero : Tm Nat
    zero = Lam (λ X → lam (λ z → lam (λ s → z)))

    suc : Tm Nat → Tm Nat
    suc n = Lam (λ X → lam (λ z → lam (λ s → s ∙ (n • X ∙ z ∙ s))))

    iteNat : {A : Ty} → Tm A → (Tm A → Tm A) → Tm Nat → Tm A
    iteNat {A} z s n = n • A ∙ z ∙ lam (λ x → s x)

    [_]↑ : ℕ → Tm Nat
    [ ℕ.zero ]↑ = zero
    [ ℕ.suc x ]↑ = suc ([ x ]↑)

    -- We use products to encode the recursor
    recNat : {A : Ty} → Tm A → (Tm Nat → Tm A → Tm A) → Tm Nat → Tm A
    recNat {A} f g n = snd (iteNat (zero , f) (λ x →  suc (fst x) , g (fst x) (snd x)) n)

    isZero : Tm Nat → Tm Bool
    isZero = iteNat true (λ _ → false)

    pred : Tm Nat → Tm Nat
    pred n = recNat zero (λ m _ → m) n

    lessthen : Tm Nat → Tm (Nat ⇒ Bool)
    lessthen n = recNat (lam (λ _ → true)) (λ x' r → lam λ y → ite false (r ∙ (pred y)) (isZero y)) n

    -- Lists

    List : Ty → Ty
    List A = ∀' (λ X → X ⇒ (A ⇒ X ⇒ X) ⇒ X)

    nil : {A : Ty} → Tm (List A)
    nil = Lam (λ X → lam2 (λ n c → n)) 

    cons : {A : Ty} → Tm A → Tm (List A) → Tm (List A)
    cons {A} a xs = Lam (λ X → lam2 (λ n c → c ∙ a ∙ (xs • X ∙ n ∙ c)))

    iteList : {A C : Ty} → Tm C → (Tm A → Tm C → Tm C) → Tm (List A) → Tm C
    iteList {A}{C} n c xs = xs • C ∙ n ∙ lam2 (λ a c' → c a c')

    {-
        _++_
        [] ++ y      = y 
        x ∷ xs ++ ys = x ∷ (xs ++ ys)
    -}

    concat : {A : Ty} → Tm (List A) → Tm (List A) → Tm (List A)
    concat xs ys = iteList ys cons xs

    concat-t1 : concat (cons [ 1 ]↑ (cons [ 1 ]↑ nil)) (cons [ 1 ]↑ (cons [ 1 ]↑ nil)) ≡ (cons [ 1 ]↑ (cons [ 1 ]↑ (cons [ 1 ]↑ (cons [ 1 ]↑ nil))))
    concat-t1 = refl
    concat-t2 : concat (cons [ 1 ]↑ (cons [ 1 ]↑ nil)) nil ≡ (cons [ 1 ]↑ (cons [ 1 ]↑ nil))
    concat-t2 = refl
    concat-t3 : concat nil (cons [ 1 ]↑ (cons [ 1 ]↑ nil)) ≡ (cons [ 1 ]↑ (cons [ 1 ]↑ nil))
    concat-t3 = refl

    -- BinTrees

    BinTree : Ty → Ty
    BinTree A = ∀' (λ X → X ⇒ (X ⇒ A ⇒ X ⇒ X) ⇒ X)

    leaf : {A : Ty} → Tm (BinTree A)
    leaf = Lam (λ X → lam2 (λ l n → l)) 

    node : {A : Ty} → Tm (BinTree A) → Tm A → Tm (BinTree A) → Tm (BinTree A)
    node {A} t a t' = Lam (λ X → lam2 (λ l n → n ∙ (t • X ∙ l ∙ n) ∙ a ∙ (t' • X ∙ l ∙ n)))

    iteBinTree : {A C : Ty} → Tm C → (Tm C → Tm A → Tm C → Tm C) → Tm (BinTree A) → Tm C
    iteBinTree {A}{C} l n t = t • C ∙ l ∙ lam3 (λ t a t' → n t a t')

    {-
    Times.fst (iteTree' {A} {Times C (BinTree' A)} 
        (λ a → pair (l a) (leaf' a)) 
        (λ {(pair c b) (pair c' j) → pair (n b j c c') (node' b j)})
        t)
    -}

    recBinTree : {A C : Ty} → Tm C → (Tm (BinTree A) → Tm (BinTree A) → Tm C → Tm A → Tm C → Tm C) → Tm (BinTree A) → Tm C
    recBinTree {A}{C} l n t = 
        snd 
        (iteBinTree (leaf , l) 
        (λ lacc a racc → node (fst lacc) a (fst racc) , (n (fst lacc) (fst racc) (snd lacc) a (snd racc))) 
        t)

    flatten : Tm (BinTree Nat) → Tm (List Nat)
    flatten = iteBinTree nil λ lacc a racc → concat (concat lacc (cons a nil)) racc

    tree-t : Tm (BinTree Nat)
    tree-t = 
        node 
        (node (leaf) [ 1 ]↑ (leaf)) 
        [ 2 ]↑
        (node (leaf) [ 3 ]↑ (leaf))

    flatten-t1 : flatten tree-t ≡ cons [ 1 ]↑ (cons [ 2 ]↑ (cons [ 3 ]↑ nil))
    flatten-t1 = refl
    flatten-t2 : flatten leaf ≡ nil
    flatten-t2 = refl

    insert : Tm Nat → Tm (BinTree Nat) → Tm (BinTree Nat)
    insert n = 
        recBinTree 
        (node leaf n leaf) 
        λ l r lacc a racc → 
            ite 
            (node lacc a r) 
            (node l a racc) 
            (lessthen n ∙ a)

    insert-t1 : 
        insert [ 0 ]↑ tree-t ≡ 
        node 
            (node (node leaf [ 0 ]↑ leaf) [ 1 ]↑ (leaf)) 
            [ 2 ]↑
            (node (leaf) [ 3 ]↑ (leaf))
    insert-t1 = refl
    insert-t2 : insert [ 0 ]↑ leaf ≡ node leaf [ 0 ]↑ leaf
    insert-t2 = refl
    insert-t3 : 
        insert [ 4 ]↑ tree-t ≡ 
        node 
            (node (leaf) [ 1 ]↑ (leaf)) 
            [ 2 ]↑
            (node (leaf) [ 3 ]↑ (node leaf [ 4 ]↑ leaf))
    insert-t3 = refl

    treesort : Tm (List Nat) → Tm (List Nat)
    treesort = flatten ∘ (iteList leaf insert)

    {-
    treesort-t1 : treesort (cons [ 1 ]↑ (cons [ 2 ]↑ (cons [ 3 ]↑ (cons [ 4 ]↑ nil)))) ≡ cons [ 1 ]↑ (cons [ 2 ]↑ (cons [ 3 ]↑ (cons [ 4 ]↑ nil)))
    treesort-t1 = refl
    treesort-t2 : treesort nil ≡ nil
    treesort-t2 = refl
    treesort-t3 : treesort (cons [ 0 ]↑ nil) ≡ (cons [ 0 ]↑ nil)
    treesort-t3 = refl
    treesort-t4 : treesort (cons [ 10 ]↑ (cons [ 9 ]↑ (cons [ 8 ]↑ (cons [ 7 ]↑ nil)))) ≡ cons [ 7 ]↑ (cons [ 8 ]↑ (cons [ 9 ]↑ (cons [ 10 ]↑ nil)))
    treesort-t4 = refl
    -}