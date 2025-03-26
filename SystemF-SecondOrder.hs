{-# LANGUAGE TypeFamilies, GADTs, DataKinds #-}

-- This was a try at shallow-embeding second order systemf into haskell with typefamilies
-- It fails at trying to define Times, because the f : Ty -> Ty in the definition of
-- LAM cannot be an arbituary type family (in this case TimesChurch) 
module SystemF_SecondOrder where

data Ty where
    Arrow :: Ty -> Ty -> Ty
    Forall :: (Ty -> Ty) -> Ty

data Tm :: Ty -> * where
    Lam :: forall a b . (Tm a -> Tm b) -> Tm (Arrow a b)
    LAM :: forall (f :: Ty -> Ty) . (forall (x :: Ty) . Tm (f x)) -> Tm (Forall f)

(~>) :: Ty -> Ty -> Ty
(~>) = Arrow

type TimesChurch :: Ty -> Ty -> Ty -> Ty
type family TimesChurch a b x where
    TimesChurch a b x = Arrow (Arrow a (Arrow b x)) x

type Times :: Ty -> Ty -> Ty
type family Times a b where
    Times a b = Forall (TimesChurch a b)

pair :: forall a b . Tm a -> Tm b -> Tm (Times a b)
pair a b = LAM (\x -> Lam (\f -> undefined))

--fst' : {A B : Ty} → Tm (A ×' B) → Tm A
--fst' {A}{B} x = (x • A) ∙ lam (λ a → lam (λ b → a))
--
--snd' : {A B : Ty} → Tm (A ×' B) → Tm B
--snd' {A}{B} x = (x • B) ∙ lam (λ a → lam (λ b → b))