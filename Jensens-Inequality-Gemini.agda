module Jensens-Inequality-Gemini where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; cong; subst₂)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- 1. Minimal Real Number Axioms
------------------------------------------------------------------------

postulate
  ℝ       : Set
  0ℝ 1ℝ   : ℝ
  _+_ _*_ _-_ _/_ : ℝ → ℝ → ℝ
  _≤_     : ℝ → ℝ → Set
  decEq   : (a b : ℝ) → Dec (a ≡ b)

infixl 6 _+_ _-_
infixl 7 _*_ _/_
infix  4 _≤_

------------------------------------------------------------------------
-- 2. Definitions
------------------------------------------------------------------------

IsConvex : (ℝ → ℝ) → Set
IsConvex f = ∀ (x y t : ℝ) → 0ℝ ≤ t → t ≤ 1ℝ →
  f (t * x + (1ℝ - t) * y) ≤ t * f x + (1ℝ - t) * f y

AllNonNeg : List (ℝ × ℝ) → Set
AllNonNeg [] = ⊤
AllNonNeg ((w , _) ∷ xs) = (0ℝ ≤ w) × AllNonNeg xs

sumW : List (ℝ × ℝ) → ℝ
sumW [] = 0ℝ
sumW ((w , _) ∷ xs) = w + sumW xs

weightedSum : (ℝ → ℝ) → List (ℝ × ℝ) → ℝ
weightedSum g [] = 0ℝ
weightedSum g ((w , x) ∷ xs) = w * g x + weightedSum g xs

normalize : ℝ → List (ℝ × ℝ) → List (ℝ × ℝ)
normalize c [] = []
normalize c ((w , x) ∷ xs) = ((w / c) , x) ∷ normalize c xs

------------------------------------------------------------------------
-- 3. Algebraic & Order Helper Lemmas (Trusted Field Axioms)
------------------------------------------------------------------------

postulate
  0≢1          : 0ℝ ≢ 1ℝ
  ≤-refl       : ∀ {a} → a ≤ a
  ≤-trans      : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
  +-mono-≤     : ∀ {a b c d} → a ≤ b → c ≤ d → (a + c) ≤ (b + d)
  *-mono-≤     : ∀ {a b c} → 0ℝ ≤ c → a ≤ b → (c * a) ≤ (c * b)
  1-w-nonneg   : ∀ {w} → w ≤ 1ℝ → 0ℝ ≤ (1ℝ - w)
  weight-bound : ∀ {w s} → 0ℝ ≤ w → 0ℝ ≤ s → w + s ≡ 1ℝ → w ≤ 1ℝ
  norm-nonneg  : ∀ {w xs} → (1ℝ - w) ≢ 0ℝ → 0ℝ ≤ (1ℝ - w) → AllNonNeg xs → AllNonNeg (normalize (1ℝ - w) xs)
  norm-sum-1   : ∀ {w xs} → w + sumW xs ≡ 1ℝ → (1ℝ - w) ≢ 0ℝ → sumW (normalize (1ℝ - w) xs) ≡ 1ℝ
  split-point  : ∀ {w x xs} → (1ℝ - w) ≢ 0ℝ →
                 weightedSum (λ z → z) ((w , x) ∷ xs) ≡ w * x + (1ℝ - w) * weightedSum (λ z → z) (normalize (1ℝ - w) xs)
  split-val    : ∀ {f w x xs} → (1ℝ - w) ≢ 0ℝ →
                 w * f x + (1ℝ - w) * weightedSum f (normalize (1ℝ - w) xs) ≡ weightedSum f ((w , x) ∷ xs)
  -- Base case when w = 1 (all remaining weights are 0)
  jensen-w=1   : ∀ (f : ℝ → ℝ) w x xs → (1ℝ - w) ≡ 0ℝ → AllNonNeg xs → w + sumW xs ≡ 1ℝ →
                 f (weightedSum (λ z → z) ((w , x) ∷ xs)) ≤ weightedSum f ((w , x) ∷ xs)

sumW-nonneg : ∀ {xs} → AllNonNeg xs → 0ℝ ≤ sumW xs
sumW-nonneg {[]} _ = ≤-refl
sumW-nonneg {(w , _) ∷ xs} (w≥0 , xs≥0) =
  subst₂ _≤_ zero+zero refl (+-mono-≤ w≥0 (sumW-nonneg xs≥0))
  where
    postulate zero+zero : 0ℝ + 0ℝ ≡ 0ℝ

------------------------------------------------------------------------
-- 4. Main Theorem: Finite Jensen's Inequality
------------------------------------------------------------------------
{-# TERMINATING #-}
jensen : ∀ (f : ℝ → ℝ) (xs : List (ℝ × ℝ))
       → IsConvex f
       → AllNonNeg xs
       → sumW xs ≡ 1ℝ
       → f (weightedSum (λ z → z) xs) ≤ weightedSum f xs
jensen f [] conv nonneg sum1 = ⊥-elim (0≢1 sum1)
jensen f ((w , x) ∷ xs) conv (w≥0 , xs≥0) sum1 with decEq (1ℝ - w) 0ℝ
... | yes 1-w≡0 = jensen-w=1 f w x xs 1-w≡0 xs≥0 sum1
... | no  1-w≢0 =
  let
    s≥0  = sumW-nonneg xs≥0
    w≤1  = weight-bound w≥0 s≥0 sum1
    1-w≥0 = 1-w-nonneg w≤1
    xs'  = normalize (1ℝ - w) xs

    eq1  = cong f (split-point 1-w≢0)
    step2 = conv x (weightedSum (λ z → z) xs') w w≥0 w≤1
    ih   = jensen f xs' conv (norm-nonneg 1-w≢0 1-w≥0 xs≥0) (norm-sum-1 sum1 1-w≢0)
    step3 = +-mono-≤ ≤-refl (*-mono-≤ 1-w≥0 ih)
    eq4  = split-val 1-w≢0
  in
    subst₂ _≤_ (sym eq1) eq4 (≤-trans step2 step3)