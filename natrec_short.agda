{-# OPTIONS --cubical #-}

module natrec_short where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public
open import Cubical.Core.Everything public
open import Cubical.Foundations.Everything public

open import Cubical.Data.Nat

data Var : ℕ → Type where
  𝑧𝑣 : {n : ℕ} → Var (suc n)
  𝑠𝑣 : {n : ℕ} → Var n → Var (suc n)

data Program : ℕ → Type where
  Z : {n : ℕ} → Program n
  S : {n : ℕ} → Program n → Program n
  V : {n : ℕ} → Var n → Program n
  R : {n : ℕ} → Program n → Program (suc (suc n)) → Program n → Program n

infixl 20 _⊹_
data Ctx : ℕ → Type where
  ∅ : Ctx zero
  _⊹_ : {n : ℕ} → Ctx n → ℕ → Ctx (suc n)

derive : {n : ℕ} → Ctx n → Var n → ℕ
derive (Γ ⊹ n) 𝑧𝑣 = n
derive (Γ ⊹ n) (𝑠𝑣 v) = derive Γ v

natrec : (zc : ℕ) (sc : ℕ → ℕ → ℕ) (n : ℕ) → ℕ
natrec zc sc zero = zc
natrec zc sc (suc n) = sc n (natrec zc sc n)

eval : {n : ℕ} → Program n → Ctx n → ℕ
eval Z Γ = zero
eval (S t) Γ = suc (eval t Γ)
eval (V v) Γ = derive Γ v
eval (R zc sc t) Γ = natrec (eval zc Γ) (λ n rec → eval sc (Γ ⊹ n ⊹ rec)) (eval t Γ)
