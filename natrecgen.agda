{-# OPTIONS --guardedness #-}

module natrecgen where

open import natrec

open import Data.String public
open import Agda.Builtin.String using () renaming (primShowNat to showNat)
open import Data.Nat

open import IO using (putStr ; Main ; run; IO; _>>_; return)
open import Data.Unit.Polymorphic.Base

infixl 20 _⊹_
data List (A : Type) : Type where
  ∅ : List A
  _⊹_ : List A → A → List A

fold : {A B : Type} → (B → A → B) → B → List A → B
fold f z ∅ = z
fold f z (σ ⊹ t) = f (fold f z σ) t

map' : {A B : Type} (f : A → B) → List A → List B
map' f ∅ = ∅
map' f (σ ⊹ t) = map' f σ ⊹ f t

_++'_ : {A : Type} → List A → List A → List A
σ ++' ∅ = σ
σ ++' (τ ⊹ t) = (σ ++' τ) ⊹ t

gen : {A : Type} → (ℕ → A) → ℕ → List A
gen f zero = ∅
gen f (suc n) = gen f n ⊹ f n

-----------------
-- Pretty printing

var-to-nat : {n : ℕ} → Var n → ℕ
var-to-nat 𝑧𝑣 = zero
var-to-nat (𝑠𝑣 v) = suc (var-to-nat v)

print-var : {n : ℕ} → Var n → String
print-var v = showNat (var-to-nat v)

print-prog : {n : ℕ} → Program n → String
print-prog Z = "Z"
print-prog (S t) = "S " ++ print-prog t
print-prog (V v) = print-var v
print-prog (R zc sc t) =
  "R " ++ print-prog zc ++ " " ++ print-prog sc ++ " " ++ print-prog t

get-values : Program 1 → ℕ → List ℕ
get-values t = gen (λ k → eval t (∅ ⊹ k))

format-values : List ℕ → String
format-values σ = fold (λ s n → s ++ showNat n ++ ",") "" σ

format-prog : Program 1 → String
format-prog t =
  format-values (get-values t 20) ++ print-prog t ++ " X" ++ "\n"

fold-string : List String → String
fold-string σ = fold _++_ "" σ

-----------------
-- Fast poly evaluation

eval-poly : {n : ℕ} → Vec ℕ n → ℕ → ℕ
eval-poly ∅ n = 0
eval-poly (C ⊹ k) n = (eval-poly C n) * n + k

get-poly : {n : ℕ} → Vec ℕ n → String
get-poly C = format-values (gen (eval-poly C) 20) ++ print-prog (poly C) ++ " X" ++ "\n"

-----------------
-- Data Sets

numerals : ℕ → String
numerals n = fold-string (gen (λ k → format-prog (num k)) n)

{-add-coef : (m : ℕ) {k : ℕ} → Vec ℕ k → IO {a = Agda.Primitive.lzero} ⊤ → IO {a = Agda.Primitive.lzero} ⊤
add-coef zero C s = s >> putStr (get-poly C)
add-coef (suc m) C s = add-coef m C s >> putStr (get-poly (C ⊹ m))-}

add-coef : (n m k : ℕ) {l : ℕ} → Vec ℕ l → IO {a = Agda.Primitive.lzero} ⊤ → IO {a = Agda.Primitive.lzero} ⊤
add-coef zero m k C s = s >> putStr (get-poly C)
add-coef (suc n) zero k C s = add-coef n k k C s
add-coef (suc n) (suc m) k C s = add-coef (suc n) m k C (add-coef n k k (C ⊹ m) s)

polys : (n m k : ℕ) → IO {a = Agda.Primitive.lzero} ⊤
polys n zero k = return tt
polys n (suc m) k = add-coef n k k (∅ ⊹ suc m) (polys n m k)

{-coefs : (n m : ℕ) {k : ℕ} → Vec ℕ k → IO {a = Agda.Primitive.lzero} ⊤ → IO {a = Agda.Primitive.lzero} ⊤
coefs n m C s = s >> putStr (get-poly C) >> {!!}-}

{-add-num : {n : ℕ} → ℕ → List (Vec ℕ n) → List (Vec ℕ (suc n))
add-num n σ = map' (λ C → C ⊹ n) σ

add-nums : {n : ℕ} → ℕ → List (Vec ℕ n) → List (Vec ℕ (suc n))
add-nums n σ = fold _++'_ ∅ (gen (λ k → add-num k σ) n)

add-nums' : {n : ℕ} → ℕ → List (Vec ℕ n) → List (Vec ℕ (suc n))
add-nums' n σ = fold _++'_ ∅ (gen (λ k → add-num (suc k) σ) n)

coefs : (n m : ℕ) → List (Vec ℕ (suc n)) → IO ⊤ → IO ⊤
coefs n m -}

{-coefs : (n m : ℕ) → List (Vec ℕ (suc n))
coefs zero m = add-nums' m (∅ ⊹ ∅)
coefs (suc n) m = add-nums (suc m) (coefs n m)

polys : (n m : ℕ) → String
polys n m =
  fold-string (fold _++'_ ∅ (gen (λ k → map' (λ C → get-poly C) (coefs k m)) n))-}

-----------------
-- Line to run

main : Main
main = run (polys 6 7 7)
