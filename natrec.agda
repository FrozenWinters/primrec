module natrec where

open import Relation.Binary.PropositionalEquality hiding ([_]) public
open import Data.Nat public

Type = Set

-------------------------------------------------------------------
-- Data Structures

infixl 20 _⊹_
data Vec (A : Type) : ℕ → Type where
  ∅ : Vec A zero
  _⊹_ : {n : ℕ} → Vec A n → A → Vec A (suc n)

map : {A B : Type} {n : ℕ} (f : A → B) → Vec A n → Vec B n
map f ∅ = ∅
map f (σ ⊹ t) = map f σ ⊹ f t

data Var : ℕ → Type where
  𝑧𝑣 : {n : ℕ} → Var (suc n)
  𝑠𝑣 : {n : ℕ} → Var n → Var (suc n)

derive : {A : Type} {n : ℕ} → Vec A n → Var n → A
derive (Γ ⊹ t) 𝑧𝑣 = t
derive (Γ ⊹ t) (𝑠𝑣 v) = derive Γ v

Ren : ℕ → ℕ → Type
Ren n m = Vec (Var n) m

W₁Ren : {n m : ℕ} → Ren n m → Ren (suc n) m
W₁Ren σ = map 𝑠𝑣 σ

W₂Ren : {n m : ℕ} → Ren n m → Ren (suc n) (suc m)
W₂Ren σ = W₁Ren σ ⊹ 𝑧𝑣

idRen : {n : ℕ} → Ren n n
idRen {zero} = ∅
idRen {suc n} = W₂Ren idRen

πRen : {n : ℕ} → Ren (suc n) n
πRen = W₁Ren idRen

-------------------------------------------------------------------
-- Syntax

data Program : ℕ → Type where
  Z : {n : ℕ} → Program n
  S : {n : ℕ} → Program n → Program n
  V : {n : ℕ} → Var n → Program n
  R : {n : ℕ} → Program n → Program (suc (suc n)) → Program n → Program n

_[_]Ren : {n m : ℕ} → Program m → Ren n m → Program n
Z [ σ ]Ren = Z
S t [ σ ]Ren = S (t [ σ ]Ren)
V v [ σ ]Ren = V (derive σ v)
R zc sc t [ σ ]Ren =
  R (zc [ σ ]Ren) (sc [ W₂Ren (W₂Ren σ) ]Ren) (t [ σ ]Ren)

W₁Prog : {n : ℕ} → Program n → Program (suc n)
W₁Prog t = t [ πRen ]Ren

Programs : ℕ → ℕ → Type
Programs n m = Vec (Program n) m

W₁Progs : {n m : ℕ} → Programs n m → Programs (suc n) m
W₁Progs σ = map W₁Prog σ

W₂Progs : {n m : ℕ} → Programs n m → Programs (suc n) (suc m)
W₂Progs σ = W₁Progs σ ⊹ V 𝑧𝑣

_[_] : {n m : ℕ} → Program m → Programs n m → Program n
Z [ σ ] = Z
S t [ σ ] = S (t [ σ ])
V v [ σ ] = derive σ v
R zc sc t [ σ ] =
  R (zc [ σ ]) (sc [ W₂Progs (W₂Progs σ) ]) (t [ σ ])

-------------------------------------------------------------------
-- Semantics

Ctx : ℕ → Type
Ctx n = Vec ℕ n

natrec : (zc : ℕ) (sc : ℕ → ℕ → ℕ) (n : ℕ) → ℕ
natrec zc sc zero = zc
natrec zc sc (suc n) = sc n (natrec zc sc n)

eval : {n : ℕ} → Program n → Ctx n → ℕ
eval Z Γ = zero
eval (S t) Γ = suc (eval t Γ)
eval (V v) Γ = derive Γ v
eval (R zc sc t) Γ =
  natrec (eval zc Γ) (λ n rec → eval sc (Γ ⊹ n ⊹ rec)) (eval t Γ)

-------------------------------------------------------------------
-- Programming in this language

-- Conditionals

⟪if⟫ : Program 3
⟪if⟫ = R (V (𝑠𝑣 𝑧𝑣)) (V (𝑠𝑣 (𝑠𝑣 (𝑠𝑣 (𝑠𝑣 𝑧𝑣))))) (V 𝑧𝑣)

if : {n : ℕ} → Program n → Program n → Program n → Program n
if tc fc t = ⟪if⟫ [ ∅ ⊹ tc ⊹ fc ⊹ t ]

⟦if⟧ : ℕ → ℕ → ℕ → ℕ
⟦if⟧ tc fc n = eval ⟪if⟫ (∅ ⊹ tc ⊹ fc ⊹ n)

_ : ⟦if⟧ 5 3 1 ≡ 5
_ = refl

_ : ⟦if⟧ 5 3 0 ≡ 3
_ = refl

-- Arithmetic

num : {n : ℕ} → ℕ → Program n
num zero = Z
num (suc n) = S (num n)

⟦num_⟧ : ℕ → ℕ
⟦num n ⟧ = eval (num n) ∅

_ : ⟦num 20 ⟧ ≡ 20
_ = refl

⟪plus⟫ : Program 2
⟪plus⟫ = R (V (𝑠𝑣 𝑧𝑣)) (S (V 𝑧𝑣)) (V 𝑧𝑣)

plus : {n : ℕ} → Program n → Program n → Program n
plus t s = ⟪plus⟫ [ ∅ ⊹ t ⊹ s ]

⟦plus⟧ : ℕ → ℕ → ℕ
⟦plus⟧ n m = eval ⟪plus⟫ (∅ ⊹ n ⊹ m)

_ : ⟦plus⟧ 7 3 ≡ 10
_ = refl

⟪mult⟫ : Program 2
⟪mult⟫ = R Z (plus (V 𝑧𝑣) (V (𝑠𝑣 (𝑠𝑣 (𝑠𝑣 𝑧𝑣))))) (V 𝑧𝑣)

mult : {n : ℕ} → Program n → Program n → Program n
mult t s = ⟪mult⟫ [ ∅ ⊹ t ⊹ s ]

⟦mult⟧ : ℕ → ℕ → ℕ
⟦mult⟧ n m = eval ⟪mult⟫ (∅ ⊹ n ⊹ m)

_ : ⟦mult⟧ 3 5 ≡ 15
_ = refl

⟪exp⟫ : Program 2
⟪exp⟫ = R (S Z) (mult (V 𝑧𝑣) (V (𝑠𝑣 (𝑠𝑣 (𝑠𝑣 𝑧𝑣))))) (V 𝑧𝑣)

exp : {n : ℕ} → Program n → Program n → Program n
exp t s = ⟪exp⟫ [ ∅ ⊹ t ⊹ s ]

⟦exp⟧ : ℕ → ℕ → ℕ
⟦exp⟧ n m = eval ⟪exp⟫ (∅ ⊹ n ⊹ m)

_ : ⟦exp⟧ 2 10 ≡ 1024
_ = refl

⟪fact⟫ : Program 1
⟪fact⟫ = R (S Z) (mult (V 𝑧𝑣) (S (V (𝑠𝑣 𝑧𝑣)))) (V 𝑧𝑣)

fact : {n : ℕ} → Program n → Program n
fact t = ⟪fact⟫ [ ∅ ⊹ t ]

⟦fact⟧ : ℕ → ℕ
⟦fact⟧ n = eval ⟪fact⟫ (∅ ⊹ n)

_ : ⟦fact⟧ 5 ≡ 120
_ = refl

⟪sub1⟫ : Program 1
⟪sub1⟫ = R Z (V (𝑠𝑣 𝑧𝑣)) (V 𝑧𝑣)

sub1 : {n : ℕ} → Program n → Program n
sub1 t = ⟪sub1⟫ [ ∅ ⊹ t ]

⟦sub1⟧ : ℕ → ℕ
⟦sub1⟧ n = eval ⟪sub1⟫ (∅ ⊹ n)

_ : ⟦sub1⟧ 10 ≡ 9
_ = refl

⟪sub⟫ : Program 2
⟪sub⟫ = R (V (𝑠𝑣 𝑧𝑣)) (sub1 (V 𝑧𝑣)) (V 𝑧𝑣)

sub : {n : ℕ} → Program n → Program n → Program n
sub t s = ⟪sub⟫ [ ∅ ⊹ t ⊹ s ]

⟦sub⟧ : ℕ → ℕ → ℕ
⟦sub⟧ n m = eval ⟪sub⟫ (∅ ⊹ n ⊹ m)

_ : ⟦sub⟧ 10 7 ≡ 3
_ = refl

⟪≤⟫ : Program 2
⟪≤⟫ = sub (S (V 𝑧𝑣)) (V (𝑠𝑣 𝑧𝑣))

≤ : {n : ℕ} → Program n → Program n → Program n
≤ t s = ⟪≤⟫ [ ∅ ⊹ t ⊹ s ]

⟪div⟫ : Program 2
⟪div⟫ =
  R Z (if (S (V 𝑧𝑣)) (V 𝑧𝑣)
    (≤ (mult (S (V 𝑧𝑣)) (V (𝑠𝑣 (𝑠𝑣 𝑧𝑣)))) (V (𝑠𝑣 (𝑠𝑣 (𝑠𝑣 𝑧𝑣))))))
    (V (𝑠𝑣 𝑧𝑣))

div : {n : ℕ} → Program n → Program n → Program n
div t s = ⟪div⟫ [ ∅ ⊹ t ⊹ s ]

⟦div⟧ : ℕ → ℕ → ℕ
⟦div⟧ n m = eval ⟪div⟫ (∅ ⊹ n ⊹ m)

_ : ⟦div⟧ 25 7 ≡ 3
_ = refl

⟪sqrt⟫ : Program 1
⟪sqrt⟫ =
  R Z (if (S (V 𝑧𝑣)) (V 𝑧𝑣)
    (≤ (exp (S (V 𝑧𝑣)) (num 2)) (V (𝑠𝑣 (𝑠𝑣 𝑧𝑣))))) (V 𝑧𝑣)

sqrt : {n : ℕ} → Program n → Program n
sqrt t = ⟪sqrt⟫ [ ∅ ⊹ t ]

⟦sqrt⟧ : ℕ → ℕ
⟦sqrt⟧ n = eval ⟪sqrt⟫ (∅ ⊹ n)

_ : ⟦sqrt⟧ 65 ≡ 8
_ = refl

-- Let's generate all polynomials of a single variable

poly : {n : ℕ} → Vec ℕ n → Program 1
poly ∅ = Z
poly (∅ ⊹ c) = num c
poly (C ⊹ c ⊹ d) = plus (mult (poly (C ⊹ c)) (V 𝑧𝑣)) (num d)

2x²+3x+5 : Program 1
2x²+3x+5 = poly (∅ ⊹ 2 ⊹ 3 ⊹ 5)

⟦2x²+3x+5⟧ : ℕ → ℕ
⟦2x²+3x+5⟧ n = eval 2x²+3x+5 (∅ ⊹ n)

_ : ⟦2x²+3x+5⟧ 5 ≡ 70
_ = refl

-- Pairing and decoding

⟪pair⟫ : Program 2
⟪pair⟫ =
  if (plus (exp (V 𝑧𝑣) (num 2)) (V (𝑠𝑣 𝑧𝑣)))
    (plus (plus (exp (V (𝑠𝑣 𝑧𝑣)) (num 2)) (V (𝑠𝑣 𝑧𝑣))) (V 𝑧𝑣))
    (sub (V 𝑧𝑣) (V (𝑠𝑣 𝑧𝑣)))

pair : {n : ℕ} → Program n → Program n → Program n
pair t s = ⟪pair⟫ [ ∅ ⊹ t ⊹ s ]

⟦pair⟧ : ℕ → ℕ → ℕ
⟦pair⟧ n m = eval ⟪pair⟫ (∅ ⊹ n ⊹ m)

⟪π₁⟫ : Program 1
⟪π₁⟫ =
  if (sub (V 𝑧𝑣) (exp ⟪sqrt⟫ (num 2))) ⟪sqrt⟫
    (sub (plus (exp ⟪sqrt⟫ (num 2)) ⟪sqrt⟫) (V 𝑧𝑣))

π₁ : {n : ℕ} → Program n → Program n
π₁ t = ⟪π₁⟫ [ ∅ ⊹ t ]

⟦π₁⟧ : ℕ → ℕ
⟦π₁⟧ n = eval ⟪π₁⟫ (∅ ⊹ n)

⟪π₂⟫ : Program 1
⟪π₂⟫ =
  if ⟪sqrt⟫ (sub (sub (V 𝑧𝑣) (exp ⟪sqrt⟫ (num 2))) ⟪sqrt⟫)
    (sub (plus (exp ⟪sqrt⟫ (num 2)) ⟪sqrt⟫) (V 𝑧𝑣))

π₂ : {n : ℕ} → Program n → Program n
π₂ t = ⟪π₂⟫ [ ∅ ⊹ t ]

⟦π₂⟧ : ℕ → ℕ
⟦π₂⟧ n = eval ⟪π₂⟫ (∅ ⊹ n)

-- Fibonacci starting at 1 (very slow)

⟪fib⟫ : Program 1
⟪fib⟫ =
  π₂ (R (pair (num 0) (num 1))
    (pair (π₂ (V 𝑧𝑣)) (plus (π₂ (V 𝑧𝑣)) (π₁ (V 𝑧𝑣)))) (V 𝑧𝑣))

fib : {n : ℕ} → Program n → Program n
fib t = ⟪fib⟫ [ ∅ ⊹ t ]

⟦fib⟧ : ℕ → ℕ
⟦fib⟧ n = eval ⟪fib⟫ (∅ ⊹ n)
