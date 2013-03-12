{-# OPTIONS --termination-depth=10 #-}
module PLT where

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ 

_+_ : ℕ → ℕ → ℕ
zero + a = a
succ a + b = succ (a + b)

_*_ : ℕ → ℕ → ℕ
zero * b = zero
succ a * b = b + (a * b)

data Op : Set where
  PLUS MUL : Op

data Arith : Set where
  C_ : ℕ → Arith
  B : Op → Arith → Arith → Arith

do : Op → ℕ → ℕ → ℕ
do PLUS = _+_
do MUL = _*_

eval : Arith → ℕ
eval (C x) = x
eval (B x r r₁) = do x (eval r) (eval r₁)

data _✴ {A : Set} (R : A → A → Set) : A → A → Set where
  stop : ∀ {a} → (R ✴) a a
  step : ∀ {a b c} → R a b → (R ✴) b c → (R ✴) a c

data _a→a_ : Arith → Arith → Set where
  LL' : ∀ {l₁ l₂ r op} 
    → l₁ a→a l₂ 
    → B op l₁ r a→a B op l₂ r
  RR' : ∀ {l r₁ r₂ op} 
    → r₁ a→a r₂
    → B op l r₁ a→a B op l r₂
  FF' : ∀ {op n₁ n₂} 
    → B op (C n₁) (C n₂) a→a C (do op n₁ n₂)

data _a→a'_ : Arith → Arith → Set where
  NN : ∀ {r} → r a→a' r
--  FF : ∀ {op x₁ x₂} 
--    → (B op (C x₁) (C x₂)) a→a' C (do op x₁ x₂)
  RL : ∀ {l₁ l₂ r₁ r₂ op} 
    → l₁ a→a' C l₂
    → r₁ a→a' C r₂
    → (B op l₁ r₁) a→a' C (do op l₂ r₂)

a→a'-lem : ∀ r n → r a→a' (C n) → eval r ≡ n
a→a'-lem (C .n) n NN = refl
a→a'-lem (B x r r₁) .(do x l₂ r₂) (RL {.r} {l₂} {.r₁} {r₂} p p₁) with eval r | a→a'-lem r l₂ p
a→a'-lem (B x r r₁) .(do x l₂ r₂) (RL {.r} {l₂} {.r₁} {r₂} p p₁) | .l₂ | refl with eval r₁ | a→a'-lem r₁ r₂ p₁
a→a'-lem (B x r r₁) .(do x l₂ r₂) (RL {.r} {l₂} {.r₁} {r₂} p p₁) | .l₂ | refl | .r₂ | refl = refl

data _a→a''_ : Arith → Arith → Set where
  NN : ∀ {r} → r a→a'' r
  T : ∀ {r₁ r₂ r₃}
    → r₁ a→a'' r₂ 
    → r₂ a→a'' r₃
    → r₁ a→a'' r₃
  
--  FF : ∀ {op x₁ x₂} 
--    → (B op (C x₁) (C x₂)) a→a' C (do op x₁ x₂)

  

{- Goal: do op n₁ n₂ ≡ n
pp2 : n₂ ≡ n₂      pp1 : n₁ ≡ n₁
n₂  : ℕ     n₁  : ℕ
p   : B op r₁ r₂ a→a' (C n)
r₂  : Arith     r₁  : Arith
op  : Op     n   : ℕ
-} 
-- if_then_else_ : {A : Set} → Bool → A → A → A
-- if True then a else b = a
-- if False then a else b = b

lemma-a→a-sound : ∀ r n → ((_a→a_ ✴) r (C n)) → eval r ≡ n
lemma-a→a-sound .(C n) n stop = refl
lemma-a→a-sound (C x) n (step () p)
lemma-a→a-sound (B x r r₁) n (step {.(B x r r₁)} {b} {.(C n)} x₁ p) with lemma-a→a-sound b n p
lemma-a→a-sound (B x r r₁) .(eval b) (step {.(B x r r₁)} {b} x₁ p) | refl = {!!}

data _a→ℕ_ : Arith → ℕ → Set where
  CC : ∀ {n} 
--    → (C n a→ℕ n)
    → (_a→ℕ_ (C n) n)
  OPOP : ∀ {op r₁ r₂ n₁ n₂} 
    → r₁ a→ℕ n₁ 
    → r₂ a→ℕ n₂ 
    → B op r₁ r₂ a→ℕ (do op n₁ n₂)

eval-lem : ∀ r → r a→ℕ eval r
eval-lem (C x) = CC
eval-lem (B x r r₁) = 
  OPOP (eval-lem r) (eval-lem r₁)

-- Soundness (непротиворечивость?, правильность?)
eval-lem' : (r : Arith) → (n : ℕ) → r a→ℕ n → n ≡ eval r
eval-lem' .(C n) n CC = refl
eval-lem' .(B op r₁ r₂) .(do op n₁ n₂) (OPOP {op} {r₁} {r₂} {n₁} {n₂} ra→ℕn ra→ℕn₁) with eval-lem' r₁ n₁ ra→ℕn | eval-lem' r₂ n₂ ra→ℕn₁
eval-lem' .(B op r₁ r₂) .(do op (eval r₁) (eval r₂)) (OPOP {op} {r₁} {r₂} ra→ℕn ra→ℕn₁) 
  | refl | refl = refl

-- Completeness (полнота)
eval-lem2 : ∀ r n → eval r ≡ n → r a→ℕ n
eval-lem2 (C x) .x refl = CC
eval-lem2 (B x r r₁) .(do x (eval r) (eval r₁)) refl with eval-lem2 r (eval r) refl | eval-lem2 r₁ (eval r₁) refl
... | p | p2 = OPOP p p2

{-

eval' : Arith → ℕ
eval' (C x) = x
eval' (B x (C x₁) r₁) = do x x₁ (eval' r₁)
eval' (B x (B x₁ r r₁) r₂) with eval' (B x₁ r r₁)
-- ... | p = eval' (B x (C p) r₂)
... | p = do x p (eval' r₂)
-- eval' (B x (B x₁ r r₁) r₂) = eval' (B x (C eval' (B x₁ r r₁)) r₂)

data _→a_ : Arith → Arith → Set where
  FF : ∀ {op x₁ x₂} → (B op (C x₁) (C x₂)) →a C (do op x₁ x₂)
  RR : ∀ {r₂ r₃ x₁ op} → r₂ →a r₃ → (B op (C x₁) r₂) →a (B op (C x₁) r₃)
  LL : ∀ {r₁ r₂ r₃ op} → r₁ →a r₂ → (B op r₁ r₃) →a (B op r₂ r₃)
  
-}
