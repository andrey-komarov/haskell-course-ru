{-# OPTIONS --termination-depth=10 #-}
module PLT_nohole where

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

a→a-lem : ∀ r₁ r₂
  → r₁ a→a r₂
  → eval r₁ ≡ eval r₂
a→a-lem .(B op l₁ r) .(B op l₂ r) (LL' {l₁} {l₂} {r} {op} p) with eval l₁ | eval l₂ | a→a-lem l₁ l₂ p 
a→a-lem .(B op l₁ r) .(B op l₂ r) (LL' {l₁} {l₂} {r} {op} p) | .n₂ | n₂ | refl = refl
a→a-lem .(B op l r₁) .(B op l r₂) (RR' {l} {r₁} {r₂} {op} p) with eval r₁ | eval r₂ | a→a-lem r₁ r₂ p 
a→a-lem .(B op l r₁) .(B op l r₂) (RR' {l} {r₁} {r₂} {op} p) | .n₂ | n₂ | refl = refl
a→a-lem .(B op (C n₁) (C n₂)) .(C do op n₁ n₂) (FF' {op} {n₁} {n₂}) = refl

lemma-a→a-sound : ∀ r n → ((_a→a_ ✴) r (C n)) → eval r ≡ n
lemma-a→a-sound .(C n) n stop = refl
lemma-a→a-sound (C x) n (step () p)
lemma-a→a-sound (B x r r₁) n (step {.(B x r r₁)} {b} {.(C n)} x₁ p) with lemma-a→a-sound b n p
lemma-a→a-sound (B x r r₁) .(eval b) (step {.(B x r r₁)} {b} x₁ p) | refl = a→a-lem (B x r r₁) b x₁

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

tmp-lem : ∀ {l r l₂ r₂ n₁ n₂ op₁ op₂}
  → l₂ a→ℕ n₁ 
  → r₂ a→ℕ n₂
  → B op₁ l r a→a B op₂ l₂ r₂
  → B op₁ l r a→ℕ do op₂ n₁ n₂
tmp-lem CC CC (LL' FF') = OPOP (OPOP CC CC) CC
tmp-lem CC CC (RR' FF') = OPOP CC (OPOP CC CC)
tmp-lem CC (OPOP p2 p3) (LL' FF') = OPOP (OPOP CC CC) (OPOP p2 p3)
tmp-lem CC (OPOP p2 p3) (RR' (LL' x)) = OPOP CC (tmp-lem p2 p3 (LL' x))
tmp-lem CC (OPOP p2 p3) (RR' (RR' x)) = OPOP CC (tmp-lem p2 p3 (RR' x))
tmp-lem (OPOP p1 p2) CC (LL' (LL' x)) = OPOP (tmp-lem p1 p2 (LL' x)) CC
tmp-lem (OPOP p1 p2) CC (LL' (RR' x)) = OPOP (tmp-lem p1 p2 (RR' x)) CC
tmp-lem (OPOP p1 p2) CC (RR' FF') = OPOP (OPOP p1 p2) (OPOP CC CC)
tmp-lem (OPOP p1 p2) (OPOP p3 p4) (LL' (LL' x)) = OPOP (tmp-lem p1 p2 (LL' x)) (OPOP p3 p4)
tmp-lem (OPOP p1 p2) (OPOP p3 p4) (LL' (RR' x)) = OPOP (tmp-lem p1 p2 (RR' x)) (OPOP p3 p4)
tmp-lem (OPOP p1 p2) (OPOP p3 p4) (RR' (LL' x)) = OPOP (OPOP p1 p2) (tmp-lem p3 p4 (LL' x))
tmp-lem (OPOP p1 p2) (OPOP p3 p4) (RR' (RR' x)) = OPOP (OPOP p1 p2) (tmp-lem p3 p4 (RR' x))

a→✴a-is-a→ℕ : ∀ r n 
  → (_a→a_ ✴) r (C n) 
  → r a→ℕ n
a→✴a-is-a→ℕ .(C n) n stop = CC
a→✴a-is-a→ℕ (C x) n (step () bc)
a→✴a-is-a→ℕ (B x r₁ r₂) n (step {b = b} ab bc) with a→✴a-is-a→ℕ b n bc 
a→✴a-is-a→ℕ (B x .(C n₁) .(C n₂)) .(do x n₁ n₂) (step (FF' {.x} {n₁} {n₂}) bc) | CC = OPOP CC CC
a→✴a-is-a→ℕ (B x r₃ r₄) .(do op n₁ n₂) (step ab bc) | OPOP {op} {r₁} {r₂} {n₁} {n₂} pp pp₁ = tmp-lem pp pp₁ ab

tmp-lem2 : ∀ {l r n op}
  → (_a→a_ ✴) l (C n)
  → l a→ℕ n
  → (_a→a_ ✴) (B op l r) (B op (C n) r)
tmp-lem2 stop CC = stop
tmp-lem2 (step x p1) CC = stop
tmp-lem2 {.(B op₁ r₁ r₂)}{bb}{.(do op₁ n₁ n₂)}{_}(step {b = b} x p1) (OPOP {op₁}{r₁}{r₂}{n₁}{n₂} p2 p3) with tmp-lem2 {b}{r₂}{do op₁ n₁ n₂}{op₁} p1 (a→✴a-is-a→ℕ b (do op₁ n₁ n₂) p1)
tmp-lem2 (step op r₁) (OPOP p2 p3) | stop = step (LL' op) stop
tmp-lem2 {.(B op₁ r₁ r₂)}{r = r}{op = op} (step {b = b₁} ab bc) (OPOP {op₁}{r₁}{r₂}{n₁}{n₂} p2 p3) | step {b = b} x pp = step (LL' ab) (tmp-lem2 bc (a→✴a-is-a→ℕ b₁ (do op₁ n₁ n₂) bc))

tmp-lem3 : ∀ l r n op
  → (_a→a_ ✴) r (C n)
  → r a→ℕ n
  → (_a→a_ ✴) (B op l r) (B op l (C n))
tmp-lem3 l .(C n) n op stop CC = stop
tmp-lem3 l .(C n) n op (step x p1) CC = stop
tmp-lem3 l .(B op₁ r₁ r₂) .(do op₁ n₁ n₂) op (step {b = b} x p1) (OPOP {op₁} {r₁} {r₂} {n₁} {n₂} p2 p3) with tmp-lem3 r₂ b (do op₁ n₁ n₂) op₁ p1 (a→✴a-is-a→ℕ b (do op₁ n₁ n₂) p1)
tmp-lem3 l .(B op₁ r₁ r₂) .(do op₁ n₁ n₂) op (step op₁ r₁) (OPOP {r₂} {x} {n₁} {n₂} p2 p3) | stop = step (RR' op₁) stop
tmp-lem3 l .(B ab bc r₂) .(do ab n₁ n₂) op (step {b = b} ab bc) (OPOP {r₂} {x} {n₁} {n₂} {n₃} p2 p3) | step x₁ pp = step (RR' ab) (tmp-lem3 l b (do r₂ n₂ n₃) op bc (a→✴a-is-a→ℕ b (do r₂ n₂ n₃) bc))

tmp-lem4 : ∀ {a b c}
  → (_a→a_ ✴) a b
  → (_a→a_ ✴) b c
  → (_a→a_ ✴) a c
tmp-lem4 stop stop = stop
tmp-lem4 stop (step x p2) = step x p2
tmp-lem4 (step x p1) stop = step x p1
tmp-lem4 (step x p1) (step x₁ p2) = step x (tmp-lem4 p1 (step x₁ p2))

tmp-lem5 : ∀ {l n₁ n₂ op}
  → (_a→a_ ✴) l (B op (C n₁) (C n₂))
  → (_a→a_ ✴) l (C do op n₁ n₂)
tmp-lem5 stop = step FF' stop
tmp-lem5 (step x p) = step x (tmp-lem5 p)

a→ℕ-is-a→a : ∀ r n
  → r a→ℕ n
  → (_a→a_ ✴) r (C n)
a→ℕ-is-a→a .(C n) n CC = stop
a→ℕ-is-a→a .(B op r₁ r₂) .(do op n₁ n₂) (OPOP {op} {r₁} {r₂} {n₁} {n₂} p p₁) with a→ℕ-is-a→a r₁ n₁ p | a→ℕ-is-a→a r₂ n₂ p₁ 
... | pp1 | pp2 with tmp-lem3 r₁ r₂ n₂ op pp2 p₁
... | pp3 with tmp-lem2 {r₁}{C n₂}{n₁}{op} pp1 p
... | pp4 with tmp-lem4 pp3 pp4
... | pp5 = tmp-lem5 pp5

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
