data _+_ (A B : Set) : Set where
  inl : A → A + B
  inr : B → A + B

+ind : {A B : Set} (P : A + B → Set) → ((a : A) → P (inl a)) → ((b : B) → P (inr b)) → (x : A + B) → P x
+ind P l r (inl a) = l a
+ind P l r (inr b) = r b

------------------------------

data ⊥ : Set where

abort : {A : Set} → ⊥ → A
abort ()

¬ : Set → Set
¬ P = (P → ⊥)

------------------------------

data _＝_ {A : Set} (a : A) : A → Set where
  refl : a ＝ a

isProp : (A : Set) → Set
isProp A = (a b : A) → a ＝ b

------------------------------

code : {A B : Set} → A + B → A + B → Set
code (inl a1) (inl a2) = a1 ＝ a2
code (inl a) (inr b) = ⊥
code (inr b) (inl a) = ⊥
code (inr b1) (inr b2) = b1 ＝ b2

rcode : {A B : Set} (x : A + B) → code x x
rcode (inl a) = refl
rcode (inr b) = refl

encode : {A B : Set} {x y : A + B} → (x ＝ y) → code x y
encode {x = x} refl = rcode x

------------------------------

data ♭ (@♭ A : Set) : Set where
  in♭ : (@♭ _ : A) → ♭ A

ε : (@♭ A : Set) → ♭ A → A
ε A (in♭ a) = a

------------------------------

record isDisc (@♭ A : Set) : Set where
  field
    sect : A → ♭ A
    issect : (x : A) → ε A (sect x) ＝ x
open isDisc

------------------------------

postulate
  R : Set
  _<_ : R → R → Set
  <p : {x y : R} → isProp (x < y)
  <> : {x y : R} → x < y → y < x → ⊥

postulate
  LEM : (@♭ P : Set) (@♭ _ : isProp P ) → P + ¬ P
  R♭ : (@♭ A : Set) (@♭ _ : isDisc A) (f : R → A) → A
  R♭' : (@♭ A : Set) (@♭ Ad : isDisc A) (f : R → A) (x : R) → f x ＝ R♭ A Ad f
  AMP : (x y : R) → ¬ (x ＝ y) → (x < y) + (y < x)

DNE : (@♭ P : Set) (@♭ _ : isProp P) → ¬ (¬ P) → P
DNE P pP = +ind (λ _ → ¬ (¬ P) → P) (λ p _ → p) (λ np nnp → abort (nnp np)) (LEM P pP)

------------------------------

record ⊤ : Set where
  constructor ⋆

bool : Set
bool = ⊤ + ⊤

true : bool
true = inl ⋆

false : bool
false = inr ⋆

false≠true : ¬ (false ＝ true)
false≠true p = encode p

true≠false : ¬ (true ＝ false)
true≠false p = encode p

bd : isDisc bool
sect bd = +ind (λ _ → ♭ bool) (λ _ → in♭ true) (λ _ → in♭ false)
issect bd = +ind (λ x → ε bool (+ind (λ _ → ♭ bool) (λ _ → in♭ true) (λ _ → in♭ false) x) ＝ x)
  (λ _ → refl) λ _ → refl

------------------------------

Rconn : (U V : R → Set) (_ : (x : R) → isProp (U x)) (_ : (x : R) → isProp (V x))
  (_ : (x : R) → U x + V x) (_ : (x : R) → U x → V x → ⊥)
  → ((x : R) → U x) + ((x : R) → V x)
Rconn U V Up Vp union disjoint =
  +ind (λ y → ((x : R) → g x (union x) ＝ y) → ((x : R) → U x) + ((x : R) → V x))
       (λ _ fx → inl λ x → +ind (λ y → g x y ＝ true → U x) (λ u _ → u) (λ _ cc → abort (false≠true cc)) (union x) (fx x))
       (λ _ fx → inr λ x → +ind (λ y → g x y ＝ false → V x) (λ _ cc → abort (true≠false cc)) (λ v _ → v) (union x) (fx x))
       (R♭ bool bd (λ x → g x (union x))) (R♭' bool bd (λ x → g x (union x)))
  where g : (x : R) → U x + V x → bool
        g _ (inl _) = true
        g _ (inr _) = false

postulate
  ∃ : (A : Set) (B : A → Set) → Set
  ∃I : {A : Set} {B : A → Set} (a : A) (b : B a) → ∃ A B
  ∃p : {A : Set} {B : A → Set} → isProp (∃ A B)

------------------------------

IVT : (@♭ f : R → R) (@♭ c : R) (a b : R) (_ : f a < c) (_ : c < f b) → ∃ R (λ x → f x ＝ c)
IVT f c a b fa fb = DNE (∃ R (λ x → f x ＝ c)) ∃p
  (λ H → let U = λ x → f x < c in
          let V = λ x → c < f x in
          +ind (λ _ → ⊥) (λ u → <> (u b) fb) (λ v → <> (v a) fa)
          (Rconn U V (λ x → <p) (λ x → <p) (λ x → AMP (f x) c (λ p → H (∃I x p))) (λ x → <>)))
