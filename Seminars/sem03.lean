/-!
# Seminar 3
Quantifiers, tactics
-/

/- Universal Quantifier -/
variable (α : Type) (P Q : α → Prop)

#check ∀ (x : α), P x
#check ∀ x : α, P x
#check ∀ x, P x
#check ∀ x y : α, P x ∧ Q y
#check ∀ x : α, ∀ y : α, P x ∧ Q y
#check (x : α) → P x

example : (∀ x : α, P x) ∨ (∀ x : α, Q x) → ∀ x : α, P x ∨ Q x  :=
  λ h x ↦ Or.elim h (λ hP ↦ Or.inl (hP x)) (λ hQ ↦ Or.inr (hQ x))

example : (∀ (x : α), P x ∧ Q x) ↔ (∀ x : α, P x) ∧ (∀ x : α, Q x) :=
⟨
  λ h ↦ ⟨λ x ↦ (h x).left, λ x ↦ (h x).right⟩,
  λ ⟨h1, h2⟩  ↦ (λ x ↦ ⟨h1 x, h2 x⟩ )
⟩

/- Existential Quantifier -/

#check ∃ (x : α), P x
#check Exists P
#print Exists -- ?
#check Exists.intro

/- Why not this?
structure Exists' {α : Type} {P : α → Prop} : Prop where
  intro ::
  a : α
  b : P a
-/

example : (∃ x : α, P x ∧ Q x) → (∃ x : α, P x) ∧ (∃ x : α, Q x) :=
  λ ⟨x, hp, hq⟩ ↦ ⟨⟨x, hp⟩, ⟨x, hq⟩⟩

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) :=
⟨
  λ ⟨ x, h ⟩   ↦ (Or.elim h
              (λ hp ↦ (Or.inl ⟨x, hp⟩) )
              (λ hq ↦ (Or.inr ⟨x, hq⟩) )
              ),
  λ porq ↦ (Or.elim porq (λ ⟨ x,  p ⟩  ↦ ⟨x, Or.inl p⟩ ) (λ ⟨ x, q ⟩  ↦ ⟨ x, Or.inr q ⟩ ))
⟩

theorem not_iff_sf: ∀(P : Prop), ¬ (P ↔ ¬ P) :=
  λ P ↦
    λ h ↦
    have hnP : ¬ P := λ hp ↦ (h.mp hp) hp

  hnP (h.mpr hnP)

/- 2^α ≃ α → Prop (at least classicaly) -/
theorem cantor (f : α → (α → Prop)) :
 ¬∀ S : α → Prop, ∃ x : α, ∀ y : α, S y ↔ f x y :=
λ s ↦
  let ⟨ x, hx ⟩ := s (λ y ↦  ¬ f y y)
  not_iff_sf (f x x) (hx x).symm

-- have x := 2;
-- λ hS x hy
--  False.elim sorry;

/- Classical logic -/

theorem not_exists_not : (¬ ∃ x : α, ¬ P x) → ∀ x : α, P x :=
  λ h x ↦ Or.elim (Classical.em (P x)) id (λ hn ↦ False.elim (h ⟨x, hn⟩))

theorem forall_or_exists_not: (∀ x : α, P x) ∨ (∃ x : α, ¬ P x) :=
  Or.elim
    (Classical.em (∃ x : α, ¬ P x))
    (λ m ↦ Or.inr m)
    (λ nx ↦
      Or.inl (
        λ x ↦
          Or.elim (Classical.em (P x))
            (λ px ↦ px)
            (λ npx ↦ False.elim (nx ⟨x, npx⟩))
      ))




example (people : Type) (Joe : people) (drinks : people → Prop) :
  ∃ x : people, drinks x → ∀ y : people, drinks y :=
  sorry

/- Tactics -/

variable (p q r : Prop)

/- Intro, exact, apply, assumption -/

theorem ex1 : p → p := by
  intro hp
  exact hp

#print ex1

theorem ex2 : p → q → p := by
  intro hp
  intro hq
  exact hp

#print ex2

theorem ex3 : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  exact (hqr (hpq hp))

#print ex3

theorem ex3' : (p → q) → (q → r) → p → r := by
  intro hpq hqr hp
  apply hqr
  apply hpq
  exact hp

#print ex3'

theorem ex4 : (p → (q → r)) → (p → q) → p → r := by
  intro hpqr hpq hp
  apply hpqr
  · exact hp
  · apply hpq
    apply hp

#print ex4

theorem ex4': (p → (q → r)) → (p → q) → p → r := by
  intro hpqr hpq hp
  apply hpqr
  apply hp
  apply hpq
  exact hp



theorem ex5 : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro ⟨hp, hqr⟩
  apply Or.elim hqr
  . intro hq
    apply Or.inl
    apply And.intro
    . assumption
    . assumption
  . intro hr
    apply Or.inr
    apply And.intro
    . assumption
    . assumption

#print ex5

example : (p → q) → (¬ q → ¬ p) := by
  intro pq nq np
  apply False.elim
  apply nq
  apply pq
  assumption


example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  · intro pq
    apply And.intro
    · exact pq.right
    · exact pq.left
  · intro qp
    apply And.intro
    · exact qp.right
    · exact qp.left



example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  · intro ⟨p, q⟩
    apply And.intro
    · exact q
    · exact p
  · intro ⟨q, p⟩
    apply And.intro
    · exact p
    · exact q

/- cases, constructor, left/right, exists -/

example : p ∨ q → q ∨ p := by
  intro hpq
  cases hpq
  case inl =>
    right
    assumption
  case inr =>
    left
    assumption

example : (p ∧ q) ∨ (p ∧ r) → p ∧ (q ∨ r) := by
  intro h
  cases h
  case inl hpq =>
    constructor
    · exact hpq.1
    · left
      apply hpq.2
  case inr hpr =>
    have ⟨hp, hr⟩ := hpr
    constructor
    · assumption
    · right
      assumption

example : p ∨ q → ¬ (¬ p ∧ ¬ q) := by
  intro h
  intro ⟨ np, nq ⟩
  cases h
  case inl hp =>
    apply False.elim
    apply np
    assumption
  case inr hq =>
    apply False.elim
    apply nq
    assumption



example : (∀ x : α, P x) ∨ (∀ x : α, Q x) → ∀ x : α, P x ∨ Q x  := by
  intro h x
  cases h
  case inl h =>
    left
    apply h
  case inr h =>
    right
    apply h

example : (∃ x : α, P x ∧ Q x) → (∃ x : α, P x) ∧ (∃ x : α, Q x) := by
  intro ⟨x, hP, hQ⟩
  constructor
  · exists x
  · exists x


example : (∀ (x : α), P x ∧ Q x) ↔ (∀ x : α, P x) ∧ (∀ x : α, Q x) := by
  constructor
  · intro h
    constructor
    · intro x
      exact (h x).1
    · intro x
      exact (h x).2
  · intro h
    intro x
    constructor
    · exact h.1 x
    · exact h.2 x

example : (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  constructor
  · intro ⟨ x, pq ⟩
    apply Or.elim pq
    · intro hp
      apply Or.inl
      exists x
    · intro hq
      apply Or.inr
      exists x

  · intro h
    apply Or.elim h
    · intro ⟨ x, px ⟩
      exists x
      apply Or.inl
      assumption
    · intro ⟨ x, qx ⟩
      exists x
      apply Or.inr
      assumption







/- Tactic combinators -/

example (p q : Prop) (hp : p) : p ∨ q := by
  apply Or.inl; assumption

example (p q : Prop) (hp : p) (hq : q) : p ∧ q :=
  by constructor <;> assumption

--which is
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor
  · assumption
  · assumption

example (p q : Prop) (hp : p) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q : Prop) (hq : q) : p ∨ q := by
  first | apply Or.inl; assumption | apply Or.inr; assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) (hm: m): p ∧ q ∧ r ∧ m := by
  repeat (constructor <;> try assumption)

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals constructor)
  all_goals assumption

example (p q r : Prop) (hp : p) (hq : q) (hr : r) :
  p ∧ ((p ∧ q) ∧ r) ∧ (q ∧ r ∧ p) := by
  repeat (any_goals (first | constructor | assumption))

example (p q r : Prop) (hp : p) :
  (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
  repeat (any_goals (
    first
    | assumption
    | apply Or.inl; assumption
    | apply Or.inr
    | constructor
  ))

/- Make your own tactic -/

-- Define a new tactic notation
syntax "triv" : tactic

macro_rules
  | `(tactic| triv) => `(tactic| assumption)

example (h : p) : p := by
  triv

macro_rules
  | `(tactic| triv) => `(tactic| rfl)

example (x : α) : x = x := by
  triv

example (x : α) (h : p) : x = x ∧ p := by
  apply And.intro <;> triv

macro_rules | `(tactic| triv) => `(tactic| constructor <;> triv)

example (x : α) (h : p) : x = x ∧ p := by
  triv

/-!
# Exercises
-/
section hw
  example : ∀ p q : Prop, p ∧ q ↔ ∀ r : Prop, (p → q → r) → r := by
    intro p q
    apply Iff.intro
    · intro hpq hr h
      exact h hpq.1 hpq.2
    · intro h
      constructor
      · exact h p (λ hp hq ↦ hp)
      · exact h q (λ hp hq ↦ hq)

  example : ∀ p q : Prop, (p ∨ q ↔ ∀ r : Prop, (p → r) → (q → r) → r) := by
    intro p q
    apply Iff.intro
    · grind
    · intro h
      exact (h (p ∨ q) (λ hp ↦ Or.inl hp) (λ hq ↦ Or.inr hq))

  example : (∃ x : α, P x) ↔ ∀ r : Prop, (∀ x : α, P x → r) → r := by
    apply Iff.intro
    · intro ⟨ x, hx ⟩ r h
      exact (h x) hx
    · intro r
      exact (r (∃ x: α, P x) (λ x hx => ⟨ x, hx ⟩ ))


  /--
  theorem knaster_tarski - WIP
  --/

  theorem knaster_tarski
    (R : α → α → Prop)
    (trans : ∀ x y z : α, R x y → R y z → R x z)
    (inf : ∀ P : α → Prop, ∃ m : α,
      (∀ x : α, P x → R m x) ∧
      (∀ z : α, (∀ x : α, P x → R z x) → R z m))
    (f : α → α)
    (mono : ∀ x y : α, R x y → R (f x) (f y)) :
    ∃ p : α, R (f p) p ∧ R p (f p) := sorry

  /-- Explain what this theorem means
  Это парадокс Жирара.

  пи принимает на вход семейство типов (Type->Type) и выдаёт тип
  лямбда - функция,
    берёт
      функцию из альфа в X альфа, (Х имеет тип Type->Type)
    выдаёт пи от икс
  эпсилон - функция
    берёт
      пи от икс
      альфа
    выдаёт
      X от альфа
  бета
    бета-редукция

  Предположение о существовании всех 4 одновременно.

  Т.е. неверно, что мы можем делать бета-редукцию (и тогда всё логическое исчисление "ломается")

  --/

  theorem girard
    (π : (Type → Type) → Type)
    (Λ : ∀ {X : Type → Type}, ((α : Type) → X α) → π X)
    (ε : ∀ {X : Type → Type}, π X → (α : Type) → X α)
    (β : ∀ {X : Type → Type} (f : (α : Type) → X α) (α : Type),
      ∀ (P : X α → Prop), P (ε (Λ f) α) ↔ P (f α))
    : False :=
    sorry


end hw
