/- Implicit arguments -/

def id1 : (α : Type) → α → α := λ _ x ↦ x

#check id1
#check id1 Nat 5
#check id1 Prop True
#check_failure id1 5

def id2 : {α : Type} → α → α := λ x ↦ x

#check id2
#check id2 5
#check id2 True
#check_failure id2 Nat 5
#check @id2
#check @id2 Nat 5

def compose {α β γ : Type} (f : α → β) (g : β → γ) :
  α → γ := λ x ↦ g (f x)

/- Structures -/

structure PointNatNat : Type where
  mk ::
  x : Nat
  y : Nat

#check PointNatNat
#check PointNatNat.mk
#check PointNatNat.x
#check PointNatNat.y


#check PointNatNat.mk 1 2
#check ({ x := 1, y := 2 } : PointNatNat)
#check ({ y := 2, x := 1 } : PointNatNat)
#check_failure {x := 1, y := 2}

#check_failure {x := 1, y := 2 : Nat}
#check {x := 1, y := 2 : PointNatNat}
#check {x := 1, y := (2 : Nat) : PointNatNat}

def pp : PointNatNat := {x := 0, y := 0}

#eval {pp with x := 3}

#check (⟨0, 1⟩ : PointNatNat)
#eval pp.1
#eval pp.2

structure PointNatNatNat extends PointNatNat where
  z : Nat

#check {x := 0, y := 0, z := 0 : PointNatNatNat}
#check PointNatNatNat.toPointNatNat

structure Prod' (A B : Type) : Type where
  fst : A
  snd : B

#check Prod' Nat Prop

#check Prod
#print Prod
#check Prod Nat Nat
#check Nat × Nat

structure PointType where
  A : Type
  x : A
  y : A

#check { A := Nat, x := 0, y := 0 : PointType }

/- Propositions as Types -/
#check Prop
#check False
#check True

section CH
  axiom And' : Prop → Prop → Prop
  axiom Implies : Prop → Prop → Prop

  variable (p q r : Prop)

  #check Implies (And' p q) (And' q p)

  variable (Proof : Prop → Type)

  variable (modus_ponens : Proof (Implies p q) → Proof p → Proof q)
  variable (implies_intro : (Proof p → Proof q) → Proof (Implies p q))

  /-
  First, we can get rid of `Proof` and identify `Proof p` with `p` itself!
  Second, above axioms show that:
    modus_ponens p q  : Implies p q → (p → q)
    implies_intro p q : (p → q) → Implies p q

  So, we can try identifying Implies p q with the λction space (p → q)
  -/

  #check p

  variable (t : p)
  #check t

  #check (p → q → p)
end CH

/- Implication -/
variable {p q r : Prop}

theorem t1 : p → q → p := λ hp _ ↦ hp

#check t1
#print t1

theorem t1' : p → q → p :=
  λ hp : p ↦
  λ hq : q ↦
  show p from hp

theorem t2 (hp : p) : q → p := t1 hp

example : p → p := sorry
example : (p → q) → (q → r) → p → r := sorry
example : (p → (q → r)) → (p → q) → p → r := sorry

/- And -/
#check And
#print And
#check And p q
#check p ∧ q

example : p → q → p ∧ q := λ hp hq ↦ ⟨hp, hq⟩
example : p ∧ q → q ∧ p := sorry

/- Or -/

#check Or
#print Or
#check Or p q
#check p ∨ q
#check Or.inl
#check Or.inr
#check Or.elim

example : p ∨ q → q ∨ p :=
  λ h ↦ Or.elim h (λ hp ↦ Or.inr hp) (λ hq ↦ Or.inl hq)

/- True -/

#check True
#check True.intro
#check trivial
#print trivial

example : p → True :=
  λ _ ↦ trivial
example : (p ∨ True) ∧ True := sorry

/- False -/

#check False
#check False.elim

example : False → p := False.elim

/- Not -/
#check Not
#print Not
#check Not p
#check ¬ p

example : (p → ¬ p → q) :=
  λ hp hnp ↦ False.elim (hnp hp)

example : (p → q) → (¬ q → ¬ p) := sorry

/- Iff -/

#check Iff
#print Iff
#check Iff p q
#check p ↔ q

example : p ↔ p ∧ p :=
  ⟨λ hp ↦ ⟨hp, hp⟩,
  λ hpp ↦ hpp.left⟩
example : p ∧ q ↔ q ∧ p := sorry

/- Local definitions -/
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (λ h : p ∧ (q ∨ r) ↦
      have hp : p := h.left
      Or.elim (h.right)
        (λ hq : q ↦
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (λ hr : r ↦
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (λ h : (p ∧ q) ∨ (p ∧ r) ↦
      Or.elim h
        (λ hpq : p ∧ q ↦
          have hp : p := hpq.left
          let hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (λ hpr : p ∧ r ↦
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

/- Classical logic -/

#check Classical.em

example : ¬¬ p → p :=
  λ h ↦ Or.elim (Classical.em p)
    (λ hp ↦ hp)
    (λ hnp ↦ False.elim (h hnp))
example : ¬(p ∧ ¬q) → (p → q) := sorry

/-!
# Exercises
-/

section hw
  /- Classical.em is not required: -/
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    Iff.intro
    (λ h:  (p ∧ q) ∧ r ↦
    have hll : p  := h.left.left
    have hlr : q := h.left.right
    have hr  :  r := h.right
     show p ∧ (q ∧ r) from ⟨ hll, ⟨ hlr, hr  ⟩ ⟩
    )
    (λ h:  p ∧ (q ∧ r) ↦
    have hl : p  := h.left
    have hrl : q := h.right.left
    have hrr  :  r := h.right.right
     show (p ∧ q) ∧ r from ⟨ ⟨ hl,  hrl, ⟩,  hrr  ⟩
    )

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    Iff.intro
   (λ h:   (p ∨ q) ∨ r↦
        Or.elim h
        (
          λ hl: (p ∨ q) ↦
            Or.elim hl
            (λ hp: p ↦ show  p ∨ (q ∨ r) from  (Or.inl hp ))
            (λ hq: q ↦ show  p ∨ (q ∨ r) from Or.inr (Or.inl hq ))
        )
        (
          λ hr: r ↦
          show  p ∨ (q ∨ r) from (Or.inr (Or.inr hr))
        )
    )
    (λ h: p ∨ (q ∨ r) ↦
        Or.elim h
        (
          λ hp: p↦
            show  (p ∨ q) ∨ r from (Or.inl (Or.inl hp))
        )
        (
          λ hr: q ∨ r ↦
            Or.elim hr
              (λ hq: q ↦ show  (p ∨ q) ∨ r from (Or.inl (Or.inr hq)))
              (λ hr: r ↦ show  (p ∨ q) ∨ r from (Or.inr hr)
        )
    )
  )

  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    Iff.intro
    (λ pqr: p ∨ (q ∧ r) ↦
      Or.elim pqr
      (λ hp: p ↦ (And.intro (Or.inl hp) (Or.inl hp)))
      (λ hqr: q ∧ r ↦ (And.intro (Or.inr hqr.left) (Or.inr hqr.right)))
      )
      (λ pqpr: (p ∨ q) ∧ (p ∨ r) ↦
      have hl: (p ∨ q) := pqpr.left;
      have hr: (p ∨ r) := pqpr.right;
      Or.elim hl
      (λ hp: p ↦ Or.inl hp)
      (
        λ hq: q  ↦
        Or.elim hr
        (λ hp: p ↦ Or.inl hp)
        (λ hr: r ↦ Or.inr ⟨ hq, hr ⟩ )
      )
    )



  example : (p → (q → r)) ↔ (p ∧ q → r) :=
    Iff.intro
    (λ (pqr: p → (q → r)) (hpq: p ∧ q) ↦ pqr hpq.left hpq.right)
    (λ hpqr hp hq ↦ hpqr ⟨hp, hq⟩)


  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
    Iff.intro
    (
      λ (hpqr: p ∨ q → r) ↦ ⟨
      λ hp: p ↦ hpqr (Or.inl hp),
      λ hq:q ↦ hpqr (Or.inr hq)
      ⟩
    )
    (
      λ (hprqr: (p → r) ∧ (q → r)) (hpq: (p ∨ q) ) ↦ Or.elim hpq
      (λ hp: p ↦ hprqr.left hp)
      (λ  hq: q ↦ hprqr.right hq)
    )

  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (
      λ (pqf: p ∨ q → False) ↦
        ⟨
          (λ hp: p ↦ pqf (Or.inl hp)),
          (λ hq: q ↦ pqf (Or.inr hq))
        ⟩
    )
    (
      λ npnq:  ¬p ∧ ¬q ↦
        λ hporq: p∨ q  ↦ Or.elim hporq
          (λ hp: p ↦   npnq.left hp )
          (λ hq: q ↦  npnq.right hq)
    )

  example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (λ (npnq: ¬p ∨ ¬q) (npq: p ∧ q)  ↦ (Or.elim npnq
  (λ np: p -> False ↦ np npq.left)
  (λ nq: q -> False ↦ nq npq.right)
  ))


  example : ¬(p ∧ ¬p) :=
    λ h: p ∧ ¬ p ↦
      h.right h.left



  example : p ∧ ¬q → ¬(p → q) :=
  (λ (hpnq: p ∧ ¬ q) (hpq: p →  q) ↦
    have nq := hpnq.right;
    nq (hpq hpnq.left)
  )


  example : ¬p → (p → q) :=
    λ (hnp: p → False) (hp: p) ↦ False.elim (hnp hp)


  example : (¬p ∨ q) → (p → q) :=
    λ (hnpq: ¬p ∨ q) (hp: p) ↦
        Or.elim
          hnpq
          (λ (hnp: p → False) ↦  False.elim (hnp hp))
          λ (hq: q) ↦  hq

  example : p ∨ False ↔ p :=
    Iff.intro
    (λ hpf: p ∨ False ↦
      Or.elim hpf
      (λ hp: p ↦ hp)
      (False.elim)
    )
    (λ hp: p ↦ Or.inl hp)


  example : p ∧ False ↔ False :=
    Iff.intro
      (λ (hpf: p ∧ False) ↦ hpf.right)
      (λ (f: False) ↦ False.elim f)


  example : (p → q) → (¬q → ¬p) :=
    λ (hpq: p → q) (nq: q → False) (p: p) ↦ nq (hpq p)





  /- Classical.em is required: -/
  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
    (λ (hpqr: p → q ∨ r) ↦ Or.elim (Classical.em p)
      (
        λ (hp: p) ↦
          (Or.elim (hpqr hp)
          (λ (hq: q) ↦ (Or.inl (λ _ ↦  hq)))
          (λ (hr: r) ↦ (Or.inr (λ _ ↦  hr)))
        )
      )
     (
        λ (hnp: p →  False) ↦
        Or.inl (λ (hp:p ) ↦ (False.elim (hnp hp))))
     )

  example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ (hpq: (p ∧ q) → False)  ↦ (
    Or.elim (Classical.em p)
    (λ (hp: p)  ↦
      (Or.elim
        (Classical.em q)
        (λ (hq: q) ↦ (False.elim (hpq ⟨ hp, hq⟩ )))
        (λ (hnq: ¬ q) ↦ (Or.inr hnq))
        )
    )
    (λ (hnp: ¬ p) ↦ Or.inl hnp)
  )

  example : ¬(p → q) → p ∧ ¬q :=
  λ (hpqf: (p → q) → False) ↦
  (
    Or.elim (Classical.em p)
    (λ (hp: p) ↦
    ⟨
      hp,
      λ (hq: q) ↦ (hpqf (λ _ ↦ hq))
    ⟩
    )
    (
      λ (hnp: p → False) ↦
      (False.elim (hpqf (λ (hp: p) ↦  False.elim (hnp hp))))
    )
  )

  example : (p → q) → (¬p ∨ q) :=
  λ (hpq: p → q) ↦ (Or.elim (Classical.em p)
  (
    λ (hp: p)  ↦
    (Or.inr (hpq hp))
  )
  (λ (hnp: p -> False) ↦ (Or.inl hnp))
  )

  example : (¬q → ¬p) → (p → q) :=
  (λ (hnqnp: (q → False) → (p → False)) ↦
    (Or.elim (Classical.em q)
    (λ (hq: q) ↦
      (λ _ ↦ hq)
    ))
    (λ (hnq: q → False) ↦
      (λ (hp: p) ↦  False.elim ((hnqnp hnq) hp)
      )
    )
  )


  example : p ∨ ¬p :=
  Classical.em p

  example : (((p → q) → p) → p) :=
  λ (hpqp: (p → q) → p) ↦
  (Or.elim (Classical.em p)
  (λ (hp: p) ↦ hp)
  (λ (hnp: p-> False)
    ↦ hpqp λ (hp: p) ↦ (False.elim (hnp hp))))



end hw
