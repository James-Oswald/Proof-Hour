-- 6/26/2023

import data.set.basic

inductive prop : Type
| atom : nat -> prop
| and : prop -> prop -> prop
| or : prop -> prop -> prop
| not : prop -> prop
| cond : prop -> prop -> prop

--Returns if a formula is satisfied in a given interpretation
def sat : prop -> (nat -> Prop) -> Prop
| (prop.atom n) interp := interp n
| (prop.and p1 p2) interp := (sat p1 interp) ∧ (sat p2 interp)
| (prop.or p1 p2) interp := (sat p1 interp) ∧ (sat p2 interp)
| (prop.not p1) interp := ¬(sat p1 interp)
| (prop.cond p1 p2) interp := (sat p1 interp) → (sat p2 interp)

def valid (formula : prop) : Prop := 
∀ (interp : nat -> Prop), sat formula interp

-- ψ -> ψ is valid for all formula ψ
example: ∀(ψ : prop), valid (prop.cond ψ ψ) :=
begin
  intros ψ,
  rw valid,
  intros interp,
  rw sat,
  intros H,
  exact H,
end

def is_and: prop -> Prop
| (prop.atom _) := false
| (prop.and _ _) := true
| (prop.or _ _) := false
| (prop.not _) := false
| (prop.cond _ _) := false

def and_intro_test (f1 f2 : prop) (a1 : is_and f1) (a2 : is_and f2) : prop :=
(prop.and f1 f2)

#check and_intro_test

structure NDProofStep :=
(formula : prop)
(assumptions : set prop)

def and_intro (f1 f2 : NDProofStep) 
  (a1 : is_and f1.formula) 
  (a2 : is_and f2.formula) : NDProofStep :=
NDProofStep.mk 
  (prop.and f1.formula f2.formula)
  (f1.assumptions ∪ f2.assumptions)

#check and_intro

#check @or.elim