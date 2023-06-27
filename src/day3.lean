
-- 6/27/2023

import data.list.basic
import data.set.basic

--A language over an alphabet is a set of strings and
-- a proof that every char in every string is in the alphabet
structure language {α : Type} (alphabet : set α) :=
(strings : set (list α))
(H : ∀(s : list α), s ∈ strings → (∀(c : α), c ∈ s → c ∈ alphabet))


lemma l1 {α : Type} {a : set α} :
∀ (l1 l2 : language a) (s1 s2 : list α), 
s1 ∈ l1.strings → s2 ∈ l2.strings → 
∀(c : α), c ∈ (list.append s1 s2) → c ∈ a :=
begin
  intros l1 l2 s1 s2 s1l1 s2l2 ca cac,
  induction s1,
  simp at cac,
  cases l2,
  simp at s2l2,
  exact l2_H s2 s2l2 ca cac,
  simp at cac,
  sorry,
end

def union {α : Type} {a : set α} 
(l1 : language a) (l2 : language a) : language a :=
 language.mk (l1.strings ∪ l2.strings) 
 begin
  cases l1,
  cases l2,
  intros s s_in_strs c c_in_alph,
  cases s_in_strs,{
    simp [language.strings] at s_in_strs,
    exact l1_H s s_in_strs c c_in_alph,
  },{
    simp [language.strings] at s_in_strs,
    exact l2_H s s_in_strs c c_in_alph,
  }
 end

def V {α : Type} {a : set α} (l : language a) : nat -> language a
| 0 := language.mk {[]} begin
    intros s fal c c_in_s,
    simp at fal,
    rw fal at c_in_s,
    simp at c_in_s,
    by_contra,
    exact c_in_s,
  end
| (nat.succ n) := 
  language.mk 
  {x | ∀(w v : list α), w ∈ ((V n).strings) ->
   v ∈ l.strings -> x = (list.append w v)}
  begin
    intros s H ca ca_in_s,
    simp at H,
    sorry,
    --induction n,
  end

--w ∈ ((V n).strings) 
#check V
--def kstar {α : Type} {a : set α} (l : language a) : language a :=


--lang is a regular language over the given alphabet 
inductive regular {α : Type} {a : set α} (l : language a): Prop
| empty : l.strings = ∅ -> regular
| singleton : 
  ∀(c : α), c ∈ a -> l.strings = {[c]} -> regular

