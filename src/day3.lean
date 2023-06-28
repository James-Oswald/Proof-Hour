
-- 6/27/2023

import data.list.basic
import data.set.basic

--A language over an alphabet is a set of strings and
-- a proof that every char in every string is in the alphabet
structure language {α : Type} (alphabet : set α) :=
(strings : set (list α))
(H : ∀(s : list α), s ∈ strings → (∀(c : α), c ∈ s → c ∈ alphabet))

def rearSubstrings {α : Type} : list α -> set(list α)
| list.nil := ∅
| (list.cons h t) := {t} ∪ rearSubstrings t 

--If a string S is in a language over an alphabet a, then 
--all rear substrings of S contain only characters from a.
lemma rschars {α : Type} {a : set α} (l : language a) (s : list α):
s ∈ l.strings → ∀(x ∈ rearSubstrings s), ∀(c : α), c ∈ x → c ∈ a :=
begin
  intros st x xt c ct,
  cases s,{
    simp [rearSubstrings] at xt,
    contradiction,
  },{
    simp [rearSubstrings] at xt,
    cases l,simp at st,
    cases xt,{
      have H := l_H (s_hd :: s_tl) st c,
      rw<- xt at H,
      --trivial from ct and H 
      finish,
    },{
      induction x,{
        simp at ct,
        contradiction,
      },{
        cases ct,
      }
    }

  }


/-  cases s,{
    simp [rearSubstrings] at xt,
    contradiction,
  },{
    simp [rearSubstrings] at xt,
    cases l,
    simp at st,
    cases xt,{
      have H := l_H (s_hd :: s_tl) st c,
      rw<- xt at H,
      --trivial from ct and H 
      finish,
    },{
      induction s_tl,
      simp [rearSubstrings] at xt,
      contradiction,

      --have H := l_H (s_hd :: s_tl) st c,
    }
  }
-/
end

lemma l1 {α : Type} {a : set α} :
∀ (l1 l2 : language a) (s1 s2 : list α), 
s1 ∈ l1.strings → s2 ∈ l2.strings → 
∀(c : α), c ∈ (list.append s1 s2) → c ∈ a :=
begin
  intros l1 l2 s1 s2 s1l1 s2l2 ca cac,
  cases l1, cases l2,
  simp [language.strings] at s1l1 s2l2,
  cases s1,{
    simp at cac,
    exact l2_H s2 s2l2 ca cac,
  },{
    
  }
  
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

