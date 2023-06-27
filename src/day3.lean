
-- 6/27/2023

import data.list.basic
import data.set.basic

--A language over an alphabet is a set of strings and
-- a proof that every char in every string is in the alphabet
structure language {α : Type} (alphabet : set α) :=
(strings : set (list α))
(H : ∀(s : list α), s ∈ strings → (∀(c : α), c ∈ alphabet → c ∈ s))

--def kstar {α : Type} {a : set α} (l : language a) : language a :=


--lang is a regular language over the given alphabet 
inductive regular {α : Type} {a : set α} (l : language a): Prop
| empty : l.strings = ∅ -> regular
| singleton : 
  ∀(c : α), c ∈ a -> l.strings = {[c]} -> regular

