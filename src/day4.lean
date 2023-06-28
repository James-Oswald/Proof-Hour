-- 6/28/2023

import data.set.basic

--A string over an alphabet 
structure str {α : Type} (alphabet : set α) : Type :=
(chars : list α)
(in_alphabet : ∀(c ∈ chars), c ∈ alphabet)

def emptyStr {α : Type} {alphabet : set α } : str alphabet :=
str.mk [] 
begin
  intros c ce,
  simp at ce,
  contradiction,
end

def str_eq {α : Type} {alphabet : set α }
(s1 s2 : str alphabet) : Prop := s1.chars = s2.chars

--If an element e is in the concatination (appendation)
--of two lists l1 and l2, then e is in l1 or l2. 
lemma eol {α : Type} (l1 l2 : list α) (e : α):
e ∈ list.append l1 l2 → e ∈ l1 ∨ e ∈ l2 :=
begin 
  intros H,
  induction l1,{
    simp at H, right, exact H,
  },{
    simp at H,
    cases H,{
      rw H,
      simp,
    },{
      have H2 := l1_ih H,
      cases H2,{
        left,
        simp [H2],
      },{
        right,
        exact H2,
      }
    }
  }
end 

def concat {α : Type} {alphabet : set α }
(s1 s2 : str alphabet) : str alphabet :=
str.mk (list.append s1.chars s2.chars) 
begin
  cases s1,
  cases s2,
  intros ct ce,
  simp at ce,
  have H := eol s1_chars s2_chars ct ce,
  cases H,{
    exact s1_in_alphabet ct H,
  },{
    exact s2_in_alphabet ct H,
  }
end 

--A string s is a substring of string a f iff
--there exists strings pre and post such that
-- pre s post = f
def is_substr {α : Type} {alphabet : set α }
(s f : str alphabet) : Prop :=
∃(pre post : str alphabet),
(concat (concat pre s) post) = f

structure language {α : Type} (alphabet : set α) :=
(strings : set (str alphabet))

def union {α : Type} {a : set α} 
(l1 : language a) (l2 : language a) : language a :=
 language.mk (l1.strings ∪ l2.strings) 

--Recursive heirarchy of strings at each level i of Klenee Star
def V {α : Type} {alphabet : set α} (l : language alphabet) 
: nat -> language alphabet
| 0 := language.mk {emptyStr}
| (nat.succ n) := language.mk 
  {x | ∀(w v : str alphabet), w ∈ ((V n).strings) ->
   v ∈ l.strings -> x = (concat w v)}

def KStar {α : Type} {alphabet : set α} 
(l : language alphabet) : language alphabet :=
language.mk {x | ∃(i : ℕ), x ∈ (V l i).strings}

def lang_concat {α : Type} {a : set α} 
(l1 l2 : language a) : language a :=
 language.mk {x | ∀(s1 ∈ l1.strings) (s2 ∈ l2.strings),
  x = concat s1 s2}

--https://en.wikipedia.org/wiki/Regular_language#Formal_definition
inductive regular {α : Type} {alphabet : set α} 
(l : language alphabet) : Prop
--the empty language is regular
| empty : l.strings = ∅ → regular
--for each char in the alphabet c, the singleton language  
--{c} is regular
| singleton : 
  ∀ (c ∈ alphabet), l.strings = {str.mk [c] 
  begin
    intros c1 c1e, simp at c1e, rw c1e, exact H,
  end} -> regular
--if l is the kleene star of a regular language ls,
--then l is regular
| kstar : ∀ (ls : language alphabet), 
  regular ls -> l = KStar ls -> regular
| union : ∀ (l1 l2 : language alphabet),
  regular l1 -> regular l2 -> l = (union l1 l2) -> regular
| concat : ∀ (l1 l2 : language alphabet),
  regular l1 -> regular l2 -> l = (lang_concat l1 l2) -> regular

--Repeated self concatination: a^3 = aaa
def concatn {α : Type} {alphabet : set α} (s : str alphabet)
: nat -> str alphabet
| 0 := emptyStr
| (nat.succ n) := concat s (concatn n)

def ns : @str nat {1,2} := str.mk [1,2] 
begin 
  intros ct ce,
  finish,
end

def nl : @language nat {1,2} :=
language.mk {x | ∃(i : ℕ), x = (concatn ns i)}

--example: regular nl