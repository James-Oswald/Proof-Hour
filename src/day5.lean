-- 6/30/2023

import day4

--s12 is the string "12" over the alphabet {1,2}
def s12 : @str nat {1,2} := str.mk [1,2] begin finish end

--l12star is the language of {"12", "1212", "121212", ...}
--over the alphabet {1,2}
def l12n : @language nat {1,2} :=
language.mk {x | ∃(i : ℕ), x = (concatn s12 i)}

def s1 : @str nat {1,2} := str.mk [1] begin finish end
def s2 : @str nat {1,2} := str.mk [2] begin finish end
def l1 : @language nat {1,2} := language.mk {s1}
def l2 : @language nat {1,2} := language.mk {s2}
def l12 : @language nat {1,2} := language.mk {s12}

example: regular l12n :=
begin
  have l1_reg : regular l1,
  {
    apply regular.singleton l1 1,
    finish, finish,
  },
  have l2_reg : regular l2,
  {
    apply regular.singleton l2 2,
    finish, finish,
  },
  have l12_reg : regular l12,
  {
    apply regular.concat l12 l1 l2,
    exact l1_reg, exact l2_reg,
    rw l12, rw l1, rw l2, rw s12, rw s1, rw s2,
    rw lang_concat, simp, rw concat, simp,
  },
  apply regular.kstar l12n l12,
  exact l12_reg,
  rw l12n, rw KStar, rw l12, rw s12,
  simp [set.subset.antisymm_iff], split,
  intros a,
  induction a,{
    simp [concatn],
    existsi 0,
    rw V,
    finish,
  },{
    cases a_ih,
    existsi a_ih_w + 1,
    rw V, simp,
    intros w v we ve,
    rw concat,
    sorry,
  },
  sorry,
end