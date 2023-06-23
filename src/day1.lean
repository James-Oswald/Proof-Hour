
import tactic.linarith

--Working through some examples in section 4.3
--of Hammack's Book of proof

--A number n is odd iff it can be written 
--2 * a + 1
def odd (n : ℤ) : Prop :=
∃(a : ℤ), n = 2 * a + 1

example (x : ℤ) : (odd x) → (odd (x*x)) :=
begin
  intros H,
  rw odd at H,
  rw odd,
  cases H with a,
  existsi 2*a*a + 2 * a,
  rw H_h,
  linarith,
end

def divides (a : ℤ) (b : ℤ) : Prop := 
∃(d : ℤ), b = a * d

example (a : ℤ) (b : ℤ) (c : ℤ): 
(divides a b) ∧ (divides b c) → (divides a c) :=
begin
  repeat {rw divides},
  intros h,
  cases h,
  cases h_left with d,
  cases h_right with e,
  rw h_left_h at h_right_h,
  existsi d*e,
  rw h_right_h,
  linarith,
end

def even (n : ℤ) : Prop :=
∃(a : ℤ), n = 2 * a

example (x : ℤ) : (even x) → (odd (x*x-6*x+5)) :=
begin
  intros H,
  rw even at H,
  cases H with a,
  rw H_h,
  rw odd,
  existsi 2*a*a - 6 * a + 2,
  linarith,
end

example (x : ℤ) : (even x) → (even (x*x)) :=
begin
  repeat{rw even},
  intro H,
  cases H with b,
  existsi 2*b*b,
  rw H_h,
  linarith,
end

example (x : ℤ) : (odd x) → (odd (x*x*x)) :=
begin
  repeat{rw odd},
  intro H,
  cases H with b,
  existsi 4*b*b*b + 6*b*b + 3*b,
  rw H_h,
  linarith,
end
