
import tactic.linarith
import data.real.basic

--Working through some examples in section 4.3
--of Hammack's Book of proof

--A number n is odd iff it can be written 
--2 * a + 1
def odd_m (n : ℤ) : Prop :=
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

def even_m (n : ℤ) : Prop :=
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

--Big O from 
--https://en.wikipedia.org/wiki/Big_O_notation#Family_of_Bachmann%E2%80%93Landau_notations
def O (f : ℝ -> ℝ) (g : ℝ -> ℝ) : Prop :=
∃ (k : ℝ), k > 0 → ∃ (n0 : ℝ), ∀ (n : ℝ), n > n0 → |(f n)| ≤ k * (g n)

--2x^2 + x + 1 is O(x^2) 
example: O (λ (x : ℝ), 2*x*x + x + 1) (λ (x : ℝ),x*x) :=
begin
  rw O,
  existsi (3 : ℝ),
  intro kh,
  existsi (2 : ℝ),
  intros n nh,
  have left_pos : 0 < 2 * n * n + n + 1,{
    have h1 : 0 < n, by sorry,
    have l1 : (0 : ℝ) < (1 : ℝ), by finish,
    have l2 : (0 : ℝ) < (2 : ℝ), by finish,
    have h2 : 0 < 2 * n, by apply mul_pos l2 h1,
    have h3 : 0 < n + 1, by apply add_pos h1 l1,
    have h4 : 0 < 2 * n * n, by apply mul_pos h2 h1,
    have h5 : 0 < 2 * n * n + (n + 1), by apply add_pos h4 h3,
    rw add_assoc (2 * n * n) n 1,
    exact h5,
  },
  simp [abs_of_pos left_pos],
  

end
