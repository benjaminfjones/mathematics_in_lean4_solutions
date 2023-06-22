import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Basic

-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b, mul_assoc, mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [←mul_assoc a b c, mul_comm a b, mul_assoc b a c]

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [mul_comm]
  rw [mul_assoc]
  rw [mul_comm a _]

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]


example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc, mul_assoc, ←mul_assoc b c d, h, mul_assoc, ←mul_assoc, ←mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp, hyp', mul_comm, sub_self]

-- Examples.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section

variable (a b c d e f g : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm
#check @mul_comm

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

-- `rw` tactic only version
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * c)]
  rw [add_comm (b*c), ← add_assoc (a*c)]

-- calc version
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = (a + b) * c + (a + b) * d         := by rw [mul_add]
    _                 = a * c + b * c + (a * d + b * d)   := by rw [add_mul, add_mul]
    _                 = (a * c + (b * c + a * d)) + b * d := by rw [← add_assoc, add_assoc (a*c)]
    _                 = (a * c + (a * d + b * c)) + b * d := by rw [add_comm (b*c)]
    _                 = a * c + a * d + b * c + b * d     := by rw [← add_assoc (a*c)]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 :=
  calc
    (a + b) * (a - b) = (a + b) * a - (a + b) * b := by rw [mul_sub]
    _                 = a * a + b * a - (a * b + b * b) := by rw [add_mul, add_mul]
    _                 = a * a + b * a - a * b - b * b := by rw [sub_sub]
    _                 = a * a + b * a - b * a - b * b := by rw [mul_comm a b]
    _                 = a * a + (b * a - b * a) - b * b := by rw [add_sub]
    _                 = a * a + 0 - b * b := by rw [sub_self]
    _                 = a * a - b * b := by rw [add_zero]
    _                 = a ^ 2 - b ^ 2 := by rw [pow_two, pow_two]

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
#check sub_self

end

-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
