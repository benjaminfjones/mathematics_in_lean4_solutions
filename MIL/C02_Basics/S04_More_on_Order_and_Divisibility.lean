import Mathlib.Data.Real.Basic

namespace C02S04
section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
-- le_antisymm.{u} {α : Type u} [PartialOrder α] {a b : α}
--   (a✝ : a ≤ b) (a✝¹ : b ≤ a) : a = b
#check le_antisymm


example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    . apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    . apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  have h : ∀ (x y : ℝ), max x y ≤ max y x := by
    intro x y
    apply max_le
    . apply le_max_right
    . apply le_max_left
  apply le_antisymm
  repeat (apply h)

-- every combination of `le_trans` with `min_le_{left,right}` appears here
example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  . show min (min a b) c ≤ min a (min b c)
    apply le_min
    . show min (min a b) c ≤ a
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    . show min (min a b) c ≤ min b c
      apply le_min
      . show min (min a b) c ≤ b
        exact le_trans (min_le_left _ _) (min_le_right _ _)
      . show min (min a b) c ≤ c
        apply min_le_right
  . show min a (min b c) ≤ min (min a b) c
    apply le_min
    . show min a (min b c) ≤ min a b
      apply le_min
      . exact min_le_left _ _
      . exact le_trans (min_le_right _ _) (min_le_left _ _)
    . show min a (min b c) ≤ c
      exact le_trans (min_le_right _ _) (min_le_right _ _)

#check add_neg_cancel_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  . show min a b + c ≤ a + c
    apply add_le_add_right
    apply min_le_left
  . show min a b + c ≤ b + c
    apply add_le_add_right
    apply min_le_right

-- No linarith :)
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  . apply aux
  . have h : min (a - (-c)) (b - (-c)) + (-c) ≤
      min ((a - (-c)) + (-c)) ((b - (-c)) + (-c)) := by apply aux
    have hac : a - (-c) = a + c := by apply sub_neg_eq_add
    have hbc : b - (-c) = b + c := by apply sub_neg_eq_add
    have ha : a - (-c) + (-c) = a := by apply sub_add_cancel
    have hb : b - (-c) + (-c) = b := by apply sub_add_cancel
    rw [ha, hb, hac, hbc] at h
    have h2 : min (a + c) (b + c) + -c + c ≤ min a b + c := add_le_add_right h _
    rw [add_assoc, add_left_neg, add_zero] at h2
    assumption

#check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)
#check sub_add_cancel

-- exactly three lines
example : abs a - abs b ≤ abs (a - b) := by
  have h : abs (a - b + b) ≤ abs (a - b) + abs b := by apply abs_add
  rw [sub_add_cancel] at h
  linarith

end

section
variable (w x y z : ℕ)

#check x ∣ y

example : x ∣ y ↔ (∃ (c : Nat), y = x * c) := by
  constructor
  . intro
    assumption
  . intro
    assumption

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
   apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  apply dvd_add
  . apply dvd_mul_of_dvd_right
    apply dvd_mul_right
  . apply dvd_mul_left
  . apply dvd_mul_of_dvd_right
    assumption

end

section
variable (m n : ℕ)
open Nat

#check (gcd_zero_right n : gcd n 0 = n)
#check (gcd_zero_left n : gcd 0 n = n)
#check (lcm_zero_right n : lcm n 0 = 0)
#check (lcm_zero_left n : lcm 0 n = 0)

example : gcd m n = gcd n m := by
  apply gcd_comm

end


