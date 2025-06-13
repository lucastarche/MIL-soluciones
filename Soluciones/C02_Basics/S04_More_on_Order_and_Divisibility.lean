import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

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
  apply le_antisymm
  · show max a b ≤ max b a
    apply max_le
    · apply le_max_right
    · apply le_max_left
  · show max b a ≤ max a b
    apply max_le
    · apply le_max_right
    · apply le_max_left

example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · show min (min a b) c ≤ min a (min b c)
    apply le_min
    · have h : min (min a b) c ≤ min a b := by apply min_le_left
      apply le_trans h
      exact min_le_left a b
    · have h₀ : min (min a b) c ≤ b := by
        have h : min (min a b) c ≤ min a b := by apply min_le_left
        apply le_trans h
        apply min_le_right
      have h₁ : min (min a b) c ≤ c := by apply min_le_right
      apply le_min h₀ h₁
  · show min a (min b c) ≤ min (min a b) c
    apply le_min
    · apply le_min
      · apply min_le_left
      · have h : min a (min b c) ≤ min b c := by apply min_le_right
        apply le_trans h
        apply min_le_left
    · have h : min a (min b c) ≤ min b c := by apply min_le_right
      apply le_trans h
      apply min_le_right

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · show min a b + c ≤ a + c
    apply add_le_add
    apply min_le_left
    exact le_refl c
  · show min a b + c ≤ b + c
    apply add_le_add
    apply min_le_right
    exact le_refl c

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · exact aux a b c
  · show min (a + c) (b + c) ≤ min a b + c
    have h : min (a + c) (b + c) + (-c) ≤ min (a + c + -c) (b + c + -c) := by
      apply aux (a + c) (b + c) (-c)
    rw [add_neg_cancel_right, add_neg_cancel_right] at h
    linarith

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  suffices |a| ≤ |a - b| + |b| by linarith
  have h : a = a - b + b := by ring
  nth_rewrite 1 [h]
  apply abs_add

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    · apply dvd_mul_left
  · apply dvd_trans h
    apply dvd_mul_left


end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply _root_.dvd_antisymm
  · apply dvd_gcd
    · apply gcd_dvd_right
    · apply gcd_dvd_left
  · apply dvd_gcd
    · apply gcd_dvd_right
    · apply gcd_dvd_left

end
