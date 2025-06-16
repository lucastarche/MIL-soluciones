import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h]
    linarith

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h]
    linarith
  · rw [abs_of_neg h]

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x + y) with h | h
  · rw [abs_of_nonneg h]
    linarith [le_abs_self x, le_abs_self y]
  · rw [abs_of_neg h, neg_add]
    linarith [neg_le_abs_self x, neg_le_abs_self y]

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  · rintro h
    rcases le_or_gt 0 y with h' | h'
    · left
      rw [abs_of_nonneg h'] at h
      exact h
    · right
      rw [abs_of_neg h'] at h
      exact h
  · rintro h
    rcases h with h | h
    · linarith [le_abs_self y]
    · linarith [neg_le_abs_self y]

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor <;> rintro h
  · constructor
    · linarith [neg_le_abs_self x]
    · linarith [le_abs_self x]
  · rcases h with ⟨h₀,h₁⟩
    rcases le_or_gt 0 x with h' | h'
    · rw [abs_of_nonneg h']
      exact h₁
    · rw [abs_of_neg h']
      linarith

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨x, y, rfl | rfl⟩ <;> linarith [sq_nonneg x, sq_nonneg y]

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  replace h : (x - 1) * (x + 1) = 0 := by linarith
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h
  rcases h with h | h
  · left ; linarith
  · right ; linarith

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  replace h : (x - y) * (x + y) = 0 := by linarith
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h
  rcases h with h | h
  · left ; linarith
  · right ; linarith

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  replace h : (x - 1) * (x + 1) = 0 := by
    ring
    simp [h]

  apply eq_zero_or_eq_zero_of_mul_eq_zero at h
  rcases h with h | h
  · left
    exact (sub_eq_zero.mp h)
  · right
    exact (add_eq_zero_iff_eq_neg.mp h)

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  replace h : (x - y) * (x + y) = 0 := by
    ring
    simp [h]

  apply eq_zero_or_eq_zero_of_mul_eq_zero at h
  rcases h with h | h
  · left
    exact (sub_eq_zero.mp h)
  · right
    exact (add_eq_zero_iff_eq_neg.mp h)

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  rcases em P with p_true | p_false <;> constructor <;> rintro h
  · exact Or.inr (h p_true)
  · contrapose! h
    exact h
  · exact Or.inl p_false
  · contrapose! p_false
    exact And.left p_false
