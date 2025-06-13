import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

lemma aux_inf_le_comm : x ⊓ y ≤ y ⊓ x := by
  apply le_inf
  · apply inf_le_right
  · apply inf_le_left

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  · apply aux_inf_le_comm
  · apply aux_inf_le_comm

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · trans (x ⊓ y)
      repeat apply inf_le_left
    · apply le_inf
      · trans (x ⊓ y)
        apply inf_le_left
        apply inf_le_right
      · apply inf_le_right
  · apply le_inf
    · apply le_inf
      · apply inf_le_left
      · trans (y ⊓ z)
        apply inf_le_right
        apply inf_le_left
    · trans (y ⊓ z)
      repeat apply inf_le_right


lemma aux_sup_le_comm : x ⊔ y ≤ y ⊔ x := by
  apply sup_le
  · apply le_sup_right
  · apply le_sup_left

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat apply aux_sup_le_comm

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · apply le_sup_left
      · trans (y ⊔ z)
        apply le_sup_left
        apply le_sup_right
    · trans (y ⊔ z)
      repeat apply le_sup_right
  · apply sup_le
    · trans (x ⊔ y)
      repeat apply le_sup_left
    · apply sup_le
      · trans (x ⊔ y)
        apply le_sup_right
        apply le_sup_left
      · apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  · apply le_inf
    · apply le_refl
    · apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    · apply inf_le_left
  · apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  simp [h]
  apply le_antisymm
  · simp
    trans ((a ⊔ b) ⊓ c)
    · simp
      trans b
      repeat simp
    · simp
  · simp
    rw [← inf_comm, h]
    apply sup_le
    · suffices a ≤ a ⊔ b ⊓ c by
        trans a
        repeat simp
      simp
    · rw [inf_comm]
      apply le_sup_right

-- No voy a hacerlo de vuelta lol
example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

lemma aux₀ (h : a ≤ b) : 0 ≤ b - a := by
  apply add_le_add_left at h
  specialize h (-a)
  rw [neg_add_cancel, add_comm, ← sub_eq_add_neg] at h
  exact h

lemma aux₁ (h: 0 ≤ b - a) : a ≤ b := by
  apply add_le_add_left at h
  specialize h a
  have h₀ : b = a + (b - a) := by simp
  rw [← h₀, add_zero] at h
  exact h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h'' : b = (b - a) + a := by simp
  rw [h'', add_mul]
  suffices 0 ≤ (b - a) * c by
    apply add_le_add_left at this
    specialize this (a * c)
    simp at this
    simp
    exact this
  apply aux₀ at h
  exact mul_nonneg h h'


end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  have h : dist x x ≤ dist x y + dist y x := by apply dist_triangle
  rw [dist_self x, dist_comm y x] at h
  linarith

end
