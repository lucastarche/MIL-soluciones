import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · rintro h x xs
    show f x ∈ v
    apply h
    use x, xs
  · rintro h y yfs
    obtain ⟨x, xs, rfl⟩ := yfs
    apply h
    exact xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x xs
  obtain ⟨y, ys, fx_eq_fy⟩ := xs
  apply h at fx_eq_fy
  rw [← fx_eq_fy]
  exact ys

example : f '' (f ⁻¹' u) ⊆ u := by
  intro x h
  obtain ⟨y, ypreu, rfl⟩ := h
  apply ypreu

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  intro y yu
  obtain ⟨x, rfl⟩ := h y
  use x, yu

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  intro y yfs
  obtain ⟨x, xs, rfl⟩ := yfs
  have xt : x ∈ t := h xs
  use x, xt

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro x h'
  exact h h'

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext x; constructor
  · rintro (xu | xv)
    · exact Or.inl xu
    · exact Or.inr xv
  · rintro (xu | xv) <;> show f x ∈ u ∪ v
    · exact Or.inl xu
    · exact Or.inr xv

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro x xfst
  obtain ⟨y, ⟨ys, yt⟩, rfl⟩ := xfst
  have fyfs: f y ∈ f '' s := by use y, ys
  have fyft: f y ∈ f '' t := by use y, yt
  exact ⟨fyfs, fyft⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  intro y ⟨yfs, yft⟩
  obtain ⟨x, xs, rfl⟩ := yfs
  obtain ⟨x', x't, fx_eq_fx'⟩ := yft
  obtain rfl := h (symm fx_eq_fx')
  use x, ⟨xs, x't⟩

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  intro y ⟨yfs, ynft⟩
  obtain ⟨x, xs, rfl⟩ := yfs
  have xnt : x ∉ t := by
    contrapose! ynft
    use x
  use x, ⟨xs, xnt⟩

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  intro x ⟨fxu, fxnv⟩
  show f x ∈ u \ v
  exact ⟨fxu, fxnv⟩

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  ext x; constructor
  · rintro ⟨xfs, xv⟩
    obtain ⟨y, ys, rfl⟩ := xfs
    use y, ⟨ys, xv⟩
  · rintro ⟨y, ⟨ys, fyv⟩, rfl⟩
    have : f y ∈ f '' s := by use y, ys
    exact ⟨this, fyv⟩

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  intro y hy
  obtain ⟨x, ⟨xs, fxu⟩, rfl⟩ := hy
  have : f x ∈ f '' s := by use x, xs
  exact ⟨this, fxu⟩

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  intro x ⟨xs, fxu⟩
  have : f x ∈ f '' s := by use x, xs
  exact ⟨this, fxu⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  rintro x (xs | fxu)
  · have : f x ∈ f '' s := by use x, xs
    exact Or.inl this
  · exact Or.inr fxu

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y ; constructor
  · rintro ⟨x, h, rfl⟩
    obtain ⟨Ai, ⟨i, rfl⟩, xAi⟩ := h
    simp at xAi
    have : f x ∈ f '' A i := by use x, xAi
    use f '' A i
    simp
    use x
  · rintro ⟨fAi, ⟨i, rfl⟩, yfAi⟩
    obtain ⟨x, xAi, rfl⟩ := yfAi
    have : x ∈ (⋃ i, A i) := by
      use A i
      simp
      exact xAi
    use x

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  rintro y ⟨x, hx, rfl⟩
  simp ; simp at hx

  intro i
  use x, hx i

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  rintro y hy
  simp ; simp at hy
  obtain ⟨x, xAi, rfl⟩ := hy i
  use x ; simp

  intro i'
  obtain ⟨x', x'Ai', fx'_eq_fx⟩ := hy i'
  obtain rfl := injf (symm fx'_eq_fx)
  exact x'Ai'

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x ; constructor
  · rintro h
    dsimp [preimage] at h
    simp only [mem_iUnion] ; simp only [mem_iUnion] at h
    apply h
  · rintro h
    simp only [mem_iUnion] at h
    obtain ⟨i, hi⟩ := h
    dsimp [preimage] at hi ; dsimp [preimage]
    simp only [mem_iUnion]
    use i

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x ; constructor
  · rintro h
    dsimp [preimage] at h
    simp only [mem_iInter] at h ; simp only [mem_iInter]
    exact h
  · rintro h
    dsimp [preimage]
    simp only [mem_iInter] at h ; simp only [mem_iInter]
    exact h

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xnn y ynn h

  calc
    x = √x * √x := by rw [← sqrt_mul xnn, sqrt_mul_self xnn]
    _ = √y * √y := by rw [h]
    _ = y := by rw [← sqrt_mul ynn, sqrt_mul_self ynn]


example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xnn y ynn h
  dsimp at h

  calc
    x = √(x * x) := by rw [sqrt_mul_self xnn]
    _ = √(y * y) := by rw [← sq, h, sq]
    _ = y := by rw [sqrt_mul_self ynn]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, xnn, rfl⟩
    apply sqrt_nonneg
  · rintro ynn
    use y^2
    exact ⟨sq_nonneg y, sqrt_sq ynn⟩

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    dsimp
    exact sq_nonneg x
  · intro ynn
    use √y
    dsimp
    exact sq_sqrt ynn

end

section
variable {α β : Type*} [Inhabited α]

-- #check (default : α)

-- variable (P : α → Prop) (h : ∃ x, P x)

-- #check Classical.choose h

-- example : P (Classical.choose h) :=
--   Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  · intro h x
    have : ∃ x', f x' = f x := by use x
    rw [inverse, dif_pos this]
    have fx_eq_fchoose : f (choose this) = f x := Classical.choose_spec this
    exact h fx_eq_fchoose
  · intro h x x' f_eq
    have : inverse f (f x) = inverse f (f x') := by rw [f_eq]
    rw [h, h] at this
    exact this

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h y
    have ex_x: ∃ x, f x = y := by use x
    rw [inverse_spec y ex_x]
  · intro h y
    use (inverse f) y
    apply h

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := h₁
  have h₃ : j ∉ S := by
    rw [← h]
    apply h₁
  contradiction

-- COMMENTS: TODO: improve this
end
