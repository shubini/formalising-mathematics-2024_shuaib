import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional
import LeanCopilot
import Mathlib.LinearAlgebra.Isomorphisms

open FiniteDimensional
variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]


lemma intersection_non_empty_if_sum_of_ranks_greater_than_dimension_of_ambient_space {A B : Subspace k V} (n m1 m2 : ℕ) (hV : FiniteDimensional.finrank k V = n) (hA : FiniteDimensional.finrank k A = m1) (hB : FiniteDimensional.finrank k B = m2) (hS: m1 + m2 > n) : A ⊓ B ≠ ⊥:= by
  intro h
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq A B
  have h3 := Submodule.finrank_le (A ⊔ B)
  rw [hV] at h3
  rw [h, hA, hB, finrank_bot k V] at h2
  norm_num at h2
  rw [h2] at h3
  linarith

lemma rank_nullity_theorem {V₁ : Type} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁] (f : V →ₗ[k] V₁): FiniteDimensional.finrank k (LinearMap.range f) + FiniteDimensional.finrank k (LinearMap.ker f) = FiniteDimensional.finrank k V := by
  have h: (V ⧸ LinearMap.ker f) ≃ₗ[k] ↥(LinearMap.range f) := by
    exact f.quotKerEquivRange
  have h2 : FiniteDimensional.finrank k (V ⧸ LinearMap.ker f) = FiniteDimensional.finrank k (LinearMap.range f):= by
    exact LinearEquiv.finrank_eq h
  rw [←h2]
  exact Submodule.finrank_quotient_add_finrank (LinearMap.ker f)

theorem finite_vector_spaces_are_isomorphic_if_they_have_the_same_dim {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V][FiniteDimensional k V] {W : Type} [AddCommGroup W] [Module k W][FiniteDimensional k W] (hn: finrank k V = finrank k W) : V ≃ₗ[k] W := by
  let n := finrank k V
  have B : Basis (Fin n) k V := by
    exact FiniteDimensional.finBasisOfFinrankEq k V rfl
  have C : Basis (Fin n) k W := by
    exact FiniteDimensional.finBasisOfFinrankEq k W (by rw [←hn])

  let φ : V →ₗ[k] W := B.constr k C
  let φ₂: W →ₗ[k] V := C.constr k B
  have h1: φ ∘ φ₂ = id := by
    ext w
    simp only [Function.comp_apply, Basis.constr_apply_fintype, Basis.equivFun_apply, map_sum,
      map_smul, Basis.equivFun_self, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, id_eq]
    exact Basis.sum_repr C w
  have h2: φ₂ ∘ φ = id := by
    ext v
    simp only [Function.comp_apply, Basis.constr_apply_fintype, Basis.equivFun_apply, map_sum,
      map_smul, Basis.equivFun_self, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, id_eq]
    exact Basis.sum_repr B v
  constructor
  · exact Function.leftInverse_iff_comp.mpr h2
  · exact congrFun h1
  done

example (m s : ℕ) : ¬m < s → s ≤ m := by
  intro h
  exact Nat.not_lt.mp h

theorem finite_vector_spaces_have_the_same_dim_if_they_are_isomorphic {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V][FiniteDimensional k V] {W : Type} [AddCommGroup W] [Module k W][FiniteDimensional k W] (h: V ≃ₗ[k] W): finrank k V = finrank k W := by
  let m := finrank k V
  let s := finrank k W

  by_contra h2
  wlog hlt: m < s
  . cases' Ne.lt_or_lt h2 with h3 h3
    · contradiction
    · specialize this k V
      rw [Nat.not_lt] at hlt

      exact lt_of_le_of_ne h3 (Ne.symm h2)


  have B : Basis (Fin m) k V := by
    exact FiniteDimensional.finBasisOfFinrankEq k V rfl
  have C: Basis (Fin s) k W := by
    exact FiniteDimensional.finBasisOfFinrankEq k W rfl
  -- cases' h with φ φ2 left right
  -- simp [Function.leftInverse_iff_comp] at left
  -- simp [Function.rightInverse_iff_comp] at right
  let φ := LinearEquiv.bijective h
  cases' φ with φ1 φ2


  done
/-

theorem basisExistence

theorem OrthonormalBasisExistence :=

theorem subsetofOrthoBasisOrtho

theorem rank_nullity {K : Type} {V: Type v} {V₁ : Type v} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁] (f : V →ₗ[K] V₁): Module.rank K (LinearMap.range f) + Module.rank K (LinearMap.ker f) = Module.rank K V := by
  simpa using LinearMap.rank_range_add_rank_ker f



  done
-/
