import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional
import LeanCopilot
import Mathlib.LinearAlgebra.Isomorphisms

open FiniteDimensional
variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V][FiniteDimensional k V]


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

theorem finite_vector_spaces_are_isomorphic_if_they_have_the_same_dim {n : ℕ} {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V][FiniteDimensional k V] {W : Type} [AddCommGroup W] [Module k W][FiniteDimensional k W] (hV: finrank k V = n) (hW: finrank k W = n) : V ≃ₗ[k] W := by
  have B : Basis (Fin n) k V := by
    exact FiniteDimensional.finBasisOfFinrankEq k V hV
  have C : Basis (Fin n) k W := by
    exact FiniteDimensional.finBasisOfFinrankEq k W hW

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
  · refine Function.leftInverse_iff_comp.mpr h2
  · exact congrFun h1







/-

theorem basisExistence

theorem OrthonormalBasisExistence :=

theorem subsetofOrthoBasisOrtho

theorem rank_nullity {K : Type} {V: Type v} {V₁ : Type v} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁] (f : V →ₗ[K] V₁): Module.rank K (LinearMap.range f) + Module.rank K (LinearMap.ker f) = Module.rank K V := by
  simpa using LinearMap.rank_range_add_rank_ker f



  done
-/
