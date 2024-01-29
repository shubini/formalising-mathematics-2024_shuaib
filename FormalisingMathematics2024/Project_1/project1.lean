import Mathlib.Tactic
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Isomorphisms
open FiniteDimensional
variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- This is generalisation of the question from sheet 2 of the vector space materials - If A and B are subspaces of a finite
dimensional vector space V and the sum of the dimensions of A and B is greater than the dimension of V, the intersection of A and
B can't be empty.-/
lemma inter_non_empty_if_sum_of_dim_greater_than_dim_of_space {A B : Subspace k V} (n m1 m2 : ℕ)
    (hV : FiniteDimensional.finrank k V = n) (hA : FiniteDimensional.finrank k A = m1) (hB : FiniteDimensional.finrank k B = m2)
    (hS: m1 + m2 > n) : A ⊓ B ≠ ⊥ := by
  --changes goal to False, adds hypothesis h
  intro h
  -- Use dim (A ⊔ B) + dim (A ⊓ B) = dim A + dim B and that dim (A ⊔ B) < dim V
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq A B
  have h3 := Submodule.finrank_le (A ⊔ B)
  -- after rewriting and simplifying we are left with h3: m1 + m2 ≤ n
  rw [hV] at h3
  rw [h, hA, hB, finrank_bot k V] at h2
  norm_num at h2
  rw [h2] at h3
  --linarith finds the contradiction between h3 and hS and closes the goal
  linarith
  done

/-- This lemma is that if V and W are vector spaces over the same field with the same dimension, they are isomorphic to each other.-/
lemma fvs_are_iso_if_they_have_the_same_dim {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W](hn: finrank k V = finrank k W) : V ≃ₗ[k] W := by
  let n := finrank k V
  -- use the dimension of V and W to create bases for V and W
  have B : Basis (Fin n) k V := by
    exact finBasisOfFinrankEq k V rfl
  have C : Basis (Fin n) k W := by
    exact finBasisOfFinrankEq k W (by rw [←hn])
  -- Since bases in Lean are functions from an indexing set to a vector space, we can use Basis.constr to create a linear mapping
  -- that maps B i to C i and one that maps C i to B i
  let φ : V →ₗ[k] W := B.constr k C
  let φ₂: W →ₗ[k] V := C.constr k B
  --Composing maps gives identity from W → W and V → V
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
  --This means that φ₂ is the left and right inverse of φ, which shows that φ is a linear equivalence
  constructor
  · exact Function.leftInverse_iff_comp.mpr h2
  · exact Function.rightInverse_iff_comp.mpr h1
  done

/--Other direction if V and W are isomorphic to each other, they are of the same dimension.-/
lemma fvs_have_the_same_dim_if_they_are_iso {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] (φ: V ≃ₗ[k] W) : finrank k V = finrank k W := by
  let n := finrank k V
  -- use the dimension of V to create basis for V
  have B : Basis (Fin n) k V := by
    exact finBasisOfFinrankEq k V rfl
  -- by applying linear equivalenceφ, get a basis of W
  have C : Basis (Fin n) k W := by
    exact B.map φ
  --these bases are indexed by the same set, so we can show they have the same size
  have h2: finrank k W = n := by
    rw [finrank_eq_card_basis C]
    exact Fintype.card_fin n
  change finrank k W = finrank k V at h2
  exact h2.symm
  done

/--Rank nullity theorem - The sum of the rank and nullity of a linear map equals the dimension of the domain. This is the proof
in mathlib for the more general case with ranks instead of finranks.-/
theorem rank_nullity {V₁ : Type} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁] (φ : V →ₗ[k] V₁): finrank k (LinearMap.range φ)
    + finrank k (LinearMap.ker φ) = finrank k V := by
  -- first iso theorem
  have h: (V ⧸ LinearMap.ker φ) ≃ₗ[k] ↥(LinearMap.range φ) := by
    exact φ.quotKerEquivRange
  -- use lemma that iso vector spaces have the same dimension
  have h2 : finrank k (LinearMap.range φ) = finrank k (V ⧸ LinearMap.ker φ):= by
    exact (fvs_have_the_same_dim_if_they_are_iso h).symm
  rw [h2]
  -- finally, use dim (V/N) + dim (N) = dim(V)
  exact Submodule.finrank_quotient_add_finrank (LinearMap.ker φ)
  done

/--Two bases of a finite dimensional vector space are (indexed by sets that are) the same size-/
lemma bases_of_fd_vector_space_are_same_size {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W] [Fintype I] [Fintype J] (B : Basis I k V)
    (C : Basis J k V): Fintype.card I = Fintype.card J := by
  let n := finrank k V
  -- the size of each basis is the dimesion of the vector space, which makes this result quite simple to prove
  have hi : Fintype.card I = n := by
    rw [←finrank_eq_card_basis B]
  have hj : Fintype.card J = n := by
    rw [←finrank_eq_card_basis C]
  rw [hi, hj]
  done

/--Given a subspace W of a vector space V, there exists a subspace U such that W ⨁ U = V-/
theorem exists_a_subspace_directsum {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (W : Subspace k V) : ∃(U: Subspace k V), Sum W U = V := by
  let n := finrank k V
  let m := finrank k W
  -- construct bases for V and W
  have h: m ≤ n := by
    exact Submodule.finrank_le W
  have B: Basis (Fin n) k V := by
    exact finBasisOfFinrankEq k V rfl
  have C: Basis (Fin m) k W := by
    exact finBasisOfFinrankEq k W rfl
  --split h into two cases m < n and m = n
  rw [@Nat.le_iff_lt_or_eq] at h
  cases' h with h h
  swap -- do equality case first
  · use (⊥: Submodule k V) -- use the 0 dimensional subspace
    have h1: V ≃ₗ[k] W := by
      change finrank k W = finrank k V at h
      exact fvs_are_iso_if_they_have_the_same_dim h.symm
    -- I wanted to try and use this to claim W = V but I don't know how to prove equality for vector spaces, and V and W are
    -- different types so I cant use W ≤ V ∧ V ≤ W
    sorry
  · -- use (Subspace.orthogonal W)
    -- for this case, I think the way it's generally done is by taking a basis of W, adding vectors to it to a basis of V and then
    --taking U to be the space generated by those vectors added. I don't know how to do this now.
    sorry
  done

/-- This theorem states that if a set of vectors that spans V is larger than a basis, that set can't be linearly independent.-/
theorem larger_span_set_than_basis_must_be_lin_dependent {k : Type} [Field k] {V : Type} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {ι ι₁: Type*} [Fintype ι] [Fintype ι₁] (B : Basis ι k V) (c : ι₁ → V)
    (hnm : Fintype.card ι < Fintype.card ι₁) (spans : ⊤ ≤ Submodule.span k (Set.range c)): ¬(LinearIndependent k c) := by
  intro h --gives us goal of false w/ hypothesis of LinearIndependent k c
  --Show that the size of the basis is the dimesion of the span of the set of vectors
  have h2: Fintype.card ι = Set.finrank k (Set.range c) := by
    rw [←FiniteDimensional.finrank_eq_card_basis B]
    --First have that the span of vectors has ≤ dimension than ambient space
    have h4: finrank k (Submodule.span k (Set.range c)) ≤ finrank k V := by
      exact Submodule.finrank_le (Submodule.span k (Set.range c))
    --Then show that ambient space has lower dimension than the span of vectors
    have h5: finrank k V ≤ finrank k (Submodule.span k (Set.range c)) := by
      have h6 : finrank k (⊤ : Submodule k V) ≤ finrank k (Submodule.span k (Set.range c)) := by
        exact Submodule.finrank_le_finrank_of_le spans
      simp at h6
      exact h6
    exact le_antisymm h5 h4
  --Show that cardinality of the set of vectors is the same as the dimension of ambient space
  have h3: Fintype.card ι₁ = Fintype.card ι := by
    rw [h2]
    change Fintype.card ι₁ = (Set.range c).finrank k
    exact linearIndependent_iff_card_eq_finrank_span.mp h
  --We have that the set was larger than the dimension of the vector space
  rw [h3] at hnm
  exact lt_irrefl _  hnm
  done
-/
