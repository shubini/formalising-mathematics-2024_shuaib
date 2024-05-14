import Mathlib.Tactic
import LeanCopilot
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.MvPolynomial.PDeriv
import Mathlib.RingTheory.Algebraic
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.MvPolynomial
import Mathlib.RingTheory.Jacobson

open MvPolynomial

/-!
# Project 3
In this project I define and prove some results from the third year course Algebraic Curves.
I start by defining affine varities and proving some basic results about them, and then I prove
the weak version of the Nullstellensatz, which was given without proof in the course.

## Main definitions
* `AffineVariety`, `AffineVariety'` and `AffineVariety''` are definitions of affine varities of
  single polynomials, sets of polynomials and ideals of polynomial rings respectively. These are
  implemented as sets of the type `Fin n → k`, where k is the field, on which the polynomial
  evaluates to 0.

## Main statements
* `weak_nullstellensatz` states that an affine variety of an ideal of a polynomial ring over
  an algebraically closed field is empty iff 1 is in the ideal.
-/

/--Definition of an affine variety of a multivariate polynomial f - the set of valuations v from
(Fin n) → k that evaluate to 0 under f.-/
def AffineVariety {k : Type} [Field k] (f : MvPolynomial (Fin (n : ℕ)) k) :=
  {v : (Fin n) → k | eval v f  = 0}

/--Definition of the union of affine varieties of multivariate polynomials f and g - the union of
the affine varities of f and g as sets.-/
def union {k : Type} [Field k] {f : MvPolynomial (Fin (n : ℕ)) k} {g : MvPolynomial (Fin (n : ℕ)) k}
    (_ : AffineVariety f) (_ : AffineVariety g) :=
  {v : (Fin n) → k | eval v f  = 0} ∪ {v : (Fin n) → k | eval v g  = 0}

/--Definition of the intersection of affine varieties of multivariate polynomials f and g -
the intersection of the affine varities of f and g as sets.-/
def intersect {k : Type} [Field k] {f : MvPolynomial (Fin (n : ℕ)) k} {g : MvPolynomial (Fin (n : ℕ)) k}
    (_ : AffineVariety f) (_ : AffineVariety g) :=
  {v : (Fin n) → k | eval v f  = 0} ∩ {v : (Fin n) → k | eval v g  = 0}

/--The union of affine varieties of multivariate polynomials f and g is equal to the affine
variety of the polynomial f * g.-/
theorem mul_poly_union_variety {k : Type} [Field k] (f g: MvPolynomial (Fin n) k)
    {C₁ : AffineVariety f} {C₂ : AffineVariety g} : AffineVariety (f * g) =
    union C₁ C₂:= by
  ext v
  rw [AffineVariety, Set.mem_setOf_eq, map_mul, mul_eq_zero]
  rfl
  done

/--Extension of definition affine varieties to sets of multiple multivariate polynomials - Given a
set of multivariate polynomials in n variables indexed by Fin m, the affine variety of this set is
the set of valuations Fin n → k, that evaluate to 0 under every polynomial in the set.-/
def AffineVariety' {k : Type} [Field k] (σ : Fin (m : ℕ) → MvPolynomial (Fin (n : ℕ)) k) :=
    {v : (Fin n) → k | ∀ p : Fin m, eval v (σ p) = 0}

/--The intersection of affine varieties of multivariate polynomials σ a and σ b is equal to the
affine variety of the set of polynomials {σ a, σ b}, indexed by Fin 2.-/
theorem mul_poly_intersect_variety {k : Type} [Field k] (a b : Fin 2) (h : a ≠ b)
    (σ : Fin 2 → MvPolynomial (Fin n) k) {C₁ : AffineVariety (σ a)} {C₂ : AffineVariety (σ b)}:
    AffineVariety' σ = intersect C₁ C₂:= by
  ext v
  rw [AffineVariety', Set.mem_setOf_eq]
  constructor
  · -- This side is simple, we use constructor to split cases, and both cases are true
    -- as and b are members of Fin 2
    intro h
    constructor
    · exact h a
    · exact h b
  · rintro ⟨ha, hb⟩ p
    -- In this case, we argue that a value p ∈ Fin 2 is either a or not a
    cases' eq_or_ne p a with hp hp
    · -- The p = a case is easy as we have ha
      rw [hp, ha]
    · -- We need that the (Nat) cardinality of Fin 2 is 2
      have h2 : Nat.card (Fin 2) = 2 := by
        rw [Nat.card_eq_fintype_card]
        rfl
      -- This lemma states that there is a unique non a value of Fin 2
      have h2 := (Nat.card_eq_two_iff' a).mp h2
      -- We call this value b_
      obtain ⟨b_, _,  hb2⟩ := h2
      -- We have p = b_ by uniqueness, and then b_ = b by uniqueness, so p = b, then use hb
      rw [hb2 p hp, ←hb2 b h.symm]
      exact hb
  done

/--Definition of singular points of an affine variety of f - the points of an affine variety which
evaluate all first order partial derivatives of f to zero.-/
def singular_points {k : Type} [Field k] (f : MvPolynomial (Fin (n : ℕ)) k) :=
  {v ∈ AffineVariety f | ∀ i : (Fin n), eval v (pderiv i f) = 0}

/--Extension of definition affine varieties to ideals of multivariate polynomials (as a ring)
- Given an ideal of multivariate polynomials, the affine variety of this set is
the set of valuations Fin n → k, that evaluate to 0 under every polynomial in the ideal.-/
def AffineVariety'' {k : Type} [Field k] (I : Ideal (MvPolynomial (Fin (n : ℕ)) k)) :=
  {v : (Fin n) → k | ∀ p ∈ I, eval v p = 0}

/--If a polynomial p is contained in an ideal I, the affine variety of I is contained in the
affine variety of p.-/
lemma p_in_I_implies_affineI_sub_affine_p {k : Type} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) {p : MvPolynomial (Fin n) k} (hp: p ∈ I) :
    AffineVariety'' I ≤ AffineVariety p := by
  intro v hv
  exact hv p hp
  done

/--For ideals I, J of the ring of multivariate polynomials in n variables, if J is contained
in I, the affine variety of I is contained in the affine variety of J.-/
lemma J_sub_I_implies_affine_I_sub_affine_J {k : Type} [Field k]
    (I : Ideal (MvPolynomial (Fin (n : ℕ)) k)) (J : Ideal (MvPolynomial (Fin (n : ℕ)) k))
    (h: J ≤ I) : AffineVariety'' I ≤ AffineVariety'' J := by
  intro v hv j hj
  exact hv j (h hj)
  done

/--The affine variety of 1 (as a multivariate polynomial) is the empty set.-/
lemma AffineVariety_1 (k : Type) [Field k] :
    AffineVariety (1 : (MvPolynomial (Fin (n : ℕ)) k)) = ∅ := by
  -- Assuming that this affine variety is nonempty, pushing the negative inwards
  by_contra h2
  push_neg at h2
  -- Attain a valuation in the affine set
  cases' h2 with v0 hv

  -- This valuation must map under 1 to 1 (as eval v0 is a ring homo) and map under 1 to 0,
  -- as it is inside the affine variety
  have h1eq1: eval v0 1 = 1 := by refine RingHom.map_one (eval v0)
  change eval v0 1 = 0 at hv
  rw [h1eq1] at hv
  -- this implies 1 = 0, which is False
  norm_num at hv
  done

/--The mapping k to a quotient ring of multivariate polynomials by a maximal ideal m, given by
(Ideal.Quotient.mk m) composed with C, is bijective.-/
lemma quot_mvPolynomial_ring_maxIdeal_comp_C_bijective {k : Type} [Field k] [IsAlgClosed k]
    (m : Ideal (MvPolynomial (Fin n) k)) (_ : Ideal.IsMaximal m) :
    Function.Bijective ((Ideal.Quotient.mk m).comp C) := by
  -- I won't use this instance by name so I use letI instead to inline it
  letI := Ideal.Quotient.field m
  -- Breaking bijection into injective and surjective cases
  constructor
  · -- This is true since ring homorphisms are injective if the domain is a division ring
    -- (and fields are division rings)
    exact RingHom.injective (RingHom.comp (Ideal.Quotient.mk m) C)
  · -- This is a big jump. IsAlgClosed.algebraMap_surjective_of_isIntegral' says that integral
    -- ring homomorphisms on algebraically closed fields are surjective. We have that the
    -- homorphism is integral from Ideal.MvPolynomial.comp_C_integral_of_surjective_of_jacobson,
    -- which states that on a Jacobson ring, the composition of a surjective maps with C is
    -- integral, and we finally have that the quotient map is surjective
    exact IsAlgClosed.algebraMap_surjective_of_isIntegral' ((Ideal.Quotient.mk m).comp C)
      (Ideal.MvPolynomial.comp_C_integral_of_surjective_of_jacobson _ Ideal.Quotient.mk_surjective)
  done

/--The quotient map (Ideal.Quotient.mk I) maps elements of I to zero.-/
lemma mk_maps_polys_in_ideal_to_0 {k : Type} [Field k] (I : Ideal (MvPolynomial (Fin (n : ℕ)) k)):
    ∀ f ∈ I, Ideal.Quotient.mk I f = 0 := by
  intro f hf
  -- Elements of an ideal map to the same thing that zero maps to under the quotient map
  have h: Ideal.Quotient.mk I f = Ideal.Quotient.mk I (0 : MvPolynomial (Fin n) k) := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    ring_nf
    exact hf
  rw [h]
  rfl
  done

/--If B is a subset of A and is nonempty, A is nonempty.-/
lemma subset_nonempty_implies_nonempty {X : Type} {A B : Set X} (h : B ≤ A) (h2 : B ≠ ∅)
    : A ≠ ∅ := by
  rw [←Set.nonempty_iff_ne_empty] at *
  cases' h2 with b h2
  specialize h h2
  constructor
  exact h
  done

/--For an ideal I of polynomials in n variables over an algebraically closed field, the weak
nullstellensatz states that 1 is in I if and only if the affine variety of I is empty-/
theorem weak_nullstellensatz {k : Type} [Field k] [IsAlgClosed k]
    (I : Ideal (MvPolynomial (Fin (n : ℕ)) k)) : 1 ∈ I ↔ AffineVariety'' I = ∅ := by
  constructor
  · intro h
    -- have that affine variety of I is subset of empty set, so must be empty
    have hltempty : AffineVariety'' I ≤ ∅ := by
      -- Affine Variety I is subset of Affine Variety 1, which is empty
      rw [←AffineVariety_1 k]
      exact p_in_I_implies_affineI_sub_affine_p I h
    exact Set.subset_eq_empty hltempty rfl
  · intro h
    -- This is a proof by contradiction - showing
    -- if I is a proper ideal, then its affine variety is nonempty
    by_contra hnin
    -- We use Krull's theorem to obtain a maximal ideal that I is contained in
    obtain ⟨m, ⟨hmaximal, hIsubm⟩⟩ := Ideal.exists_le_maximal I ((Ideal.ne_top_iff_one I).mpr hnin)

    -- I won't use this instance by name so I use letI instead to inline it
    letI := Ideal.Quotient.field m

    -- Construct a ring equiv φ and its inverse (φ') from k to MvPolynomial (Fin n) k ⧸ m
    let φ := RingEquiv.ofBijective ((Ideal.Quotient.mk m).comp C)
      (quot_mvPolynomial_ring_maxIdeal_comp_C_bijective m hmaximal)
    let φ' := RingEquiv.symm φ

    -- Inverse composed with φ equals identity on k
    have φ'φ_is_id : (RingHom.comp (RingEquiv.symm φ).toRingHom φ) = RingHom.id _ :=
      RingEquiv.symm_comp φ

    -- Define a ring hom MvPolynomial (Fin n) k →+* k by φ' composed with the quotient map
    let φ'mk := RingHom.comp φ'.toRingHom (Ideal.Quotient.mk m)

    -- and show it maps all elements of the ideal to 0
    have h10 : ∀ f ∈ m, φ'mk f = 0 := by
      change ∀ f ∈ m, φ' ((Ideal.Quotient.mk m) f) = 0
      intro f hf
      -- apply lemma proved before, and that ring equivs preserve zeros
      rw [(mk_maps_polys_in_ideal_to_0 m) f hf, RingEquiv.map_zero]

    -- define a valuation which equals each monomial mapped under φ'mk
    let X_mapped : Fin n → k := fun (i : Fin n) ↦ φ'mk (X i)

    -- Proof that the map MvPolynomial σ R →+* R which evaluates
    -- a polynomial at X_mapped is equal to φ'mk
    have ext_φ'mk : eval X_mapped = φ'mk := by
      ext x
      -- Ext creates two cases, that these mappings have the same value for a value x ∈ k,
      -- then that they have the same value for a degree 1 monomial X x, x ∈ Fin n
      · -- Rewrite in a way that allows application of lemmas
        change (eval X_mapped) (C x) = (RingHom.comp φ'.toRingHom φ) x
        rw [eval_C, φ'φ_is_id]
        rfl
      · -- Rewrite LHS to X_mapped x, which equals RHS by definition
        rw [eval_X]

    -- This gives us a valuation inside AffineVariety'' m, which proves this set nonempty
    have nonempty_variety : AffineVariety'' m ≠ ∅ := by
      push_neg
      constructor
      intro f hf
      rw [ext_φ'mk, h10 f hf]

    -- We now have AffineVariety'' m ≤ AffineVariety'' I, so AffineVariety'' I is nonempty
    -- This breaks our assumption from the start
    apply subset_nonempty_implies_nonempty
      (J_sub_I_implies_affine_I_sub_affine_J m I hIsubm) nonempty_variety
    exact h
  done

/-- The product of two non-zero polynomials has degree eq to sum of degrees-/
lemma degree_mul_non_zero {k : Type} [Field k] {p q : MvPolynomial (Fin (n : ℕ)) k}
    (hp : p ≠ 0) (hq : q ≠ 0): totalDegree (p * q) = totalDegree p + totalDegree q :=
  sorry

/-- A polynomial is irreducible if wherever it can written as the product of two polynomials
one of them is constant. -/
def irreducible {k : Type} [Field k] (f : MvPolynomial (Fin (n : ℕ)) k) :=
  ∀ (g h : MvPolynomial (Fin (n : ℕ)) k), f = g * h → totalDegree g = 0 ∨ totalDegree h = 0

/-- All monomials X i are irreducible. -/
lemma is_irreducible {k : Type} [Field k] :
    ∀ i : Fin n, irreducible ((X i) : MvPolynomial (Fin n) k) := by
  intro i g r h
  cases' eq_or_ne g 0 with hg hg
  · -- rw so 1 = 0
    rw [hg, zero_mul, X, monomial_eq_zero] at h
    exfalso
    norm_num at h

  · cases' eq_or_ne r 0 with hr hr
    · --same as case above
      rw [hr, mul_zero, X, monomial_eq_zero] at h
      exfalso
      norm_num at h
    · -- argue on basis of degree of polynomials
      have hdeg : totalDegree (X i) = totalDegree (g * r) := congrArg totalDegree h
      have hdeg2 : totalDegree g + MvPolynomial.totalDegree r = totalDegree (g * r) :=
        (degree_mul_non_zero hg hr).symm
      rw [←hdeg, totalDegree_X] at hdeg2
      --assume both g and r have degree greater or equal to than 1
      by_contra h0
      --push_neg to get a
      push_neg at h0
      cases' h0 with hg hr
      -- two natural numbers must sum to more than 1
      have hcon : 1 < totalDegree g + totalDegree r := by
        have hg : 0 < totalDegree g := Nat.pos_of_ne_zero hg
        have hr : 1 ≤ totalDegree r := Nat.pos_of_ne_zero hr
        exact lt_add_of_pos_of_le hg hr
      rw [hdeg2] at hcon
      -- linarith solves contraidiction
      linarith
  done
