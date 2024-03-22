import Mathlib.Tactic
import LeanCopilot
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.MvPolynomial.PDeriv
import Mathlib.RingTheory.Algebraic
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
open MvPolynomial

def AffineVariety {k : Type} [Field k] (f : MvPolynomial (Fin (n : ℕ)) k) := {v : (Fin n) → k | eval v f  = 0}

def union {f : MvPolynomial (Fin (n : ℕ)) ℂ} {g : MvPolynomial (Fin (n : ℕ)) ℂ}
    (_ : AffineVariety f) (_ : AffineVariety g) :=
    {v : (Fin n) → ℂ | eval v f  = 0} ∪ {v : (Fin n) → ℂ | eval v g  = 0}

def intersect {f : MvPolynomial (Fin (n : ℕ)) ℂ} {g : MvPolynomial (Fin (n : ℕ)) ℂ}
    (_ : AffineVariety f) (_ : AffineVariety g) :=
    {v : (Fin n) → ℂ | eval v f  = 0} ∩ {v : (Fin n) → ℂ | eval v g  = 0}

theorem mul_poly_union_variety (f g: MvPolynomial (Fin n) ℂ)
    {C₁ : AffineVariety f} {C₂ : AffineVariety g} : AffineVariety (f * g) =
    union C₁ C₂:= by
  ext v
  rw [AffineVariety]
  change v ∈ {v | (eval v) (f * g) = 0} ↔
    v ∈ {v : (Fin n) → ℂ | eval v f  = 0} ∪ {v : (Fin n) → ℂ | eval v g  = 0}
  rw [Set.mem_setOf_eq, map_mul, mul_eq_zero]
  rfl
  done

/--Extension of affine varieties to multiple polynomials-/
def AffineVariety' (σ : Fin (m : ℕ) → MvPolynomial (Fin (n : ℕ)) ℂ) :=
    {v : (Fin n) → ℂ | ∀ p : Fin m, eval v (σ p) = 0}

--wip fix hypotheis -
theorem mul_poly_intersect_variety (a b : Fin 2) (h : a ≠ b)
    (σ : Fin 2 → MvPolynomial (Fin n) ℂ) :
    AffineVariety' σ = {v : (Fin n) → ℂ | eval v (σ a)  = 0 ∧ eval v (σ b)  = 0} := by
  ext v
  rw [AffineVariety']
  rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · intro h
    constructor
    · exact h a
    · exact h b
  · rintro ⟨ha, hb⟩ p
    cases' eq_or_ne p a with hp hp
    · rw [hp, ha]
    · have h2 : Nat.card (Fin 2) = 2 := by
        rw [Nat.card_eq_fintype_card]
        rfl
      have h2 := (Nat.card_eq_two_iff' a).mp h2
      obtain ⟨b_, _,  hb2⟩ := h2
      have hp := hb2 p hp
      specialize hb2 b h.symm
      rw [hp, ←hb2]
      exact hb
  done

def singular_points (f : MvPolynomial (Fin (n : ℕ)) ℂ) :=
  {v ∈ AffineVariety f | ∀ i : (Fin n), eval v (pderiv i f) = 0}

class AffineVariety'' (f : MvPolynomial (Fin (n : ℕ)) ℂ) where
  points : (Fin n) → ℂ
  eval_0 : eval points f = 0
  singular_points : (Fin n) → ℂ
  singular_points_eval_0 : eval singular_points f = 0 ∧
    ∀ i : (Fin n), eval singular_points (pderiv i f) = 0

--def AffineVariety''.intersect {C₁ : AffineVariety f} {C₂ : AffineVariety g} :=

def AffineVariety''' (I : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ)) :=
  {v : (Fin n) → ℂ | ∀ p ∈ I, eval v p = 0}

def AffineVariety'''' {I : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ)} (p : I) :=
    {v : (Fin n) → ℂ | eval v p = 0}

def intersect' {I : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ)} {p q : I}
    (_ : AffineVariety'''' p) (_ : AffineVariety'''' q) :=
    {v : (Fin n) → ℂ | eval v p = 0} ∩ {v : (Fin n) → ℂ | eval v q = 0}

lemma p_in_I_implies_affineI_sub_affine_p (I : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ))
    (hp: p ∈ I) : AffineVariety''' I ≤ AffineVariety p := by
  intro v hv
  exact hv p hp
  done

theorem J_sub_I_implies_affine_I_sub_affine_J (I : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ))
    (J : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ)) (h: J ≤ I): AffineVariety''' I ≤ AffineVariety''' J := by
  intro v hv j hj
  exact hv j (h hj)
  done

theorem zariskis_lemma (K: Type) (A : Type) [Field K] [Field A] [Algebra K A]
    (h: Algebra.FiniteType K A): FiniteDimensional K A := by
  have h' := h
  rw [Algebra.FiniteType.iff_quotient_mvPolynomial''] at h
  obtain ⟨n, x, hi⟩ := h




lemma alg_ext_of_AlgClosed_bijects_base_field [Field K] [Field A] [Algebra K A]
    (h : Algebra.IsAlgebraic K A) (h2: IsAlgClosed K) : Function.Bijective (algebraMap K A) := by
    constructor
    · exact NoZeroSMulDivisors.algebraMap_injective K A
    · exact IsAlgClosed.algebraMap_surjective_of_isAlgebraic h
    done

lemma AffineVariety_1 (k : Type) [Field k] : AffineVariety (1 : (MvPolynomial (Fin (n : ℕ)) k)) = ∅ := by
  by_contra h2
  push_neg at h2
  cases' h2 with v0 hv
  have h1eq1: eval v0 1 = 1 := by refine RingHom.map_one (eval v0)
  change eval v0 1 = 0 at hv
  rw [h1eq1] at hv
  norm_num at hv
  done

lemma quot_mvPolynomial_ring_maxIdeal_bijects_base_field {k : Type} [Field k] [hAlgClosed : IsAlgClosed k]
    (m : Ideal (MvPolynomial (Fin n) k)) (_ : Ideal.IsMaximal m) :
    Function.Bijective (algebraMap k (MvPolynomial (Fin n) k ⧸ m)) := by
  let Rmodm := Ideal.Quotient.field m
  have _ := zariskis_lemma k (MvPolynomial (Fin n) k ⧸ m)
    (Algebra.FiniteType.trans (Algebra.FiniteType.mvPolynomial k (Fin n))
    (Module.Finite.finiteType (MvPolynomial (Fin n) k ⧸ m)))
  exact alg_ext_of_AlgClosed_bijects_base_field (Algebra.IsAlgebraic.of_finite k (MvPolynomial (Fin n) k ⧸ m)) hAlgClosed
  done

lemma mk_maps_polys_in_ideal_to_0 {k : Type} [Field k] (I : Ideal (MvPolynomial (Fin (n : ℕ)) k)) :
    ∀ f ∈ I, Ideal.Quotient.mk I f = 0 := by
  intro f hf
  have h: Ideal.Quotient.mk I f = Ideal.Quotient.mk I (0 : MvPolynomial (Fin n) k) := by
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    ring_nf
    exact hf
  rw [h]
  rfl
  done

lemma nonempty_le_nonempty {X : Type} {A B : Set X} (h : B ≤ A) (h2 : B ≠ ∅) : A ≠ ∅ := by
  rw [←Set.nonempty_iff_ne_empty] at *
  cases' h2 with b h2
  specialize h h2
  constructor
  exact h


theorem weak_nullstellensatz (I : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ)) : 1 ∈ I ↔
    AffineVariety''' I = ∅ := by
  constructor
  · intro h
    have h3 : AffineVariety''' I ≤ ∅ := by
      rw [←AffineVariety_1 ℂ]
      exact p_in_I_implies_affineI_sub_affine_p I h
    exact Set.subset_eq_empty h3 rfl
  · intro h
    by_contra hnin
    obtain ⟨m, ⟨hmaximal, hIsubm⟩⟩ := Ideal.exists_le_maximal I ((Ideal.ne_top_iff_one I).mpr hnin)
    let Rmodm := Ideal.Quotient.field m
    let φ := Ideal.Quotient.mk m
    let π := RingEquiv.ofBijective (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ m))
      (quot_mvPolynomial_ring_maxIdeal_bijects_base_field m hmaximal)

    let π' := RingEquiv.symm π
    let π'φ := RingHom.comp (RingEquiv.toRingHom π') φ

    have h10 : ∀ f ∈ m, π'φ f = 0 := by
      intro f hf
      change π' (φ f) = 0
      rw [(mk_maps_polys_in_ideal_to_0 m) f hf]
      exact RingEquiv.map_zero π'

    let φ_mono : Fin n → ℂ := fun (i : Fin n) ↦ π'φ (X i)

    have h11 : eval φ_mono = π'φ := by
      ext x
      swap
      · rw [eval_X]
      · change (eval φ_mono) (C x) = π'φ (C x)
        rw [eval_C]
        change x = (π' (φ (C x)))
        sorry

    have h12 : AffineVariety''' m ≠ ∅ := by
      push_neg
      constructor
      intro f hf
      rw [h11, h10 f hf]

    apply nonempty_le_nonempty
      (J_sub_I_implies_affine_I_sub_affine_J m I hIsubm) h12
    exact h

  done
