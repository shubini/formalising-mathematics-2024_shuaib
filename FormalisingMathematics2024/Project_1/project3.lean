import Mathlib.Tactic
import LeanCopilot
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.MvPolynomial.PDeriv
import Mathlib.RingTheory.Algebraic
import Mathlib.Analysis.Complex.Polynomial
import Mathlib.FieldTheory.IsAlgClosed.Basic
open MvPolynomial

def AffineVariety (f : MvPolynomial (Fin (n : ℕ)) ℂ) := {v : (Fin n) → ℂ | eval v f  = 0}

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
    · specialize h a
      exact h
    · specialize h b
      exact h
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
    (hp: p ∈ I): AffineVariety''' I ≤ AffineVariety p := by
  intro v hv
  exact hv p hp
  done

theorem J_sub_I_implies_affine_I_sub_affine_J (I : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ))
    (J : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ)) (h: J ≤ I): AffineVariety''' I ≤ AffineVariety''' J := by
  intro v hv j hj
  exact hv j (h hj)
  done

theorem zariskis_lemma (K: Type) (A : Type) [Field K] [Field A] [Algebra K A] (h: Algebra.FiniteType K A): FiniteDimensional K A := by
  sorry

lemma alg_ext_of_AlgClosed_is_AlgClosure [Field K] [Field A] [Algebra K A]
    (h : Algebra.IsAlgebraic K A) (h2: IsAlgClosed K) : Function.Bijective (algebraMap K A) := by
    constructor
    · exact NoZeroSMulDivisors.algebraMap_injective K A
    · exact IsAlgClosed.algebraMap_surjective_of_isAlgebraic h
    done

theorem weak_nullstellensatz (I : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ)) : 1 ∈ I ↔
    AffineVariety''' I = ∅ := by
  constructor
  · rintro h
    by_contra h2
    push_neg at h2
    cases' h2 with v0 hv
    have h1eq1: eval v0 1 = 1 := by refine RingHom.map_one (eval v0)
    specialize hv (1 : MvPolynomial (Fin (n : ℕ)) ℂ) h
    rw [h1eq1] at hv
    norm_num at hv
  · intro h
    by_contra hnin
    obtain ⟨m, ⟨hmaximal, hIsubm⟩⟩ := Ideal.exists_le_maximal I ((Ideal.ne_top_iff_one I).mpr hnin)
    let Rmodm := Ideal.Quotient.field m
    let π := Ideal.Quotient.mk m
    let alg_m := RingHom.toAlgebra (Ideal.Quotient.mk m)
    have h2 : Algebra.FiniteType (MvPolynomial (Fin n) ℂ) (MvPolynomial (Fin n) ℂ ⧸ m) :=
      Module.Finite.finiteType (MvPolynomial (Fin n) ℂ ⧸ m)
    have h3 := Algebra.FiniteType.mvPolynomial ℂ (Fin n)
    have h4 := Algebra.FiniteType.trans h3 h2
    have h5 : FiniteDimensional ℂ (MvPolynomial (Fin n) ℂ ⧸ m) := by
      exact zariskis_lemma ℂ (MvPolynomial (Fin n) ℂ ⧸ m) h4
    have h6 := Algebra.IsAlgebraic.of_finite ℂ (MvPolynomial (Fin n) ℂ ⧸ m)

      --isAlgClosure_iff
    have h8a : Algebra.IsAlgebraic ℂ ℂ := by exact Normal.isAlgebraic'
    have h8 := (isAlgClosure_iff ℂ ℂ).2 ⟨Complex.isAlgClosed, h8a⟩
    have h7 : Function.Bijective (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ m)) := by
      exact alg_ext_of_AlgClosed_is_AlgClosure h6 Complex.isAlgClosed
    let φ := RingEquiv.ofBijective (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ m)) h7

    have h9 : ∀ f ∈ m, Ideal.Quotient.mk m f = Ideal.Quotient.mk m 0:= by
      intro f hf
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      ring_nf
      exact hf

    --have h10 : ∀ v : (Fin n) → ℂ, ∀ f ∈ m, eval v



  done
