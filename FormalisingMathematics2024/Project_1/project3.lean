import Mathlib.Tactic
import LeanCopilot
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.MvPolynomial.PDeriv
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
  {v : (Fin n) → ℂ | ∀ p : I, eval v p = 0}

def AffineVariety'''' {I : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ)} (p : I) :=
    {v : (Fin n) → ℂ | eval v p = 0}

def intersect' {I : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ)} {p q : I}
    (_ : AffineVariety'''' p) (_ : AffineVariety'''' q) :=
    {v : (Fin n) → ℂ | eval v p = 0} ∩ {v : (Fin n) → ℂ | eval v q = 0}


theorem (I : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ)) (J : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ))

theorem weak_nullstellensatz (I : Ideal (MvPolynomial (Fin (n : ℕ)) ℂ)) : 1 ∈ I ↔
    AffineVariety''' I = ∅ := by
  constructor
  · rintro h
    change {v : (Fin n) → ℂ | ∀ p : I, eval v p = 0} = ∅
    have h1 : {v | (eval v) 1 = 0} = ∅ := by
      by_contra h0
      push_neg at h0
      cases' h0 with v0 hv
      have h02: (eval v0) 1 = 1 := by refine RingHom.map_one (eval v0)
      change (eval v0) 1 = 0 at hv
      rw [hv] at h02
      · norm_num at h02
      · exact ℤ
    by_contra h2
    push_neg at h2
    cases' h2 with v0 hv
    have h1eq1: (eval v0) 1 = 1 := by refine RingHom.map_one (eval v0)
    change ∀ (p : I), (eval v0) p = 0 at hv
    specialize hv (1 : ↥I)



  · intro h
  done
