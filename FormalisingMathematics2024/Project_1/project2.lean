import Mathlib.Tactic
import LeanCopilot
import Mathlib.SetTheory.Cardinal.Finite
open AddGroup
open QuotientGroup
open CategoryTheory
open MulOpposite

/-
TO DO

GROUPS AND RINGS PROBLEM SHEET 1

Q1
Q2A
Q3
Q5
Q6
Q7

GROUPS AND RINGS PROBLEM SHEET 2 Q9

GROUPS AND RINGS MIDTERM Q1 -- done

CANT FIND BUT -- GROUP THEORY PROVE ANY INDEX 3 SUBGROUP OF AN ODD ORDER GROUP IS NORMAL

-/

-- MIDTERM Q1
variable (G : Type) [Group G]  (H K : Subgroup G)
variable {G H} {x : G}

variable {y z : G}

theorem centralizer.one_mem : (1 : G) ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h} := by
  rintro h _
  group
  done

theorem centralizer.inv_mem (hy : y ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h}) :
    y⁻¹ ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h} := by
  intro h hh
  specialize hy h hh
  rw [hy.symm]
  group at *
  exact hy.symm
  done

theorem centralizer.mul_mem (hy : y ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h})
    (hz : z ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h}) :
    y * z ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h} := by
  intro h hh
  specialize hy h hh
  specialize hz h hh
  rw [mul_inv_rev, ←mul_assoc]
  have hyz : y * z * h * z⁻¹ = y * (z * h * z⁻¹) := by group
  rw [hyz, hz, hy]
  done

def centralizer (H : Subgroup G) : Subgroup G
    where
  carrier := {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h}
  one_mem' := centralizer.one_mem
  inv_mem' := centralizer.inv_mem
  mul_mem' := centralizer.mul_mem

lemma cent_of_normal_is_normal (H : Subgroup G) [H_norm : H.Normal]: (centralizer H).Normal:= by
  constructor
  intro n hn g h hh
  rw [show g * n * g⁻¹ * h * (g * n * g⁻¹)⁻¹ = g * (n * (g⁻¹ * h * g) * n⁻¹) * g⁻¹ by group]
  have h2 : (g⁻¹ * h * g) ∈ H := by
    rw [show (g⁻¹ * h * g) = (g⁻¹ * h * g⁻¹⁻¹) by group]
    exact Subgroup.Normal.conj_mem H_norm h hh g⁻¹
  specialize hn (g⁻¹ * h * g) h2
  rw [hn]
  group
  done

def center := centralizer (⊤ : Subgroup G)
theorem subofCentreNormal (H : Subgroup G) (hSub: H ≤ center) :  ∀ n, n ∈
    H → ∀ g : G, g * n * g⁻¹ ∈ H:= by
  intro h hh g
  specialize hSub hh g (Subgroup.mem_top g)
  rw [←eq_mul_of_mul_inv_eq hSub, mul_assoc, mul_inv_self g, mul_one]
  exact hh
  done

-- PS1
/-
theorem autgroupofZ [Z : AddGroup ℤ] {AutZ : Group (AddGroup ℤ ≃+ AddGroup ℤ)} (H : Subgroup G)
      (c2 : (AddGroup.IsAddCyclic H) ∧ (Nat.card H = 2)):
    ∃φ, (φ : AutZ →* H):= by

  done
-/
--q3
lemma card2sethastwoelements {X: Type} (x y z : X) (h: Nat.card X = 2) (hxy: x≠y): z = x ∨ z = y
    := by
  have h2 := (Nat.card_eq_two_iff' x).mp h
  have h3 := (Nat.card_eq_two_iff' y).mp h
  obtain ⟨y_, ⟨_, h2_2⟩⟩ := h2
  obtain ⟨x_, ⟨_, h3_2⟩⟩ := h3
  have hx: x = x_ := by
    specialize h3_2 x hxy
    exact h3_2
  have hy: y = y_ := by
    specialize h2_2 y hxy.symm
    exact h2_2
  rw [←hy] at h2_2
  rw [←hx] at h3_2
  cases' eq_or_ne z x with hxz hxz
  · left; exact hxz
  · right
    specialize h2_2 z hxz
    exact h2_2
  done


open scoped Pointwise
theorem index2subgroupNormal [Group G] (H: Subgroup G) (ind: Subgroup.index H = 2) : H.Normal:= by
  have h2: ∀g : G, g • (H : Set G) = op g • H := by
    intro g
    cases' em (g ∈ H) with hginH hgninH
    · rw [leftCoset_mem_leftCoset H hginH, rightCoset_mem_rightCoset H hginH]
    · let π := (QuotientGroup.mk : G → G ⧸ H)
      let x := π (1:G)
      have hHT : H ≠ ⊤ := by
        intro hInd
        rw [←Subgroup.index_eq_one, ind] at hInd
        contradiction
      let y := π g
      have hxneqy : x ≠ y := by
        by_contra hxeqy

      have hxy : ∀ t : (G ⧸ H), t = x ∨ t = y := by
        intro t
        exact card2sethastwoelements x y t ind hxneqy
      have hygH : y • (H : Set G) = g • (H : Set G) := by
        sorry
      have hyHg : y • (H : Set G) = op g • (H : Set G) := by
        sorry
      rw [hygH] at hyHg
      exact hyHg
  exact normal_of_eq_cosets H h2
  done
