import Mathlib.Tactic
import LeanCopilot
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

theorem centralizer.inv_mem (hy : y ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h}) :
    y⁻¹ ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h} := by
  intro h hh
  specialize hy h hh
  rw [hy.symm]
  group at *
  exact hy.symm

theorem centralizer.mul_mem (hy : y ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h})
    (hz : z ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h}) :
    y * z ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h} := by
  intro h hh
  specialize hy h hh
  specialize hz h hh
  rw [mul_inv_rev, ←mul_assoc]
  have hyz : y * z * h * z⁻¹ = y * (z * h * z⁻¹) := by
    group
  rw [hyz, hz, hy]

def centralizer (H : Subgroup G) : Subgroup G
    where
  carrier := {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h}
  one_mem' := centralizer.one_mem
  inv_mem' := centralizer.inv_mem
  mul_mem' := centralizer.mul_mem

lemma cent_of_normal_is_normal (H : Subgroup G) [H_norm : H.Normal]: ∀ n, n ∈
    (centralizer H) → ∀ g : G, g * n * g⁻¹ ∈ (centralizer H):= by
  intro n hn g h hh
  rw [show g * n * g⁻¹ * h * (g * n * g⁻¹)⁻¹ = g * (n * (g⁻¹ * h * g) * n⁻¹) * g⁻¹ by group]
  have h2 : (g⁻¹ * h * g) ∈ H := by
    rw [show (g⁻¹ * h * g) = (g⁻¹ * h * g⁻¹⁻¹) by group]
    exact Subgroup.Normal.conj_mem H_norm h hh g⁻¹
  specialize hn (g⁻¹ * h * g) h2
  rw [hn]
  group

def center := centralizer (⊤ : Subgroup G)
theorem subofCentreNormal (H : Subgroup G) (hSub: H ≤ center) :  ∀ n, n ∈
    H → ∀ g : G, g * n * g⁻¹ ∈ H:= by
  intro h hh g
  specialize hSub hh g (Subgroup.mem_top g)
  rw [←eq_mul_of_mul_inv_eq hSub, mul_assoc, mul_inv_self g, mul_one]
  exact hh

-- PS1
-- theorem autgroupofZ [G : AddGroup ℤ]: ∃φ, (φ : ((Group (G →* G)) →* (ℤ⧸2*ℤ))):= by sorry


--q3
theorem index2subgroupNormal [Group G] (H: Subgroup G) (ind: Subgroup.index H = 2) : H.Normal:= by
