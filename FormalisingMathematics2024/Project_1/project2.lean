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

GROUPS AND RINGS MIDTERM Q1 -- init

CANT FIND BUT -- GROUP THEORY PROVE ANY INDEX 3 SUBGROUP OF AN ODD ORDER GROUP IS NORMAL

-/

-- MIDTERM Q1
variable (G : Type) [Group G]  (H K : Subgroup G)
variable {G H} {x : G}

variable {y z : G}

lemma mul_inv_eq_inv_mul_inv (x y : G) : (x * y)⁻¹ = y⁻¹ * x⁻¹ := by group

theorem centralizer.one_mem : (1 : G) ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h} := by
  rintro h _
  group

theorem centralizer.inv_mem (hy : y ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h}) :
    y⁻¹ ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h} := by
  intro h hh
  specialize hy h hh
  rw [hy.symm]
  group at * -- evil floating point bit level hacking
  exact hy.symm

theorem centralizer.mul_mem (hy : y ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h})
    (hz : z ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h}) :
    y * z ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h} := by
  intro h hh
  specialize hy h hh
  specialize hz h hh
  rw [mul_inv_eq_inv_mul_inv]
  rw [←mul_assoc]
  have hyz : y * z * h * z⁻¹ = y * (z * h * z⁻¹) := by
    group
  rw [hyz]
  rw [hz]
  rw [hy]

def centralizer (H : Subgroup G) : Subgroup G
    where
  carrier := {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h}
  one_mem' := centralizer.one_mem
  inv_mem' := centralizer.inv_mem
  mul_mem' := centralizer.mul_mem

theorem cent_of_normal_is_normal (H : Subgroup G) [H_norm : H.Normal]: ∀ n, n ∈
    (centralizer H) → ∀ g : G, g * n * g⁻¹ ∈ (centralizer H):= by
  rintro n hn g h hh
  have H_norm_1 := Subgroup.Normal.conj_mem H_norm
  have h2: ∀ h ∈ H, n * h * n⁻¹ = h := by -- del
    exact fun h a => hn h a
  specialize h2 h hh
  specialize H_norm_1 h hh g
  let h₂ := g⁻¹ * h* g
  simp
  rw [mul_assoc, mul_assoc]
  have assoc_helper : (g⁻¹ * (h * (g * (n⁻¹ * g⁻¹)))) = (g⁻¹ * h * g) * (n⁻¹ * g⁻¹) := by group
  rw [assoc_helper]
  change g * n * (h₂ * (n⁻¹ * g⁻¹)) = h
  have assoc_helper : g * n * (h₂ * (n⁻¹ * g⁻¹)) = g * (n * h₂ * n⁻¹) * g⁻¹ := by group
  rw [assoc_helper]
  have h2h : h₂ ∈ H := by
    change (g⁻¹ * h * g) ∈ H
    have a: g⁻¹ * h * g⁻¹⁻¹ ∈ H := by
      exact Subgroup.Normal.conj_mem H_norm h hh g⁻¹
    have b: (g⁻¹ * h * g) = (g⁻¹ * h * g⁻¹⁻¹) := by
      group
    rw [b]
    exact a
  specialize hn h₂ h2h
  rw [hn]
  change g * (g⁻¹ * h * g) * g⁻¹ = h
  group
