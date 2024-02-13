import Mathlib.Tactic
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

theorem cent_of_normal_is_normal (H : Subgroup G) : H.Normal → (centralizer H).Normal := by
  rintro h
  sorry
