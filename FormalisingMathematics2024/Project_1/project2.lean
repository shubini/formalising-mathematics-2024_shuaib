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
Q3 -- done
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

lemma cent_of_normal_is_normal (H : Subgroup G) (H_norm : H.Normal): (centralizer H).Normal:= by
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
theorem subofCentreNormal (H : Subgroup G) (hSub: H ≤ center) :  H.Normal:= by
  refine' ⟨?_⟩
  intro h hh g
  specialize hSub hh g (Subgroup.mem_top g)
  rw [←eq_mul_of_mul_inv_eq hSub, mul_assoc, mul_inv_self g, mul_one]
  exact hh
  done

-- PS1
/- def Z := AddGroup ℤ
def AutZ := Group ({f | f  : ℤ →* ℤ })

theorem setautgroupofZsize2 [Z : AddGroup ℤ] : Nat.card AutZ = 2:= by
  have AutZnonempty : Nonempty AutZ := by exact Set.instNonemptyRange fun y => y
  cases' AutZnonempty with el
  rw [Nat.card_eq_two_iff' el]
  have hid : (id: ℤ →* ℤ) : AutZ
  def id2 : ℤ ≃+ ℤ := fun z ↦ z
  done
-/
--q3
lemma el_of_card_2_eqs_either_el {X: Type} (x y : X) (h: Nat.card X = 2)
    (hxy: x≠y): ∀ z : X, z = x ∨ z = y := by
  intro z
  obtain ⟨y_, ⟨_, h2⟩⟩ := (Nat.card_eq_two_iff' x).mp h
  have hy: y = y_ := h2 y hxy.symm
  rw [←hy] at h2
  cases' eq_or_ne z x with hxz hxz
  · left
    exact hxz
  · right
    exact h2 z hxz
  done

lemma mk_g_nin_H_neq_mk_1 [Group G] {H: Subgroup G} {g : G} (hg :g ∉ H):
    (g : G ⧸ H) ≠ ↑(1 : G) := by
  by_contra h
  rw [QuotientGroup.eq'] at h
  apply hg
  rw [mul_one] at h
  let h := inv_mem h
  group at h
  exact h

lemma mk_g_eq_mk_g_inv [Group G] {H: Subgroup G} (g : G) (ind: Subgroup.index H = 2):
    (g : G ⧸ H) = ↑(g⁻¹) := by
  cases' em (g ∈ H) with hg hg
  · rw [QuotientGroup.eq']
    exact mul_mem (inv_mem hg) (inv_mem hg)
  · have hxy := el_of_card_2_eqs_either_el (g : G ⧸ H) ↑(1 : G) ind (mk_g_nin_H_neq_mk_1 hg)
    cases' hxy ↑g⁻¹ with l r
    · exact l.symm
    · rw [QuotientGroup.eq'] at r
      group at r
      by_contra
      apply hg
      exact r

open scoped Pointwise
theorem ind_2_subgroup_normal [Group G] (H: Subgroup G) (ind: Subgroup.index H = 2) : H.Normal:= by
  have h2: ∀g : G, g • (H : Set G) = op g • H := by
    intro g
    cases' em (g ∈ H) with hginH hgninH
    · rw [leftCoset_mem_leftCoset H hginH, rightCoset_mem_rightCoset H hginH]
    · have hygH := eq_class_eq_leftCoset H g
      have hyHg : {(t:G) | ↑t = (g: G ⧸ H)} = op g • (H : Set G) := by
        ext g₂
        change ↑g₂ = (g: G ⧸ H) ↔ g₂ ∈ op g • (H : Set G)
        have hy2 := (mk_g_eq_mk_g_inv g ind).symm
        constructor
        · intro hg2y
          have hy1: ↑(g₂⁻¹) = (g : G ⧸ H) := by
            rw [←mk_g_eq_mk_g_inv g₂ ind]
            exact hg2y
          rw [←hy2, QuotientGroup.eq', show g₂⁻¹⁻¹ = g₂ by group] at hy1
          exact (mem_rightCoset_iff g).mpr hy1
        · intro hg₂Hg
          rw [(mem_rightCoset_iff g), show g₂= g₂⁻¹⁻¹ by group] at hg₂Hg
          have h2:= QuotientGroup.eq'.mpr hg₂Hg
          rw [hy2, ←mk_g_eq_mk_g_inv g₂ ind] at h2
          exact h2
      rw [hygH] at hyHg
      exact hyHg
  exact normal_of_eq_cosets H h2
  done

lemma center_is_normal [Group G]: (centralizer (⊤ : Subgroup G)).Normal:= by
  have h : (⊤ : Subgroup G).Normal :=
    by exact Subgroup.normal_of_characteristic ⊤
  exact cent_of_normal_is_normal ⊤ h
  done

theorem G_quot_center_cylic_imp_G_abel [Group G] (h: Subgroup.isCyclic (QuotientGroup.Quotient.group (centralizer (⊤ : Subgroup G)) (cent_of_normal_is_normal ⊤ h))) : ∀ a b : G, a * b = b * a := by
  intro a b

#lint
