import Mathlib.Tactic
import LeanCopilot
import Mathlib.SetTheory.Cardinal.Finite
open QuotientGroup
open MulOpposite

/-!
# Project 2

## Main definitions

* `centralizer H`: the subgroup consisting of elements of G that fix all h ∈ H under conjugation
* `center`: the subgroup `Z(G)` of elements that commute with all g ∈ G

## Main statements

* `cent_of_normal_is_normal`: The centralizer of a normal subgroup of G is normal
* `ind_2_subgroup_normal`: A subgroup of index 2 is normal
* `G_quot_center_cylic_imp_G_abel`: If the quotient group `(G / Z(G)` is cyclic.
-/

-- MIDTERM Q1
variable (G : Type) [Group G]  (H : Subgroup G)
variable {G H} {x : G}

/-- 1 is in centralizer H-/
theorem centralizer.one_mem : (1 : G) ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h} := by
  intro h _
  group
  done

/--centralizer H is closed under inverses-/
theorem centralizer.inv_mem (hy : y ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h}) :
    y⁻¹ ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h} := by
  intro h hh
  specialize hy h hh
  --use hypothesis that y in centralizer to rw h as g * h * g⁻¹
  rw [←hy]
  -- simplifies all hypotheses using group axioms
  group at *
  exact hy.symm
  done

/--centralizer H is closed under multiplication-/
theorem centralizer.mul_mem (hy : y ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h})
    (hz : z ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h}) :
    y * z ∈ {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h} := by
  -- intros h and hypothesis h ∈ H which are then used to specialise hy and hz
  intro h hh
  specialize hy h hh
  specialize hz h hh
  -- the first three rewrites simplify the goal to y * (z * h * z⁻¹) * y⁻¹ = h,
  --and then hypotheses that z and y centralize h is used to get goal h = h,
  --which is closed by rw's rfl
  rw [mul_inv_rev, ←mul_assoc, show y * z * h * z⁻¹ = y * (z * h * z⁻¹) by group, hz, hy]
  done

/--The centralizer of a subgroup H is all the
elements of G that fix all elements of H by conjugation-/
def centralizer (H : Subgroup G) : Subgroup G
    where
  carrier := {g : G | ∀ h ∈ H,  g * h * g⁻¹ = h}
  one_mem' := centralizer.one_mem
  inv_mem' := centralizer.inv_mem
  mul_mem' := centralizer.mul_mem

/--The centralizer of a normal subgroup is normal-/
theorem cent_of_normal_is_normal (H : Subgroup G) (H_norm : H.Normal) :
    (centralizer H).Normal := by
  constructor
  intro n hn g h hh
  -- rw using group axioms to write goal in a form where normality can be used
  rw [show g * n * g⁻¹ * h * (g * n * g⁻¹)⁻¹ = g * (n * (g⁻¹ * h * g) * n⁻¹) * g⁻¹ by group]
  -- use normality of H to show (g⁻¹ * h * g) is in H
  have h2 : (g⁻¹ * h * g) ∈ H := by
    rw [show (g⁻¹ * h * g) = (g⁻¹ * h * g⁻¹⁻¹) by group]
    exact Subgroup.Normal.conj_mem H_norm h hh g⁻¹
  -- use that n is in centralizer to rw goal without n, then solve goal using group axioms
  specialize hn (g⁻¹ * h * g) h2
  rw [hn]
  group
  done

/--The center is the subgroup of elements which centralize the entire group G-/
abbrev center := centralizer (⊤ : Subgroup G)

/--Any subgroup of the center of G is normal-/
lemma sub_of_center_normal (H : Subgroup G) (hSub: H ≤ center) : H.Normal:= by
  constructor
  intro h hh g
  specialize hSub hh g (Subgroup.mem_top g) --specialize hSub w/ g as a member of ⊤
  -- ←eq_mul_of_mul_inv_eq hSub swaps g * h for h * g in goal, then use various group axioms
  rw [←eq_mul_of_mul_inv_eq hSub, mul_assoc, mul_inv_self g, mul_one]
  exact hh
  done

-- PS1
--Q3
/--Given two elements x and y of cardinality 2 set X which are not equal,
any element of X is equal to x or is equal to y.-/
lemma el_of_card_2_eqs_either_el {X: Type} (x y : X) (h: Nat.card X = 2)
    (hxy: x≠y): ∀ z : X, z = x ∨ z = y := by
  intro z
  --Nat.card_eq_two_iff' says theres a unique non x value in a card 2 set, we call it y_
  obtain ⟨y_, ⟨_, h2⟩⟩ := (Nat.card_eq_two_iff' x).mp h
  have hy: y = y_ := h2 y hxy.symm -- since y_ is unique, and y ≠ x,  y = y_
  rw [←hy] at h2
  -- break down z into cases where z = x or z = y
  cases' eq_or_ne z x with hxz hxz
  · left -- goal z = x
    exact hxz
  · right -- goal z = y
    exact h2 z hxz
  done

/--If g ∉ H, g ∈ G, the coercion of g to type G ⧸ H is not equal to
the coercion of 1 to type G ⧸ H.-/
lemma mk_g_nin_H_neq_mk_1 [Group G] {H: Subgroup G} {g : G} (hg : g ∉ H):
    (g : G ⧸ H) ≠ ↑(1 : G) := by
  by_contra h -- add hypothesis h : ↑g = ↑1, change goal to False
  rw [QuotientGroup.eq', mul_one] at h -- QuotientGroup.eq' gives g⁻¹ * 1 ∈ H
  apply hg -- change goal to g ∈ H
  exact (Subgroup.inv_mem_iff H).mp h -- iff version of inv_mem
  done

/--For an index 2 subgroup H, the coercion to G ⧸ H of
any g ∈ G is equal to the coercion of g⁻¹.-/
lemma mk_g_eq_mk_g_inv [Group G] {H: Subgroup G} (g : G) (ind: Subgroup.index H = 2):
    (g : G ⧸ H) = ↑(g⁻¹) := by
  cases' em (g ∈ H) with hg hg
  -- g ∈ H case
  · rw [QuotientGroup.eq']
    exact mul_mem (inv_mem hg) (inv_mem hg)
  -- g ∉ H case
  · have hxy := el_of_card_2_eqs_either_el (g : G ⧸ H) ↑(1 : G) ind (mk_g_nin_H_neq_mk_1 hg)
    cases' hxy ↑g⁻¹ with mk_g mk_1
    -- split into cases mk g⁻¹ = mk g and mk g⁻¹ = mk 1
    · exact mk_g.symm
    · rw [QuotientGroup.eq', mul_one, inv_inv] at mk_1
      -- we have g ∈ H and and g ∉ H so prove by contradiction
      by_contra
      apply hg
      exact mk_1
  done

open scoped Pointwise
/--An index 2 subgroup is normal.-/
theorem ind_2_subgroup_normal [Group G] (H : Subgroup G) (ind : Subgroup.index H = 2) :
    H.Normal := by
  rw [normal_iff_eq_cosets] --change goal into something about cosets
  intro g
  -- take cases g ∈ H and g ∉ H
  cases' em (g ∈ H) with hginH hgninH
  · rw [leftCoset_mem_leftCoset H hginH, rightCoset_mem_rightCoset H hginH]
  · have hygH := eq_class_eq_leftCoset H g -- gives left coset as set of G with specific mk val
    -- want set of right cosets to be the same set
    have hyHg : {(t : G) | ↑t = (g : G ⧸ H)} = op g • (H : Set G) := by
      ext g₂
      change ↑g₂ = (g : G ⧸ H) ↔ g₂ ∈ op g • (H : Set G)
        -- switch mk g₂ and mk g for mk g₂⁻¹ and mk g⁻¹, so QuotientGroup.eq' rws hg2y such that
        -- it matches with mem_rightCoset_iff
      rw [mk_g_eq_mk_g_inv g₂ ind, mk_g_eq_mk_g_inv g ind, QuotientGroup.eq',
        show g₂⁻¹⁻¹ = g₂ by group, (mem_rightCoset_iff g)]
      rfl -- def. true that g ∈ H as a subgroup iff g ∈ H as a set
    rw [hygH] at hyHg -- left and right cosets are equal
    exact hyHg
  done

--Q5
instance center_is_normal [Group G]: (centralizer (⊤: Subgroup G)).Normal := by
  exact sub_of_center_normal center (Eq.le rfl)

/--Elements of the Z(G) commute with all elements of G-/
lemma mem_center_iff : a ∈ center ↔ ∀ g : G, a * g = g * a := by
  constructor
  · intro a_cent g
    specialize a_cent g (Subgroup.mem_top g)
    nth_rewrite 2 [←a_cent]
    group
  · intro h g _
    specialize h g
    rw [h]
    group
  done

/--If G ⧸ Z(G) is cyclic, then G is abelian.-/
theorem G_quot_center_cylic_imp_G_abel [Group G]
    (h: ∃ (g : G), ∀ (x : G ⧸ center), x ∈ Subgroup.zpowers ↑g):
    ∀ a b : G, a * b = b * a := by
  intro a b
  -- get generator of G ⧸ Z(G)
  obtain ⟨g, h⟩ := h
  have ha := h a
  have hb := h b

  -- get k₁ and k₂ where mk a = mk (g) ^ k₁ and mk b = mk (g) ^ k₂
  rw [Subgroup.mem_zpowers_iff] at ha hb
  obtain ⟨k₁, ha⟩ := ha
  obtain ⟨k₂, hb⟩ := hb

  -- let w = (g ^ k₁)⁻¹ * a and z = (g ^ k₂)⁻¹ * b and show both of these are in center
  let w := (g ^ k₁)⁻¹ * a
  have hw : w ∈ center := by
    exact QuotientGroup.eq.mp ha
  let z := (g ^ k₂)⁻¹ * b
  have hz : z ∈ center := by
    exact QuotientGroup.eq.mp hb

  -- rewrite goal in terms of w, z and g ^ k
  rw [show a = (g ^ k₁) * w by group, show b = (g ^ k₂) * z by group]
  -- using that w and z commute with everything in G (in center) and
  -- that g ^ k₁ * g ^ k₂ = g ^ k₂ * g ^ k₁, we can reorder everything on LHS until
  -- its the same order and the RHS
  nth_rewrite 1 [show g ^ k₁ * w * (g ^ k₂ * z) = g ^ k₁ * (w * (g ^ k₂ * z)) by group,
    mem_center_iff.mp hw, show g ^ k₁ * (g ^ k₂ * z * w) = g ^ k₂ *(g ^ k₁ * z) * w by group,
    ←mem_center_iff.mp hz]
  simp only [mul_assoc] -- all thats left is assoc
  done
