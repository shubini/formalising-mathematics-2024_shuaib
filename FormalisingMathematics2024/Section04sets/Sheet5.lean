/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal.

## Tactics

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext x
  constructor
  · intro h
    cases' h with h h <;>
    exact h
  · intro h
    constructor
    exact h

example : A ∩ A = A := by
  ext x
  constructor
  · intro h
    cases' h with h _
    exact h
  · intro h
    constructor <;>
    exact h

example : A ∩ ∅ = ∅ := by
  ext x
  constructor
  · rintro ⟨l, r⟩
    exact r
  · intro h
    constructor
    · exfalso
      apply h
    · exact h

example : A ∪ univ = univ := by
  exact union_univ

example : A ⊆ B → B ⊆ A → A = B := by
  exact fun a a_1 => Subset.antisymm a a_1

example : A ∩ B = B ∩ A := by
  ext x
  constructor <;>
  · rintro ⟨l, r⟩
    constructor <;>
    simp [*]

example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  ext x
  constructor
  · rintro ⟨ha, ⟨hb, hc⟩⟩
    constructor
    · constructor
      · exact ha
      · exact hb
    · exact hc
  · rintro ⟨⟨ha, hb⟩, hc⟩
    constructor
    · exact ha
    · constructor
      · exact hb
      · exact hc

example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext x
  constructor
  · rintro (ha | hb | hc)
    · left; left; exact ha
    · left; right; exact hb
    · right; exact hc
  · rintro ((ha | hb) | hc)
    · left; exact ha
    · right; left; exact hb
    · right; right; exact hc
example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  · rintro (ha | ⟨hb, hc⟩)
    · constructor <;>
      · left; exact ha
    · constructor <;>
      · right; simp [*]
  · rintro ⟨(ha | hb), (ha | hc)⟩
    · left; exact ha
    · left; exact ha
    · left; exact ha
    · right
      constructor <;>
      simp [*]

example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  ext x
  constructor
  · rintro ⟨ha, (hb|hc)⟩
    · left; constructor
      · exact ha
      · exact hb
    · right; constructor
      . exact ha
      · exact hc
  · rintro (⟨ha, hb⟩ | ⟨ha, hc⟩)
    · constructor
      · exact ha
      · left; exact hb
    · constructor
      · exact ha
      · right; exact hc
