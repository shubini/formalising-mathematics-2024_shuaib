/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl
  done

example : (P ↔ Q) → (Q ↔ P) := by
  intro hPQ
  rw [hPQ]
  done

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  intro hPQ
  rw [hPQ]
  intro hQP
  rw [hQP]
  done

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPQ
  rw [hPQ]
  intro hQR
  exact hQR
  done

example : P ∧ Q ↔ Q ∧ P := by
  constructor <;>
  · rintro ⟨a, b⟩
    exact ⟨b, a⟩
  done

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro h
    cases' h with hPaQ hR
    cases' hPaQ with hP hQ
    constructor
    · exact hP
    · constructor
      · exact hQ
      · exact hR
  · rintro ⟨hP, hQ, hR⟩
    exact ⟨⟨hP, hQ⟩, hR⟩
  done

example : P ↔ P ∧ True := by
  constructor
  intro hP
  constructor
  exact hP
  triv
  rintro ⟨hP, -⟩
  exact hP
  done

example : False ↔ P ∧ False := by
  constructor
  intro hf
  exfalso
  exact hf

  intro h
  cases' h with hP false
  exact false
  done

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro hPQ
  cases' hPQ with hPQ hQP
  intro hRS
  cases' hRS with hRS hSR
  constructor
  intro hPR
  cases' hPR with hP hR
  constructor
  apply hPQ
  exact hP
  apply hRS
  exact hR

  intro hQS
  cases' hQS with hQ hS
  constructor
  apply hQP
  exact hQ
  apply hSR
  exact hS
  done

example : ¬(P ↔ ¬P) := by
  intro h
  have hnP : ¬P := by
    cases' h with h1 h2
    intro hP
    apply h1 <;>
    exact hP
  apply hnP
  rw [h]
  exact hnP
  done
