/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP
  done

example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ
  done

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  cases' hPoQ with hP hQ
  intro h
  intro h2
  apply h
  exact hP

  intro h
  intro h2
  apply h2
  exact hQ
  done

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hPQ
  cases' hPQ with hP hQ
  right
  exact hP
  left
  exact hQ
  done

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  rintro ((hP | hQ) | hR)
  left; exact hP
  right; left; exact hQ
  right; right; exact hR

  rintro (hP | hQ | hR)
  left; left; exact hP
  left; right; exact hQ
  right; exact hR
  done

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  rintro (hPR  hQS (hP|hQ))
  left; apply hPR; exact hP
  right; apply hQS; exact hQ
  done

example : (P → Q) → P ∨ R → Q ∨ R := by
  rintro (hPQ (hP|hR))
  left; apply hPQ; exact hP
  right; exact hR
  done

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  rintro (hPR hQS)
  rw [hPR]
  rw [hQS]
  done

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  intro h
  constructor
  intro hP
  apply h
  left; exact hP

  intro hQ
  apply h
  right; exact hQ

  intro h
  by_contra h2
  cases' h with hnP hnQ
  cases' h2 with hP hQ
  apply hnP; exact hP
  apply hnQ; exact hQ
  done

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  intro h
  by_cases hP:P
  right
  intro hQ
  apply h
  constructor
  exact hP
  exact hQ
  left
  exact hP

  intro h
  by_contra h2
  cases' h with hnP hnQ
  apply hnP
  cases' h2 with hP hQ
  exact hP

  apply hnQ
  cases' h2 with hP hQ
  exact hQ

  done
