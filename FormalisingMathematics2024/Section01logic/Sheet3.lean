/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  change True → False at h
  apply h
  triv
  done

example : False → ¬True := by
  intro h
  change True → False
  intro h2
  exact h
  done

example : ¬False → True := by
  intro h
  change False → False at h
  triv
  done

example : True → ¬False := by
  intro h
  change False → False
  intro h2
  exact h2
  done

example : False → ¬P := by
  intro f
  change P → False
  intro hP
  exact f
  done

example : P → ¬P → False := by
  intro hP
  intro hPf
  change P → False at hPf
  apply hPf
  exact hP
  done

example : P → ¬¬P := by
  intro hP
  change ¬P → False
  change (P → False) → False
  intro hPf
  apply hPf
  exact hP
  done

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ
  change (Q → False) → (P → False)
  intro hQf
  intro hP
  apply hQf
  apply hPQ
  exact hP
  done

example : ¬¬False → False := by
  intro h
  change (False → False) → False at h
  apply h
  intro f
  exact f
  done

example : ¬¬P → P := by
  intro hnnP -- assume ¬ ¬ P
  by_contra hnP -- goal is now `False`
  apply hnnP -- goal is now ¬ P
  exact hnP
  done

example : (¬Q → ¬P) → P → Q := by
  intro h hP
  change (Q → False) → P → False at h
  by_contra hnQ
  apply h
  exact hnQ
  exact hP
  done
