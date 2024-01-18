/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet5 -- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/


theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  rw [tendsTo_def]
  intro ε hε
  obtain ⟨X, hX⟩ := h (ε / 37) (by linarith)
  use X
  intro n hn
  specialize hX n hn
  rw [← mul_sub]
  rw [abs_mul]
  rw [abs_of_nonneg] <;>
  linarith


/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rw [tendsTo_def]
  intro ε hε
  obtain ⟨X, hX⟩ := h (ε / c) (by positivity)
  use X
  intro n hn
  specialize hX n hn
  rw [← mul_sub]
  rw [abs_mul]
  rw [abs_of_pos hc]
  exact (lt_div_iff' hc).mp hX

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rw [tendsTo_def]
  intro ε hε
  have hc' : 0 < -c := neg_pos.mpr hc
  obtain ⟨X, hX⟩ := h (ε / -c) (by positivity)
  use X
  intro n hn
  specialize hX n hn
  rw [← mul_sub]
  rw [abs_mul]
  rw [abs_of_neg hc]
  exact (lt_div_iff' hc').mp hX

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  obtain hc | hc | hc := lt_trichotomy c 0
  exact tendsTo_neg_const_mul h hc

  rw [hc, tendsTo_def]
  simp
  intro ε hε
  use 0
  intro n hn
  exact hε

  exact tendsTo_pos_const_mul h hc

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
  simpa [mul_comm] using tendsTo_const_mul c h
  done

-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa only [neg_mul, one_mul] using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by

  simpa using tendsTo_add h1 h2

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
example (a b c: ℝ) (hc: 0 < c): a < b / c ↔ c * a < b := by
  exact lt_div_iff' hc

theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  constructor
  intro h
  simpa [tendsTo_def] using tendsTo_sub h (tendsTo_const t)
  intro h
  simpa using tendsTo_add h (tendsTo_const t)

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  intro ε hε
  obtain⟨X, hX⟩ := ha ε hε
  obtain ⟨Y, hY⟩ := hb 1 (by norm_num)
  use max X Y
  intro n hn
  simp at *
  rw [abs_mul]
  specialize hX n hn.1
  specialize hY n hn.2
  simpa using mul_lt_mul'' hX hY
  done

example (x y : ℝ) : |x| * |y| = |x * y| := by exact (abs_mul x y).symm

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
  intro ε hε
  obtain⟨X, hX⟩ := ha (ε ^ 1/2) (by linarith)
  obtain⟨Y, hY⟩ := hb (ε ^ 1/2) (by linarith)
  use max X Y
  intro n hn
  specialize hX n (by exact le_of_max_le_left hn)
  specialize hY n (by exact le_of_max_le_right hn)
  simp [hX, hY, abs_mul]
  exact
  sorry

-- something we never used!
/-- A sequence has at most one limit. -/
example (t s : ℝ) : t - s = 0 ↔ t = s:= by exact sub_eq_zero

example (t s : ℝ) (h: t ≠ s): |t-s| > 0:= by
  simp [h, sub_eq_zero]



theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  by_contra h
  wlog hlt : s < t
  · cases' Ne.lt_or_lt h with h3 h3
    · contradiction
    · specialize this a t s
      apply this ht hs (by exact Ne.symm h)
      exact h3
  have h2 : TendsTo (0) (s - t) := by
    simpa using tendsTo_sub hs ht
  rw [tendsTo_def] at h2
  simp at h2
  specialize h2
  specialize h2 |t - s| (by simp [h, Ne.symm, sub_eq_zero])
  obtain⟨B, hB⟩ := h2
  specialize hB B
  have hBB: B ≤ B := by rfl
  apply hB at hBB
  rw [← lt_self_iff_false |t-s|]
  exact hBB
  done

end Section2sheet6
