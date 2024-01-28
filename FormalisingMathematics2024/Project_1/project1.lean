import Mathlib.Tactic
import LeanCopilot

variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V]

theorem basisExistence

theorem OrthonormalBasisExistence :=

theorem subsetofOrthoBasisOrtho

theorem rank_nullity {K : Type} {V: Type v} {V₁ : Type v} [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁] (f : V →ₗ[K] V₁): Module.rank K (LinearMap.range f) + Module.rank K (LinearMap.ker f) = Module.rank K V := by



  done
