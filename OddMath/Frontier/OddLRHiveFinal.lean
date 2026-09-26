import OddMath.Frontier.OddLRHiveTableau
import OddMath.Frontier.OddLRRule

/-!
# The odd Littlewood–Richardson rule for triangles and hives

Ellis, arXiv:1111.3932v1, §4.3: (4.14), p.17, and (4.20), p.19, unconditionally, with
Definition 4.11 (3) corrected (see `OddLRHive.printed_4_14_fails`). These combine
Theorem 4.8 (`OddLRRule.thm_4_8`) with `OddLRHive.eq_4_14_of_thm_4_8` and
`OddLRHive.eq_4_20_of_thm_4_8`.
-/

namespace OddMath.Frontier.OddLRHive

open OddLRTableau
open scoped BigOperators

variable {n : ℕ} {lam mu nu : YoungDiagram}

/-- E (4.14): `c^λ_{μν} = (-1)^{N(μ)+N(λ)} Σ_{A ∈ △_LR(λ,μ,ν) ∩ V_ℤ} (-1)^{Q_△(A)}`. -/
theorem eq_4_14 (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) (hn : nu.colLen 0 ≤ n) :
    oddLR lam mu nu = (-1 : ℤ) ^ (TableauStripSigns.north mu + TableauStripSigns.north lam) *
      ∑ A ∈ trianglePoints n lam mu nu, (-1 : ℤ) ^ (Qtri A).natAbs :=
  eq_4_14_of_thm_4_8 hl hm hn (OddLRRule.thm_4_8 lam mu nu)

/-- E (4.20): `c^λ_{μν} = (-1)^{N(μ)+N(λ)} Σ_{H ∈ 𝔥(λ,μ,ν) ∩ V_ℤ} (-1)^{Q_𝔥(H)}`. -/
theorem eq_4_20 (hl : lam.colLen 0 ≤ n) (hm : mu.colLen 0 ≤ n) (hn : nu.colLen 0 ≤ n) :
    oddLR lam mu nu = (-1 : ℤ) ^ (TableauStripSigns.north mu + TableauStripSigns.north lam) *
      ∑ H ∈ hivePoints n lam mu nu, (-1 : ℤ) ^ (QH H).natAbs :=
  eq_4_20_of_thm_4_8 hl hm hn (OddLRRule.thm_4_8 lam mu nu)

end OddMath.Frontier.OddLRHive
