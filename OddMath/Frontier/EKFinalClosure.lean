import OddMath.Frontier.EKLemma311Cond
import OddMath.Frontier.EKClosureComposition

/-!
# EK final closure: Lemma 3.11 (3.13), Cor 3.12, Cor 3.13 for every degree

Closure module.  It contains ONLY term-mode applications of existing theorems: no new
lemmas beyond the four statements below, no definitions, no local instances, no tactics.

Premises (all in `OddMath/Frontier`):
* `EKClosureComposition.identity311 d : EKProp310.Identity311 d` (every `d`, unconditional; from
  `EKKostkaValues.Mh_eq_sum_kostka` via `EKSchurOrthonormal.corollary_3_9`).
* `EKLemma311Cond.lemma_3_11_of_identity311 d : EKLemma311CondControls.Identity311 d → (3.13)_d`
  Its hypothesis is a verbatim namespaced copy of `EKProp310.Identity311`;
  the copies of `schur` / `transposeChoose` / the local `DecidableEq` instance have identical bodies,
  so the application is accepted by definitional unfolding (checked by the kernel on compile).
* `EKClosureComposition.cor_3_12_first`, `cor_3_12_second`, `cor_3_13` : `EKOddRSKII.Lemma311 d → …`
  The (3.13) produced above is accepted as `EKOddRSKII.Lemma311 d`
  by the same unfolding (`EKOddRSKII.schur` has the identical body `KostkaModuleInversion.recover d
  (degreeHBasis d)`; `transposeShape` is the shared `EKDualBases.transposeShape`).

`EKOddRSKII.Lemma311` is pinned to printed (3.13) `ψ₁ψ₂(s_λ) = (-1)^{ℓ(w_λ)+|λ|} s_{λᵀ}` by
`EKClosureCompositionAudit`; `First312`, `Second312`, `OddRSKII` are the EKOddRSKII
predicates for (3.14, first), (3.14, second) and (3.15).
-/

namespace OddMath.Frontier.EKFinalClosure

/-- **EK Lemma 3.11, (3.13), for every degree `d`, unconditional.** -/
theorem lemma_3_11 (d : ℕ) : EKOddRSKII.Lemma311 d :=
  fun lam => EKLemma311Cond.lemma_3_11_of_identity311 d (EKClosureComposition.identity311 d) lam

/-- **EK Corollary 3.12, first equation (3.14), for every degree `d`, unconditional.** -/
theorem cor_3_12_first (d : ℕ) : EKOddRSKII.First312 d :=
  EKClosureComposition.cor_3_12_first d
    (fun lam => EKLemma311Cond.lemma_3_11_of_identity311 d (EKClosureComposition.identity311 d) lam)

/-- **EK Corollary 3.12, second equation (3.14), for every degree `d`, unconditional.** -/
theorem cor_3_12_second (d : ℕ) : EKOddRSKII.Second312 d :=
  EKClosureComposition.cor_3_12_second d
    (fun lam => EKLemma311Cond.lemma_3_11_of_identity311 d (EKClosureComposition.identity311 d) lam)

/-- **EK Corollary 3.13, (3.15), for every degree `d`, unconditional.** -/
theorem cor_3_13 (d : ℕ) : EKOddRSKII.OddRSKII d :=
  EKClosureComposition.cor_3_13 d
    (fun lam => EKLemma311Cond.lemma_3_11_of_identity311 d (EKClosureComposition.identity311 d) lam)

end OddMath.Frontier.EKFinalClosure

#print axioms OddMath.Frontier.EKFinalClosure.lemma_3_11
#print axioms OddMath.Frontier.EKFinalClosure.cor_3_12_first
#print axioms OddMath.Frontier.EKFinalClosure.cor_3_12_second
#print axioms OddMath.Frontier.EKFinalClosure.cor_3_13
