import OddMath.Frontier.ThickRelations

/-!
# [EKL] Lemma 3.3: the ambient ring

Source: A. P. Ellis, M. Khovanov, A. D. Lauda, *The odd nilHecke algebra and its
diagrammatics*, arXiv:1111.1320v1, §3.2.2, Lemma 3.3, (3.24), p. 24.

The identity (3.24) involves `D_a` together with one further strand, so it is an identity among
diagrams on `a + 1` strands: it holds in `ONH_{a+1}`, not in `ONH_a` as printed. Here `ONH_{m+2}`
is `NilHeckeAction.Presented m`, and the identity is `ThickRelations.lemma_3_3` on the full
window `[0, a+1)` of `ONH_{a+1}`, `a = m + 1` (`lemma_3_3_in_ONH_succ`).
-/

namespace OddMath.Frontier.ErrataChecks
open NilHeckeAction NilCoxeterWords StrandCrossing ThickRelations

/-- [EKL] Lemma 3.3, (3.24), for `a = m + 1`, in `ONH_{a+1} = NilHeckeAction.Presented m`, on all
`a + 1` strands: `(D_a ⊗ 1) · (strand from a to 0) = (−1)^{C(a,3)} (strand from a to 0) ·
(1 ⊗ D_a)`. -/
theorem lemma_3_3_in_ONH_succ (m : ℕ) :
    product (triWord m 0 (m+1)) * product (downWord m 0 (m+1)) =
      (-1 : ℤ)^((m+1).choose 3) •
        (product (downWord m 0 (m+1)) * product (triWord m 1 (m+1))) :=
  lemma_3_3 (n := m) 0 (m+1) (by omega)

end OddMath.Frontier.ErrataChecks
