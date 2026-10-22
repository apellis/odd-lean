/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.EvenBridge.MatchingDegree
import OddMath.SKM.EvenBridge.Bubbles
import OddMath.SKM.MixedDotGrading

/-!
# The Theorem 8.1 family and KL III's index set `B_{𝐢,𝐣,λ}`

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Theorem 8.1:
`HOM(E_a 1_μ, E_b 1_μ)` is spanned by the decorated reduced matchings of a
`MatchingBasisChoice`, with coefficients in `SYM`. For purely even data with the symmetrizer
`dᵢ = (i·i)/2`, a decorated matching with a bubble monomial is the same datum as an element of
KL III's index set `B_{𝐢,𝐣,λ}` (A. D. Lauda, M. Khovanov, *A categorification of quantum sl(n)*,
arXiv:0807.3250v1, §3.2.3), and the degrees agree.

## Main results

* `tableDegree_layers`: the degree of a decorated matching is KL's `deg(D_σ, λ)` plus `i·i`
  for each dot on an `i`-strand.
* `monoIdxEquiv`: decorated matchings with a monomial coefficient correspond to `SpanIdx a b`.
* `spanDeg_monoIdxEquiv`: this correspondence matches the Brundan–Ellis degree with `spanDeg`.
-/

noncomputable section
namespace OddMath.SKM.EvenBridge
open StringDiagrams StringDiagrams.Chord Categorification.KL3 Categorification.QuantumGroup

universe u v
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)
  (C : CartanDatum I) (hc : Compatible D C)

local notation "RD" => weightDatum D C hc

variable {a b : List (Letter I)}

/-- The colour of a strand of a matching is the colour of the corresponding KL arc. -/
theorem matchingStrandColour_eq {R : List (TMove (Letter I))} (hR : IsMatching₂ a b R)
    (j : MatchingStrand a R) :
    matchingStrandColour a R j = Diagram.arcCol (strandEquivArc hR j) := by
  rw [arcCol_strandEquivArc]
  rfl

/-- **The degree of a decorated matching**: KL III's degree of the minimal diagram of the
pairing, plus `i·i` for each dot on an `i`-strand. -/
theorem tableDegree_layers (μ : X) (F : MatchingBasisChoice a b) (t : F.Labels) :
    tableDegree D (symmetrizer D C hc) μ (F.layers t) =
      UDot.pdeg C ((RD).ellOf μ) a b (matchingPerm (F.matching t.1 t.1.2).1) +
        ∑ x, (t.2 ((strandEquivArc (F.matching t.1 t.1.2).1).symm x) : ℤ) *
          C.dot (Diagram.arcCol x) (Diagram.arcCol x) := by
  obtain ⟨R, c⟩ := t
  rw [MatchingBasisChoice.layers, (mixed_decorated_degree_parity D (symmetrizer D C hc) μ
      (F.matching R R.2).1 (F.points R) (F.onStrand R) c _ (F.decorates R c)).1,
    tableDegree_tLay D C hc μ (F.matching R R.2).1 (F.matching R R.2).2.1]
  congr 1
  rw [← (strandEquivArc (F.matching R R.2).1).sum_comp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Equiv.symm_apply_apply, ← matchingStrandColour_eq, two_mul_symmetrizer_d]

/-- The bubble degree of a monomial is KL III's degree of the corresponding bubble monomial. -/
theorem bubbleDegree_eq_weight (m : (I × ℕ) →₀ ℕ) :
    bubbleDegree (symmetrizer D C hc) m = Finsupp.weight (Diagram.wPi C) m := by
  rw [bubbleDegree]
  congr 2
  funext p
  rw [Diagram.wPi, two_mul_symmetrizer_d]
  ring

/-- Decorated matchings of a `MatchingBasisChoice` together with a bubble monomial. -/
abbrev MonoIdx (F : MatchingBasisChoice a b) : Type u := Σ _t : F.Labels, (I × ℕ) →₀ ℕ

/-- **Decorated matchings with a bubble monomial are KL III's index set `B_{𝐢,𝐣,λ}`**: the
representative goes to its pairing, the dots on a strand to the dots on its arc. -/
def monoIdxEquiv (F : MatchingBasisChoice a b) : MonoIdx F ≃ Diagram.SpanIdx a b :=
  (Equiv.sigmaAssoc fun _ _ => (I × ℕ) →₀ ℕ).trans <|
    Equiv.sigmaCongr F.pairingEquiv fun R =>
      (Equiv.sigmaEquivProd _ _).trans <|
        Equiv.prodCongr (Equiv.arrowCongr (strandEquivArc (F.matching R R.2).1) (Equiv.refl ℕ))
          (Equiv.refl _)

/-- **The correspondence preserves degrees**: the degree of a decorated matching with a bubble
monomial is KL III's `spanDeg` of the corresponding index. -/
theorem spanDeg_monoIdxEquiv (μ : X) (F : MatchingBasisChoice a b) (j : MonoIdx F) :
    Diagram.spanDeg C ((RD).ellOf μ) (monoIdxEquiv F j) =
      tableDegree D (symmetrizer D C hc) μ (F.layers j.1) +
        bubbleDegree (symmetrizer D C hc) j.2 := by
  obtain ⟨t, m⟩ := j
  rw [tableDegree_layers, bubbleDegree_eq_weight]
  rfl

end OddMath.SKM.EvenBridge
