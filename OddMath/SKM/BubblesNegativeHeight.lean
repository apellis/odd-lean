/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Bubbles

/-!
# Right bubbles at negative height

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 2.3, (2.11), (2.14), (2.17), (2.18).

At a weight with `⟨hᵢ, λ⟩ < 0` the leftward cap `ε'` of (2.11) is `c_{λ;i}⁻¹` times the
`♦`-cap with label `-⟨hᵢ, λ⟩ - 1`, and every right bubble `bubRs(s)`, `s ≥ 0`, has a
nonnegative number `s - ⟨hᵢ, λ⟩ - 1` of dots. So the normalized right bubble
`c_{λ;i} · bubRs(s)` is the rightward cup with `s - ⟨hᵢ, λ⟩ - 1` dots followed by the
`♦`-cap, with no scalar (`smul_bubRs_of_neg`). The odd bubble (2.18) is the normalized
right bubble `bubRs(1)` there (`oddBubble_of_neg`).

In an action these are the cup, the dots and the inverse cap row `-⟨hᵢ, λ⟩ - 1` of the
inverted `sl₂` map, which is the shape of the inverse-cap moments computed on the tensor
vacuum (research issue #345).
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- At negative height the normalized right bubble with `s + *` dots is the rightward cup
with `s - ⟨hᵢ, λ⟩ - 1` dots followed by the `♦`-cap with label `-⟨hᵢ, λ⟩ - 1`. -/
theorem smul_bubRs_of_neg (i : I) (μ : X) (hμ : D.h i μ < 0) (s : ℕ) :
    (cs.c μ i : k) • bubRs cs i μ s =
      cl D Sc μ [] [dn i, up i] (etaL i ((s : ℤ) - D.h i μ - 1).toNat) ≫
        cl D Sc μ [dn i, up i] [] (dcapL i (-D.h i μ - 1).toNat) := by
  rw [bubRs, bubR, ite_eq_left (show (0 : ℤ) ≤ (s : ℤ) - D.h i μ - 1 by omega),
    epsP, ite_eq_left hμ,
    Linear.comp_smul, smul_smul,
    show (cs.c μ i : k) * (↑(cs.c μ i)⁻¹ : k) = 1 by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one], one_smul]

/-- At negative height the odd bubble (2.18) is the normalized right bubble `bubRs(1)`. -/
theorem oddBubble_of_neg (i : I) (μ : X) (hμ : D.h i μ < 0) :
    oddBubble cs i μ = (cs.c μ i : k) • bubRs cs i μ (1 : ℕ) := by
  rw [oddBubble, ite_eq_right (not_le.mpr hμ), bubRs,
    show ((1 : ℕ) : ℤ) - D.h i μ - 1 = -D.h i μ by omega]

end OddMath.SKM
