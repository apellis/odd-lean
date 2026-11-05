/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteSwappedNonpositiveBubbles

/-! # Positive-height bubbles of the swapped route bases

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, in the research scope of `FieldScopeBoundary.md`; (2.11), (2.13),
(2.17), (2.18), and `InverseColumnMoments.md`.

At positive height `hᵢ(μ) > 0` the normalized left bubbles and the odd bubble are closed
diagrams of the dotted leftward cup followed by a dotted rightward cap
(`SKM.inv_smul_bubLs_of_pos`, `SKM.oddBubble_eq_cl_of_pos`). So the vacuum entries of these
closed diagrams give the positive-height bubble field of the swapped route bases:

* `SupportedSectors.VacuumLeftEntries`: the vacuum entries at positive height, as coefficient
  actions of the substituted-series coefficients and of `(-1)^(N_i+1) δ_i`;
* `VacuumBubblesPositiveHeight.of_closed`: the positive-height bubble hypothesis from the
  values of the closed action on these diagrams, for any upward action;
* `SwappedLeftEntriesField sy` and `positiveBubbleField_of_entries`:
  `PositiveBubbleField (swappedRouteBases sy)`;
* `nondegeneracy_of_swapped_entries`: the conjecture from the left and right vacuum entries.

The vacuum entries are an intermediate hypothesis: they are the inverse-column moments of the
probe reservoir at the vacuum sector.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams

/-- At positive height the odd bubble (2.18) is the closed diagram of the dotted leftward cup
with `hᵢ(μ) - 1` dots followed by the rightward cap with `hᵢ(μ)` dots. -/
theorem oddBubble_eq_cl_of_pos {I X k : Type*} [AddCommGroup X] [CommRing k] {D : Datum I X}
    {Sc : Scalars D k} (cs : CScalars Sc) (i : I) (μ : X) (h : 0 < D.h i μ) :
    oddBubble cs i μ =
      cl D Sc μ [] [] (dcupL i (D.h i μ - 1).toNat ++ epsL i (D.h i μ).toNat) := by
  have e := inv_smul_bubLs_of_pos cs i μ h 1
  rw [bubLs, show ((1 : ℕ) : ℤ) + D.h i μ - 1 = D.h i μ by push_cast; ring] at e
  rw [oddBubble, ite_eq_left h.le]
  exact e

end OddMath.SKM

namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u w

section Closed
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k} (cs : SKM.CScalars Sc)

/-- **Bubbles at positive height from closed diagrams.** For any upward action `A` and any
`raw`, the positive-height bubble hypothesis follows from the values of `A.closedAct` on the
closed diagrams of `SKM.inv_smul_bubLs_of_pos` and `SKM.oddBubble_eq_cl_of_pos`. -/
theorem VacuumBubblesPositiveHeight.of_closed {μ : X}
    (A : UpwardModuleAction.{u, w} D Sc μ) (t : List I)
    (raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)) (M N : I → ℕ)
    (left_even : ∀ i, D.parity i = 0 → 0 < D.h i μ → ∀ s : ℕ,
      A.closedAct t (SKM.cl D Sc μ [] []
        (SKM.dcupL i (D.h i μ - 1).toNat ++ SKM.epsL i ((s : ℤ) + D.h i μ - 1).toNat)) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i))))
    (left_odd : ∀ i, D.parity i = 1 → 0 < D.h i μ → ∀ s : ℕ,
      A.closedAct t (SKM.cl D Sc μ [] []
        (SKM.dcupL i (D.h i μ - 1).toNat ++
          SKM.epsL i (((2 * s : ℕ) : ℤ) + D.h i μ - 1).toNat)) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i))))
    (odd : ∀ i : {i : I // D.parity i = 1}, 0 < D.h i.1 μ →
      A.closedAct t (SKM.cl D Sc μ [] []
        (SKM.dcupL i.1 (D.h i.1 μ - 1).toNat ++ SKM.epsL i.1 (D.h i.1 μ).toNat)) =
      raw (SKM.SYM.probeSign D k N i • SKM.SYM.delta D k i)) :
    VacuumBubblesPositiveHeight cs A t raw M N where
  left_even i hi h s := by
    rw [SKM.inv_smul_bubLs_of_pos cs i μ h s]
    exact left_even i hi h s
  left_odd i hi h s := by
    rw [show (2 * (s : ℤ)) = ((2 * s : ℕ) : ℤ) by push_cast; ring,
      SKM.inv_smul_bubLs_of_pos cs i μ h (2 * s)]
    exact left_odd i hi h s
  oddBubble i h := by
    rw [SKM.oddBubble_eq_cl_of_pos cs i.1 μ h]
    exact odd i h

end Closed

namespace SwappedAssembly.SupportedSectors
open SKM CyclotomicAction ELVOld

section Tensor
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (hF : ProbeActionInputs D Sc m cutoff (PowerWordContent.powerBound D cutoff L) ΛP ΛR hP hR)

/-- **Vacuum entries of the bubbles at positive height.** The entries at the vacuum sector of
the closed diagrams of `SKM.inv_smul_bubLs_of_pos` and `SKM.oddBubble_eq_cl_of_pos`, as
coefficient actions of the substituted-series coefficients of `probeSeries M` and of
`(-1)^(N_i+1) δ_i`. -/
structure VacuumLeftEntries (μ : X) (M N : I → ℕ) : Prop where
  left_even : ∀ i, D.parity i = 0 → 0 < D.h i μ → ∀ s : ℕ,
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF μ
      (SKM.dcupL i (D.h i μ - 1).toNat ++ SKM.epsL i ((s : ℤ) + D.h i μ - 1).toNat)
      ((SKM.sChain_dcupL i _).append (SKM.sChain_epsL i _))
      (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i)))
  left_odd : ∀ i, D.parity i = 1 → 0 < D.h i μ → ∀ s : ℕ,
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF μ
      (SKM.dcupL i (D.h i μ - 1).toNat ++ SKM.epsL i (((2 * s : ℕ) : ℤ) + D.h i μ - 1).toNat)
      ((SKM.sChain_dcupL i _).append (SKM.sChain_epsL i _))
      (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k M) i)))
  odd : ∀ i : {i : I // D.parity i = 1}, 0 < D.h i.1 μ →
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF μ
      (SKM.dcupL i.1 (D.h i.1 μ - 1).toNat ++ SKM.epsL i.1 (D.h i.1 μ).toNat)
      ((SKM.sChain_dcupL i.1 _).append (SKM.sChain_epsL i.1 _))
      (SKM.SYM.probeSign D k N i • SKM.SYM.delta D k i)

end Tensor
end SwappedAssembly.SupportedSectors

variable {I X : Type u} [AddCommGroup X] {D : SKM.Datum I X}

/-- **The vacuum entries of the bubbles at positive height**, at every route index of the
swapped route bases. Intermediate hypothesis. -/
def SwappedLeftEntriesField (sy : SKM.Symmetrizer D) : Prop :=
  ∀ ι : VacuumRouteIndex D,
    SwappedAssembly.SupportedSectors.VacuumLeftEntries (D := ι.datum) (Sc := ι.scalars)
      (m := ι.exponent) (cutoff := ι.level) (ΛP := ι.probeHW) (ΛR := ι.reservoirHW)
      (L := ι.power) (hP := ι.probe_pairing) (hR := ι.reservoir_pairing)
      (hF := ι.actionInputs sy) ι.weight
      (probeExponent ι.datum ι.weight ι.t ι.d) (reservoirLevel ι.datum ι.weight ι.t ι.d)

/-- **The positive-height bubble field of the swapped route bases**, from the vacuum entries
of the bubbles at positive height. -/
theorem positiveBubbleField_of_entries (sy : SKM.Symmetrizer D)
    (hE : SwappedLeftEntriesField sy) : PositiveBubbleField (swappedRouteBases sy) :=
  fun ι =>
    VacuumBubblesPositiveHeight.of_closed ι.cscalars (swappedRouteBases sy ι).A ι.t
      (swappedRouteBases sy ι).raw _ _
      (fun i hi h s => swappedRouteBases_closedAct_cl sy ι _ _ _ ((hE ι).left_even i hi h s))
      (fun i hi h s => swappedRouteBases_closedAct_cl sy ι _ _ _ ((hE ι).left_odd i hi h s))
      (fun i h => swappedRouteBases_closedAct_cl sy ι _ _ _ ((hE ι).odd i h))

/-- **The conjecture from the vacuum entries** of the bubbles at positive height and of the
right bubbles at nonpositive height, for the swapped route bases. A reduction step: both
inputs are proved (`swappedLeftEntriesField`, `swappedRightEntriesField`), and the resulting
theorem is `nondegeneracy_of_symmetrizer`. -/
theorem nondegeneracy_of_swapped_entries (sy : SKM.Symmetrizer D)
    (hL : SwappedLeftEntriesField sy) (hR : SwappedRightEntriesField sy)
    {R : Type w} [CommRing R] (h₂ : IsUnit (2 : R))
    {Sc : SKM.Scalars D R} (hh : Sc.Homogeneous) (cs : SKM.CScalars Sc) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_swapped_positive_field_and_entries sy (positiveBubbleField_of_entries sy hL)
    hR h₂ hh cs

end OddMath.QuiverHecke
