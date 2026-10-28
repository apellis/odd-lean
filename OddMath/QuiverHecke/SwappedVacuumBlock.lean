/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedVacuumRecovery
import OddMath.QuiverHecke.PlacementSign
import OddMath.SKM.BubbleSubstitution

/-!
# The vacuum block of the swapped action

Research issue #345, toward the Nondegeneracy Conjecture of Brundan–Ellis,
*Super Kac–Moody 2-categories* (arXiv:1701.04133v2), §8. This file fixes the
schedule of `SwappedNondegeneracy.md` §2 and states the vacuum data of §4 for an
upward module action with exactly that schedule:

* the cutoff `N₀ = d + 2·C(|t|, 2) + 1`, the probe levels `Pᵢ = 2N₀ + 2·max(hᵢ, 0)`,
  the reservoir levels `Nᵢ = 2N₀ + |hᵢ|` (so `Pᵢ - Nᵢ = hᵢ(μ)` and `Nᵢ ≥ N₀`), and the
  bubble substitution `θ` determined by them (`SYM.probeSubstitution`);
* a structure `SwappedVacuumBlock` recording an upward module action together with a
  vacuum vector, the raw reservoir coefficient action, the source-placed bubble
  identity (A16), the transformed last-boundary ideal with the weight bound of
  `SwappedVacuumCoordinates.md` §6, and the literal vacuum evaluation (A18) with the
  ordered-source placement sign.

The construction of the upward module action, of the raw coefficient action and of
the vacuum coordinates belongs to the swapped and ELV-factor actions; this file takes
them as fields. Everything downstream is proved: a vacuum block is a vacuum evaluation
(`SwappedVacuumBlock.toSwappedVacuumEvaluation`), and vacuum blocks at every
equal-weight upward word pair give the Nondegeneracy Conjecture over a field
(`nondegeneracy_of_vacuum_blocks`).
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u

section Schedule
variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X)

/-- The cutoff `N₀ = d + 2·C(|t|, 2) + 1` of the vacuum schedule. -/
def vacuumCutoff (t : List I) (d : ℕ) : ℕ := d + 2 * t.length.choose 2 + 1

/-- The probe level `Pᵢ = 2N₀ + 2·max(hᵢ(μ), 0)`. -/
def probeLevel (μ : X) (t : List I) (d : ℕ) (i : I) : ℕ :=
  2 * vacuumCutoff t d + 2 * (D.h i μ).toNat

/-- The reservoir level `Nᵢ = 2N₀ + |hᵢ(μ)|`. -/
def reservoirLevel (μ : X) (t : List I) (d : ℕ) (i : I) : ℕ :=
  2 * vacuumCutoff t d + (D.h i μ).natAbs

/-- The exponent of the probe series: `Pᵢ / 2` at odd colours, `Pᵢ` at even ones. -/
def probeExponent (μ : X) (t : List I) (d : ℕ) (i : I) : ℕ :=
  if D.parity i = 1 then probeLevel D μ t d i / 2 else probeLevel D μ t d i

theorem probeLevel_even (μ : X) (t : List I) (d : ℕ) (i : I) : Even (probeLevel D μ t d i) :=
  ⟨vacuumCutoff t d + (D.h i μ).toNat, by unfold probeLevel; ring⟩

theorem probeLevel_sub_reservoirLevel (μ : X) (t : List I) (d : ℕ) (i : I) :
    (probeLevel D μ t d i : ℤ) - reservoirLevel D μ t d i = D.h i μ := by
  unfold probeLevel reservoirLevel
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

theorem vacuumCutoff_le_reservoirLevel (μ : X) (t : List I) (d : ℕ) (i : I) :
    vacuumCutoff t d ≤ reservoirLevel D μ t d i := by
  unfold reservoirLevel; omega

theorem vacuumCutoff_sub_choose (t : List I) (d : ℕ) :
    (vacuumCutoff t d : ℤ) - 2 * t.length.choose 2 = d + 1 := by
  unfold vacuumCutoff; push_cast; ring

variable (k : Type u) [CommRing k]

/-- The bubble substitution `θ` of the schedule (`SwappedNondegeneracy.md` §2). -/
def vacuumSubstitution (μ : X) (t : List I) (d : ℕ) : SKM.SYM D k ≃ₐ[k] SKM.SYM D k :=
  SKM.SYM.probeSubstitution D k (probeExponent D μ t d) (reservoirLevel D μ t d)

theorem vacuumSubstitution_weight (μ : X) (t : List I) (d : ℕ) :
    PreservesCoefficientWeight D (vacuumSubstitution D k μ t d).toLinearMap :=
  fun n _ hx => SKM.SYM.probeSubstitution_mem_coefficientAtMost D k _ _ n hx

end Schedule

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- **The vacuum block** at one external weight `μ`, upward word pair `t, t'` and
degree bound `d`: an upward module action with the vacuum data of
`SwappedNondegeneracy.md` §4 for the schedule of §2. The fields `bubbles_eq` and
`evaluation` are (A16) and (A18); `ideal_le` is the weight bound of
`SwappedVacuumCoordinates.md` §6 for the transformed last-boundary ideal. -/
structure SwappedVacuumBlock (μ : X) (t t' : List I) (d : ℕ) where
  /-- The upward module action. -/
  A : UpwardModuleAction D Sc μ
  /-- The vacuum vector of the source sector. -/
  vacuum : A.V t
  /-- The raw action of the reservoir coefficients on the source sector. -/
  raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)
  /-- (A16): source-placed normalized bubbles act as the substituted raw coefficients. -/
  bubbles_eq : ∀ a, A.bubbles cs t a = raw (vacuumSubstitution D k μ t d a)
  /-- The transformed last-boundary ideal. -/
  ideal : Submodule k (coefficientObj D Sc t ⟶ coefficientObj D Sc t')
  /-- Its weight bound `N₀ - 2·C(|t|, 2)`. -/
  ideal_le : ideal ≤ ExtendedAtLeast D Sc t t'
    ((vacuumCutoff t d : ℤ) - 2 * t.length.choose 2)
  /-- The vacuum coordinates on the target sector. -/
  coordinate : A.V t' →ₗ[k] ((coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸ ideal)
  /-- (A18): the literal evaluation at the reservoir-shifted vacuum. -/
  evaluation : ∀ (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')),
    coordinate (A.act t t' ((alpha D Sc μ).map f) (raw (vacuumSubstitution D k μ t d a) vacuum)) =
      ideal.mkQ (placementSign D Sc t t'
        (coefficientSubstitution D Sc (vacuumSubstitution D k μ t d) t t'
          (sourceCoefficientHom D Sc a f)))

namespace SwappedVacuumBlock
variable {D Sc cs} {μ : X} {t t' : List I} {d : ℕ}

/-- (A18) in terms of the raw coefficient: the reservoir coefficient `b` of the
vacuum evaluates to the placed source coefficient `b`. -/
theorem evaluation_raw (B : SwappedVacuumBlock D Sc cs μ t t' d) (b : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    B.coordinate (B.A.act t t' ((alpha D Sc μ).map f) (B.raw b B.vacuum)) =
      B.ideal.mkQ (placementSign D Sc t t' (sourceCoefficientHom D Sc b f)) := by
  have h := B.evaluation ((vacuumSubstitution D k μ t d).symm b) f
  rwa [AlgEquiv.apply_symm_apply, coefficientSubstitution_source,
    AlgEquiv.apply_symm_apply] at h

/-- A vacuum block is a vacuum evaluation, with substitution `θ`, placement the
ordered-source sign and bound `d + 1`. -/
def toSwappedVacuumEvaluation (B : SwappedVacuumBlock D Sc cs μ t t' d) :
    SwappedVacuumEvaluation D Sc cs μ t t' d :=
  UpwardModuleAction.toSwappedVacuumEvaluation D Sc cs B.A B.vacuum B.raw (vacuumSubstitution D k μ t d)
    (vacuumSubstitution_weight D k μ t d) B.bubbles_eq B.ideal ((d : ℤ) + 1)
    (by omega) (by simpa only [vacuumCutoff_sub_choose] using B.ideal_le)
    (placementSign D Sc t t') (fun _ hx => placementSign_mem_extendedAtMost D Sc hx)
    B.coordinate B.evaluation_raw

end SwappedVacuumBlock

section Field
variable {I X k : Type u} [AddCommGroup X] [Field k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- **Conditional field theorem.** Vacuum blocks at every equal-weight upward word
pair, external weight and degree bound imply the Nondegeneracy Conjecture. -/
theorem nondegeneracy_of_vacuum_blocks
    (h : ∀ (t t' : List I), SKM.wt D 0 (SKM.ups t) = SKM.wt D 0 (SKM.ups t') →
      ∀ (μ : X) (d : ℕ), Nonempty (SwappedVacuumBlock D Sc cs μ t t' d)) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_vacuum_evaluations fun t t' hw μ d =>
    (h t t' hw μ d).map SwappedVacuumBlock.toSwappedVacuumEvaluation

end Field

end OddMath.QuiverHecke
