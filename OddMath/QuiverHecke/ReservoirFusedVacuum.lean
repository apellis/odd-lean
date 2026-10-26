/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ReservoirCoverage
import OddMath.QuiverHecke.ReservoirVacuumDetection

/-! # Fused vacuum word modules and their regular coordinates

Ports the vacuum-word identification of
`Categorification/KLR/CyclotomicAction/VacuumProduct.lean` (the left colours
of a product family act at the vacuum through the cyclotomic quotient,
`wcoord_klrActAt_inl_wgen`) and its use in
`Categorification/KLR/Unfurling/GenericVacuumWordCoordinates.lean`.

`FusedVacuumWords` is the evaluation of an upward action on the word modules
of one vacuum: it is the output of the action, not a construction of it.
`RegularVacuumIdentification` records the identification of these modules
and operators with the connected regular reservoir modules of
`ReservoirRegular.lean`: the vacuum goes to the regular generator, affine
morphisms act by postcomposition and the reservoir coefficients act by
source-placed coefficients. From these identities alone,
`FusedVacuumWords.evaluation` constructs the fused-vacuum
`affine_coordinates` on every regular window, and
`FusedRegularVacuumFamily.toFamily` constructs the categorical `covers`
field. The normalized bubble formula remains a separate input; see
`ReservoirFusedBubbles.lean`.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory
open ReservoirWeights
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- The upward action evaluated on the word modules of a vacuum at weight `μ`.
`act_comp` is functoriality; `bubbles_eq` says that `bubbles` is the action of
the source-placed SKM bubbles. No injectivity is assumed. -/
structure FusedVacuumWords (μ : X) where
  V : List I → Type u
  [addV : ∀ t, AddCommGroup (V t)]
  [moduleV : ∀ t, Module k (V t)]
  act : ∀ t t', UpwardHom D Sc μ t t' →ₗ[k] (V t →ₗ[k] V t')
  act_comp : ∀ t t' t'' (f : UpwardHom D Sc μ t t') (g : UpwardHom D Sc μ t' t''),
    act t t'' (f ≫ g) = (act t' t'' g).comp (act t t' f)
  vacuum : ∀ t, V t
  bubbles : ∀ t, SKM.SYM D k →ₐ[k] Module.End k (V t)
  bubbles_eq : ∀ t a, bubbles t a =
    act t t (SKM.bubAt D Sc μ (upWord t) (SKM.betaSYM cs μ a))

attribute [instance] FusedVacuumWords.addV FusedVacuumWords.moduleV

variable {D Sc cs}

/-- Identification of fused vacuum words with the connected regular module at
`cutoff`. `coord s t` is the coordinate at source word `s`. The three laws
identify the vacuum, the affine operators and the reservoir coefficient
action; they are the cyclotomic content of the action, not a detection
hypothesis (no injectivity of `coord` is required for coordinates). -/
structure RegularVacuumIdentification {μ : X} (W : FusedVacuumWords D Sc cs μ)
    (cutoff : I → ℕ) where
  coord : ∀ s t, W.V t →ₗ[k] ReservoirQuotient D Sc cutoff s t
  coord_vacuum : ∀ t, coord t t (W.vacuum t) = reservoirRegularGenerator D Sc cutoff t
  coord_act : ∀ s t t' (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) v,
    coord s t' (W.act t t' ((alpha D Sc μ).map f) v) =
      reservoirPostcomp D Sc cutoff (sourceCoefficientHom D Sc 1 f) (coord s t v)
  reservoir : ∀ t, SKM.SYM D k →ₐ[k] Module.End k (W.V t)
  coord_reservoir : ∀ s t a v, coord s t (reservoir t a v) =
    reservoirPostcomp D Sc cutoff (sourceCoefficientHom D Sc a (𝟙 _)) (coord s t v)

namespace RegularVacuumIdentification
variable {μ : X} {W : FusedVacuumWords D Sc cs μ} {cutoff : I → ℕ}
  (Θ : RegularVacuumIdentification W cutoff)

/-- On the vacuum, an affine morphism after a coefficient is the regular class
of the source-placed coefficient morphism in the composite order. -/
theorem coord_vacuum_source (t t' : List I) (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) :
    Θ.coord t t' (W.act t t' ((alpha D Sc μ).map f) (Θ.reservoir t a (W.vacuum t))) =
      reservoirPostcomp D Sc cutoff (sourceCoefficientHom D Sc 1 f)
        (reservoirPostcomp D Sc cutoff (sourceCoefficientHom D Sc a (𝟙 _))
          (reservoirRegularGenerator D Sc cutoff t)) := by
  rw [Θ.coord_act, Θ.coord_reservoir, Θ.coord_vacuum]

end RegularVacuumIdentification

section Field
variable {K : Type u} [Field K] {S : SKM.Scalars D K} {cK : SKM.CScalars S}

/-- The recovery map of a regular window, chosen once for each pair of words. -/
def regularRecover (h : I → ℤ) (m : ℕ) (t t' : List I) :
    ReservoirQuotient D S (reservoirLevel h m) t t' →ₗ[K]
      ReservoirQuotient D S (reservoirLevel h m) t t' :=
  (regularVacuumWindow_coordinates D S h m t t').choose

theorem regularRecover_spec (h : I → ℤ) (m : ℕ) (t t' : List I) (a : SKM.SYM D K)
    (f : (pres D S).obj (ob D t) ⟶ (pres D S).obj (ob D t'))
    (hf : sourceCoefficientHom D S a f ∈
      ExtendedAtMost D S t t' (regularVacuumWindow m t.length)) :
    regularRecover (D := D) (S := S) h m t t'
      (reservoirPostcomp D S (reservoirLevel h m) (sourceCoefficientHom D S 1 f)
        (reservoirPostcomp D S (reservoirLevel h m) (sourceCoefficientHom D S a (𝟙 _))
          (reservoirRegularGenerator D S (reservoirLevel h m) t))) =
      (ELVRelationSpan D S (reservoirLevel h m) t t').mkQ (sourceCoefficientHom D S a f) :=
  (regularVacuumWindow_coordinates D S h m t t').choose_spec a f hf

/-- The fused vacuum evaluation at a regular cutoff. Its `affine_coordinates`
field is proved from the regular identification and C0; the window is the
regular window at every strand number. -/
def FusedVacuumWords.evaluation {μ : X} (W : FusedVacuumWords D S cK μ) (h : I → ℤ) (m : ℕ)
    (Θ : RegularVacuumIdentification W (reservoirLevel h m)) :
    ReservoirVacuumEvaluation D S cK μ (reservoirLevel h m) where
  V := W.V
  act := W.act
  act_comp := W.act_comp
  vacuum := W.vacuum
  bubbles := W.bubbles
  bubbles_eq := W.bubbles_eq
  reservoir := Θ.reservoir
  recover t t' := (regularRecover (D := D) (S := S) h m t t').comp (Θ.coord t t')
  window t _ := regularVacuumWindow m t.length
  affine_coordinates t t' a f hf := by
    rw [LinearMap.comp_apply, Θ.coord_vacuum_source]
    exact regularRecover_spec h m t t' a f hf

/-- The bubble formula on the fused evaluation is literally the equality of the
fused bubble action with the identified reservoir action. -/
theorem FusedVacuumWords.evaluation_normalizedBubbleFormula {μ : X}
    (W : FusedVacuumWords D S cK μ) (h : I → ℤ) (m : ℕ)
    (Θ : RegularVacuumIdentification W (reservoirLevel h m))
    (hb : ∀ t, W.bubbles t = Θ.reservoir t) :
    (W.evaluation h m Θ).NormalizedBubbleFormula where
  elementary t i n := by simp only [FusedVacuumWords.evaluation, hb]
  exterior t i := by simp only [FusedVacuumWords.evaluation, hb]

variable (D S cK) in
/-- A cofinal family of fused vacua at the fixed external weight `μ`, one for
each reservoir level `m`, with their regular identifications. -/
structure FusedRegularVacuumFamily (μ : X) (h : I → ℤ) where
  words : ℕ → FusedVacuumWords D S cK μ
  regular : ∀ m, RegularVacuumIdentification (words m) (reservoirLevel h m)

/-- The categorical `covers` field is supplied by the cofinal regular windows.
The only remaining input is the bubble formula at each level. -/
def FusedRegularVacuumFamily.toFamily {μ : X} {h : I → ℤ}
    (F : FusedRegularVacuumFamily D S cK μ h)
    (hb : ∀ m, ((F.words m).evaluation h m (F.regular m)).NormalizedBubbleFormula) :
    FusedFixedWeightFamily D S cK μ where
  Index := ULift ℕ
  cutoff m := reservoirLevel h m.down
  evaluation m := (F.words m.down).evaluation h m.down (F.regular m.down)
  normalizedBubbleFormula m := hb m.down
  covers t _ d := by
    obtain ⟨m, N, hw, hN, hb⟩ := regularVacuumWindow_covers h t.length d
    exact ⟨⟨m⟩, N, hw, hN, hb⟩

end Field
end OddMath.QuiverHecke
