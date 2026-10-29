/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SpectatorSeparation
import OddMath.SKM.ReservoirBubbleCoordinates

/-! # Reservoir-vacuum detection at a prescribed weight

Conditional consumers for C1–C3 of `docs/Nondegeneracy/GeneralRoute.md`.
The interface is the extracted part of a fused action, not a construction of
fusion. In contrast to `SpectatorEvaluation`, its coordinate module has only
active strands. Both interfaces remain useful: the spectator consumer requires
additional joint detection, while the reservoir consumer proves it by C0.

The categorical normalized bubble formula is an explicit generator hypothesis.
In particular it is not deduced from the existence of independent scalar
parameters. The affine coordinate law is on the *same* reservoir module and
includes arbitrary, ordered multicolour exterior coefficients.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical TensorProduct
universe u w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cs : SKM.CScalars Sc)

/-- The connected reservoir quotient on the active words, without spectators. -/
abbrev ReservoirQuotient (cutoff : I → ℕ) (t t' : List I) :=
  (coefficientObj D Sc t ⟶ coefficientObj D Sc t') ⧸ ELVRelationSpan D Sc cutoff t t'

/-- C0 on any prescribed colourwise parity schedule. In particular `ε = 0`
and `ε = 1` give even and odd cutoffs; mixed choices use the same proof. This
is algebraic separation, not realization of the cutoffs by dominant weights. -/
theorem reservoir_parity_cutoffs_detect (ε : I → ℕ) (t t' : List I)
    (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t')
    (hf : ∀ m, (ELVRelationSpan D Sc (fun i => 2 * m + ε i) t t').mkQ f = 0) : f = 0 := by
  apply cofinal_elv_quotients_with_spectators_detect D Sc
    (fun m i => 2 * m + ε i) (fun N => ⟨N, fun i => by omega⟩) [] t t' f
  exact hf

/-- The linear data extracted from fusion at a highest-probe vacuum. All weights
in `act` are literally `μ`; increasing a cutoff does not change this weight.
`reservoir` is the coefficient action after the specified normalization. The
normalization's categorical identification is NOT part of these data.

`affine_coordinates` must be constructed from the connected reservoir regular
module. It cannot be supplied by unrelated rank-one tests. No injection of an
SKM Hom space, or of the action, is assumed. -/
structure ReservoirVacuumEvaluation (μ : X) (cutoff : I → ℕ) where
  V : List I → Type w
  [addV : ∀ t, AddCommGroup (V t)]
  [moduleV : ∀ t, Module k (V t)]
  act : ∀ t t', UpwardHom D Sc μ t t' →ₗ[k] (V t →ₗ[k] V t')
  act_comp : ∀ t t' t'' (f : UpwardHom D Sc μ t t') (g : UpwardHom D Sc μ t' t''),
    act t t'' (f ≫ g) = (act t' t'' g).comp (act t t' f)
  vacuum : ∀ t, V t
  bubbles : ∀ t, SKM.SYM D k →ₐ[k] Module.End k (V t)
  bubbles_eq : ∀ t a, bubbles t a =
    act t t (SKM.bubAt D Sc μ (upWord t) (SKM.betaSYM cs μ a))
  reservoir : ∀ t, SKM.SYM D k →ₐ[k] Module.End k (V t)
  recover : ∀ t t', V t' →ₗ[k] ReservoirQuotient D Sc cutoff t t'
  window : List I → List I → ℕ
  affine_coordinates : ∀ t t' (a : SKM.SYM D k)
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')),
    sourceCoefficientHom D Sc a f ∈ ExtendedAtMost D Sc t t' (window t t') →
    recover t t' (act t t' ((alpha D Sc μ).map f) (reservoir t a (vacuum t))) =
      (ELVRelationSpan D Sc cutoff t t').mkQ (sourceCoefficientHom D Sc a f)

attribute [instance] ReservoirVacuumEvaluation.addV ReservoirVacuumEvaluation.moduleV

variable {D Sc cs}
namespace ReservoirVacuumEvaluation
variable {μ : X} {cutoff : I → ℕ} (E : ReservoirVacuumEvaluation D Sc cs μ cutoff)

/-- C1's remaining categorical calculation, stated on the correctly indexed
normalized elementary generators `e_{n+1}` and on each distinct odd generator.
If a probe series or unit sign is present, `reservoir` must include its proved
normalization and `affine_coordinates` must undo it on the chosen window.
This hypothesis is not asserted for an unconstructed fused action. -/
structure NormalizedBubbleFormula : Prop where
  elementary : ∀ t i n,
    E.bubbles t (SKM.SYM.e D k i n) = E.reservoir t (SKM.SYM.e D k i n)
  exterior : ∀ t i,
    E.bubbles t (SKM.SYM.delta D k i) = E.reservoir t (SKM.SYM.delta D k i)

/-- C1: the multicolour generator formula extends to the whole coefficient
algebra, hence to ordered products of exterior generators of different colours. -/
theorem normalized_bubbles (h : E.NormalizedBubbleFormula) (t : List I) :
    E.bubbles t = E.reservoir t := by
  apply SKM.SYM.hom_ext
  intro g
  cases g with
  | inl p => exact h.elementary t p.1 p.2
  | inr i => exact h.exterior t i

/-- In particular the source-placed categorical odd bubble is the reservoir's
own exterior coefficient, not an odd parameter from the probe. -/
theorem odd_bubble_vacuum (h : E.NormalizedBubbleFormula) (t : List I)
    (i : {i : I // D.parity i = 1}) :
    E.act t t (SKM.bubAt D Sc μ (upWord t) (SKM.oddBubble cs i.1 μ)) (E.vacuum t) =
      E.reservoir t (SKM.SYM.delta D k i) (E.vacuum t) := by
  rw [← SKM.betaSYM_delta cs μ i, ← E.bubbles_eq, E.normalized_bubbles h]

/-- Evaluation on the reservoir vacuum followed by connected coordinates. -/
def observe (t t' : List I) : UpwardHom D Sc μ t t' →ₗ[k]
    ReservoirQuotient D Sc cutoff t t' where
  toFun f := E.recover t t' (E.act t t' f (E.vacuum t))
  map_add' := by intros; simp
  map_smul' := by intros; simp

/-- C2 on pure tensors follows from composition, the bubble formula and the
reservoir affine coordinates. There is no spectator length in this equation. -/
theorem observe_source (h : E.NormalizedBubbleFormula) (t t' : List I)
    (a : SKM.SYM D k) (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    (hf : sourceCoefficientHom D Sc a f ∈ ExtendedAtMost D Sc t t' (E.window t t')) :
    E.observe t t' (upwardCoefficientMap D Sc cs μ t t' (sourceCoefficientHom D Sc a f)) =
      (ELVRelationSpan D Sc cutoff t t').mkQ (sourceCoefficientHom D Sc a f) := by
  rw [upwardCoefficientMap_source]
  change E.recover t t' (E.act t t' (_ ≫ _) (E.vacuum t)) = _
  rw [E.act_comp]
  change E.recover t t' (E.act t t' _ (E.act t t _ (E.vacuum t))) = _
  rw [← E.bubbles_eq, E.normalized_bubbles h]
  exact E.affine_coordinates t t' a f hf

/-- C2 for bounded joint upward × bubble coordinates. Span induction
retains the signed coefficient extension; no factorization by colours occurs. -/
theorem observe_coefficient (h : E.NormalizedBubbleFormula) (t t' : List I)
    (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t')
    (hf : f ∈ ExtendedAtMost D Sc t t' (E.window t t')) :
    E.observe t t' (upwardCoefficientMap D Sc cs μ t t' f) =
      (ELVRelationSpan D Sc cutoff t t').mkQ f := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨a, i⟩, hi, rfl⟩ := hf
    rw [extensionBasis_apply]
    apply E.observe_source h
    rw [← extensionBasis_apply]
    exact Submodule.subset_span ⟨(a, i), hi, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul r x _ hx => simpa only [map_smul] using congrArg (r • ·) hx

/-- A nonzero vector in a sufficiently large observation window forces the
chosen cyclic vector to be nonzero. Thus coverage cannot be discharged by a
zero module or by a zero vacuum. -/
theorem vacuum_ne_zero_of_window (h : E.NormalizedBubbleFormula) (t t' : List I)
    (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t') {d : ℕ}
    (hf : f ∈ ExtendedAtMost D Sc t t' d) (hw : d ≤ E.window t t') (hne : f ≠ 0)
    {N : ℕ} (hN : ∀ i, N ≤ cutoff i)
    (hb : d + 2 * t.length.choose 2 < N) : E.vacuum t ≠ 0 := by
  intro hv
  have hmem : f ∈ ExtendedAtMost D Sc t t' (E.window t t') :=
    (Submodule.span_mono (Set.image_mono (fun _ hi => hi.trans hw))) hf
  have hz : (ELVRelationSpan D Sc cutoff t t').mkQ f = 0 := by
    rw [← E.observe_coefficient h t t' f hmem]
    simp [observe, hv]
  have hinj := elv_quotient_injective_on_extendedAtMost D Sc (t := t) (t' := t')
    (d := d) hN hb
  exact hne (congrArg Subtype.val (hinj (a₁ := ⟨f, hf⟩) (a₂ := 0) (by simpa using hz)))

end ReservoirVacuumEvaluation
variable (D Sc cs)

/-- Fixed-weight data demanded of A2/A3, with the C1 formula explicitly separate
from fusion existence. Cutoffs can have arbitrary colour-dependent parity.
There is no claim here that weights with these cutoffs have been constructed. -/
structure FusedFixedWeightFamily (μ : X) where
  Index : Type u
  cutoff : Index → I → ℕ
  evaluation : ∀ a, ReservoirVacuumEvaluation D Sc cs μ (cutoff a)
  normalizedBubbleFormula : ∀ a, (evaluation a).NormalizedBubbleFormula
  covers : ∀ t t' d, ∃ a N, d ≤ (evaluation a).window t t' ∧
    (∀ i, N ≤ cutoff a i) ∧ d + 2 * t.length.choose 2 < N

namespace FusedFixedWeightFamily
variable {D Sc cs} {μ : X} (F : FusedFixedWeightFamily D Sc cs μ)
include F

/-- C0 consumes the joint C2 identity, with the number of active strands fixed.
The proof covers even, odd, and mixed cutoff parities without modification. -/
theorem vacuum_evaluations_jointly_detect (t t' : List I)
    (f : coefficientObj D Sc t ⟶ coefficientObj D Sc t')
    (hf : ∀ a, (F.evaluation a).observe t t' (upwardCoefficientMap D Sc cs μ t t' f) = 0) :
    f = 0 := by
  obtain ⟨d, hd⟩ := exists_mem_extendedAtMost D Sc t t' f
  obtain ⟨a, N, hw, hN, hb⟩ := F.covers t t' d
  have hmem : f ∈ ExtendedAtMost D Sc t t' ((F.evaluation a).window t t') :=
    (Submodule.span_mono (Set.image_mono (fun _ hi => hi.trans hw))) hd
  have he := (F.evaluation a).observe_coefficient (F.normalizedBubbleFormula a) t t' f hmem
  have hz : (ELVRelationSpan D Sc (F.cutoff a) t t').mkQ f = 0 := he.symm.trans (hf a)
  have hinj := elv_quotient_injective_on_extendedAtMost D Sc (t := t) (t' := t')
    (d := d) hN hb
  exact congrArg Subtype.val (hinj (a₁ := ⟨f, hd⟩) (a₂ := 0) (by simpa using hz))

/-- C3 at the prescribed external weight. The family contains no injectivity
hypothesis; detection is supplied by the independently checked C0 theorem. -/
theorem upwardCoefficientMap_injective (t t' : List I) :
    Function.Injective (upwardCoefficientMap D Sc cs μ t t') := by
  intro f g h
  apply sub_eq_zero.mp
  apply F.vacuum_evaluations_jointly_detect t t' (f - g)
  intro a
  rw [map_sub, h, sub_self, map_zero]

/-- C3 in matching coordinates at the fixed weight, for every complete choice
of upward matching representatives. No change of weight is used. -/
theorem upward_independence_at (t t' : List I)
    (U : SKM.MatchingBasisChoice (upWord t) (upWord t')) :
    Function.Injective (U.expansion cs μ) := by
  by_cases hlen : t.length = t'.length
  · let C := SKM.CanonicalUpward.choiceList t t' hlen
    have hC : Function.Injective (C.expansion cs μ) :=
      canonicalChoice_independence D Sc cs C
        (SKM.CanonicalUpward.choiceList_word t t' hlen)
        (SKM.CanonicalUpward.choiceList_word_spec t t' hlen) μ
        (F.upwardCoefficientMap_injective t t')
    exact U.expansion_injective_of_choice cs μ C hC
  · exact upward_choice_injective_of_length_ne D Sc cs hlen μ U

end FusedFixedWeightFamily

/-- C3 for the oriented reduction, conditional on fused reservoir data at each
weight. A2, A3, and the normalized categorical bubble formula remain premises. -/
theorem upward_independence_of_fused_fixed_weight_families
    (F : ∀ μ, FusedFixedWeightFamily D Sc cs μ) : SKM.WeakMate.UpwardIndependence cs := by
  apply upward_independence_of_coefficientMap D Sc cs
  intro t t' _ μ
  exact (F μ).upwardCoefficientMap_injective t t'

end OddMath.QuiverHecke
