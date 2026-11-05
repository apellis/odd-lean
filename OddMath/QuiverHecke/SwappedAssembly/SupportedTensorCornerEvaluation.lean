import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorLayerSquares
import OddMath.QuiverHecke.SwappedAssembly.SupportedActionAlphaLayers
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorVacuumCoefficientClass
import OddMath.QuiverHecke.SwappedVacuum.CornerLayerSquare
import OddMath.QuiverHecke.VacuumCornerChartCoherence

/-! # The corner evaluation of the swapped probe-reservoir action

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, in the
research scope of `FieldScopeBoundary.md`; `SwappedVacuumCoordinates.md` §§2–7.

For the swapped action `pointwiseUpwardModuleAction` on the tensor source and target
families of a source word `s`, at the external weight `ΛP - ΛR`, this file builds a
`VacuumCornerEvaluation`:

* the ideal at a target word `t` is the transformed ideal
  `PowerWordQuotientCoordinates.kernel s t`;
* the evaluation at `t` is the canonical quotient observation along the all-reservoir
  vacuum path of the labelled word of `t` when that path exists (the formal content of
  `t` is that of `s`), and zero otherwise;
* the generator squares are the dot and crossing layer observations
  (`tensorMatrixQuotientObservation_dot_of_eq`, `_sameCross_of_eq`, `_cross_of_eq`) on
  path-carrying words; layers preserve formal content, so on the other words both sides
  vanish, the ideal being closed under right composition;
* the vacuum value is `tensorWordQuotientObservation_coefficient_vacuum`.

By `VacuumCornerEvaluation.chartCoherence`, its coordinates satisfy
`VacuumChartCoherence` for the tensor matrix vacuum and the raw coefficient action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly

namespace SPath
universe u
variable {I X : Type u}

/-- An upward path into the probe vacuum removes exactly the word content from the
reservoir. -/
theorem content_eq {w : List (Col I X)} {s t : Sector I} (p : SPath w s t)
    (hw : ∀ c ∈ w, c.l.1 = true) (ht : t.1 = 0) : s.2 = wordContent w + t.2 := by
  induction p with
  | nil s => simp [wordContent]
  | @cons w t c side s hv p ih =>
    have hc := hw c List.mem_cons_self
    have hw' : ∀ d ∈ w, d.l.1 = true := fun d hd => hw d (List.mem_cons_of_mem _ hd)
    have ih := ih hw' ht
    rcases c with ⟨⟨b, i⟩, r⟩
    cases b with
    | false => cases hc
    | true =>
      obtain rfl := side_eq_false_of_upward_probe_zero i side p hw' ht
      have hv' : 1 ≤ s.2 i := hv
      have ih' : s.2 - Finsupp.single i 1 = wordContent w + t.2 := ih
      have hle : Finsupp.single i 1 ≤ s.2 := Finsupp.single_le_iff.mpr hv'
      show s.2 = Finsupp.single i 1 + wordContent w + t.2
      rw [add_assoc, ← ih', add_tsub_cancel_of_le hle]

/-- The formal content depends only on the colours of the word. -/
theorem wordContent_eq_sum (w : List (Col I X)) :
    wordContent w =
      ((w.map (fun a : Col I X => a.l.2)).map (fun i => Finsupp.single i 1)).sum := by
  induction w with
  | nil => rfl
  | cons c w ih => simp only [wordContent, List.map_cons, List.sum_cons, ih]

end SPath

namespace SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance tensorCornerEvaluationHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C

section Colours
variable {I X : Type u} [AddCommGroup X] (D : Datum I X)

/-- The colours of a labelled upward word are the word itself. -/
theorem wd_upWord_colours (x : X) (t : List I) :
    (SKM.wd D x (upWord t)).map (fun (a : SKM.Col I X) => a.l.2) = t := by
  induction t with
  | nil => rfl
  | cons i t ih =>
    simpa only [upWord, List.map_cons, wd_cons] using congrArg (List.cons i) ih

/-- The left context colours of a labelled layer. -/
theorem lay_left_colours (ν : X) (left right : List I) (g : SKM.Shape I) :
    List.reverse (List.reverse (List.map (fun (a : SKM.Col I X) => a.l.2)
      (Layer.left (SKM.lay D ν (upWord left) g (upWord right))))) = left := by
  rw [List.reverse_reverse]
  exact wd_upWord_colours D _ left

/-- The right context colours of a labelled layer. -/
theorem lay_right_colours (ν : X) (left right : List I) (g : SKM.Shape I) :
    List.reverse (List.reverse (List.map (fun (a : SKM.Col I X) => a.l.2)
      (Layer.right (SKM.lay D ν (upWord left) g (upWord right))))) = right := by
  rw [List.reverse_reverse]
  exact wd_upWord_colours D _ right

/-- A generating layer of `H` permutes the colours of its boundary word. -/
theorem layer_word_perm (G : Layer (QuiverHecke.sig D)) : G.dom.word.Perm G.cod.word := by
  obtain ⟨start, left, gen, right⟩ := G
  cases gen with
  | dot i => exact List.Perm.refl _
  | cross i j =>
    exact List.Perm.append_right _ (List.Perm.append_left _ (List.Perm.swap _ _ _))

end Colours

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR) (s : List I)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "cS" => tensorSourceContent D ΛP ΛR s

omit [CommRing k] [Fintype I] in
/-- The formal content of the labelled upward word of `t`. -/
theorem tensorSourceLabels_content (t : List I) :
    SPath.wordContent (tensorSourceLabels D ΛP ΛR t) =
      (t.map (fun i => Finsupp.single i 1)).sum := by
  rw [SPath.wordContent_eq_sum, tensorSourceLabels_colors]

omit [CommRing k] [Fintype I] in
/-- Generating layers preserve the formal content of the labelled words. -/
theorem tensorSourceLabels_content_layer (G : Layer (QuiverHecke.sig D)) :
    SPath.wordContent (tensorSourceLabels D ΛP ΛR G.cod.word) =
      SPath.wordContent (tensorSourceLabels D ΛP ΛR G.dom.word) := by
  rw [tensorSourceLabels_content, tensorSourceLabels_content]
  exact ((layer_word_perm D G).map _).sum_eq.symm

/-- **The corner evaluation at a target word**: the canonical quotient observation
along the all-reservoir vacuum path when the content of `t` is that of `s`, and zero
otherwise. -/
def tensorCornerEv (t : List I) :
    tensorWordMatrixModule D Sc m cutoff ΛP ΛR L s t →ₗ[k]
      ((coefficientObj D Sc s ⟶ coefficientObj D Sc t) ⧸
        PowerWordQuotientCoordinates.kernel D Sc cutoff L s t) := by
  classical
  exact if h : SPath.wordContent (tensorSourceLabels D ΛP ΛR t) + 0 = cS then
    tensorWordQuotientObservation D Sc cutoff L m ΛP ΛR hP hR s t
      (h ▸ SPath.reservoirPath _ (tensorSourceLabels_up D ΛP ΛR t) 0)
  else 0

/-- On a path-carrying word the corner evaluation is the observation along any path. -/
theorem tensorCornerEv_eq (t : List I)
    (p : SPath (tensorSourceLabels D ΛP ΛR t) (0,cS) (0,0)) :
    tensorCornerEv D Sc m cutoff ΛP ΛR L hP hR s t =
      tensorWordQuotientObservation D Sc cutoff L m ΛP ΛR hP hR s t p := by
  have h : SPath.wordContent (tensorSourceLabels D ΛP ΛR t) + 0 = cS :=
    (SPath.content_eq p (tensorSourceLabels_up D ΛP ΛR t) rfl).symm
  unfold tensorCornerEv
  split
  · exact tensorWordQuotientObservation_path_independent D Sc cutoff L m ΛP ΛR hP hR s t _ _
  · exact absurd h ‹_›

/-- Off the content of `s` the corner evaluation vanishes. -/
theorem tensorCornerEv_of_ne (t : List I)
    (h : ¬ SPath.wordContent (tensorSourceLabels D ΛP ΛR t) + 0 = cS) :
    tensorCornerEv D Sc m cutoff ΛP ΛR L hP hR s t = 0 := by
  unfold tensorCornerEv
  split
  · exact absurd ‹_› h
  · rfl

variable (sy : Symmetrizer D) (hc : Sc.Homogeneous)
local notation "c" => elvProbeCrossCoeffOf D Sc m cutoff N ΛP ΛR hP hR
    (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
      (parameterTwist_homogeneous D Sc hc) N)
local notation "leftward" => pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR
        (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
          (parameterTwist_homogeneous D Sc hc) N)
local notation "action" => pointwiseUpwardModuleAction D Sc m cutoff N ΛP ΛR hP hR
        (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
          (parameterTwist_homogeneous D Sc hc) N)
        (SupportedSectors.reservoirWindowIdeal D Sc m cutoff N ΛP ΛR hP hR sy hc)
  (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L)

/-- The generator square of the corner evaluation on one presented layer. -/
theorem tensorCornerEv_layer (G : Layer (QuiverHecke.sig D)) (hv : G.Valid)
    (v : (action (ΛP - ΛR)).V G.dom.word)
    (y : coefficientObj D Sc s ⟶ coefficientObj D Sc G.dom.word)
    (hy : tensorCornerEv D Sc m cutoff ΛP ΛR L hP hR s G.dom.word v =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s G.dom.word).mkQ y) :
    tensorCornerEv D Sc m cutoff ΛP ΛR L hP hR s G.cod.word
        ((action (ΛP - ΛR)).act G.dom.word G.cod.word
          ((QuiverHecke.alpha D Sc (ΛP - ΛR)).map
            ((QuiverHecke.pres D Sc).diag (Diagram.ofLayer G hv))) v) =
      (PowerWordQuotientCoordinates.kernel D Sc cutoff L s G.cod.word).mkQ
        (y ≫ coefficientHom D Sc 1 (t := G.dom.word) (t' := G.cod.word)
          ((QuiverHecke.pres D Sc).diag (Diagram.ofLayer G hv))) := by
  classical
  rw [pointwiseUpwardModuleAction_act_ofLayer D Sc m cutoff N ΛP ΛR hP hR sy hc
      (tensorSourceFamily D Sc m cutoff ΛP ΛR L s) (tensorTargetFamily D Sc m cutoff ΛP ΛR L)
      (ΛP - ΛR) G hv,
    coefficientHom_one_ofLayer D Sc G hv]
  have hcont := tensorSourceLabels_content_layer D ΛP ΛR G
  by_cases h : SPath.wordContent (tensorSourceLabels D ΛP ΛR G.dom.word) + 0 = cS
  · have h' : SPath.wordContent (tensorSourceLabels D ΛP ΛR G.cod.word) + 0 = cS := by
      rw [hcont]; exact h
    have pA := h ▸ SPath.reservoirPath _ (tensorSourceLabels_up D ΛP ΛR G.dom.word) 0
    have pB := h' ▸ SPath.reservoirPath _ (tensorSourceLabels_up D ΛP ΛR G.cod.word) 0
    rw [tensorCornerEv_eq D Sc m cutoff ΛP ΛR L hP hR s _ pA,
      tensorWordQuotientObservation_apply] at hy
    rw [tensorCornerEv_eq D Sc m cutoff ΛP ΛR L hP hR s _ pB,
      tensorWordQuotientObservation_apply]
    obtain ⟨start, left, gen, right⟩ := G
    cases gen with
    | dot i =>
      exact tensorMatrixQuotientObservation_dot_of_eq D Sc m cutoff ΛP ΛR L hP hR s c leftward
        (ΛP - ΛR) (upWord left) (upWord right) i
        (lay_left_colours D _ left right _) (lay_right_colours D _ left right _)
        ((QuiverHecke.label D (ΛP - ΛR)).dom_eq hv) ((QuiverHecke.label D (ΛP - ΛR)).cod_eq hv)
        (tensorWordVacuumEndpoint D ΛP ΛR _) (tensorWordVacuumEndpoint D ΛP ΛR _)
        pA (tensorSourceLabels_up D ΛP ΛR _) pB (tensorSourceLabels_up D ΛP ΛR _)
        (tensorSourceLabels_colors D ΛP ΛR _) (tensorSourceLabels_colors D ΛP ΛR _) v y hy
    | cross i j =>
      by_cases hij : i = j
      · subst hij
        exact tensorMatrixQuotientObservation_sameCross_of_eq D Sc m cutoff ΛP ΛR L hP hR s c
          leftward (ΛP - ΛR) (upWord left) (upWord right) i
          (lay_left_colours D _ left right _) (lay_right_colours D _ left right _)
          ((QuiverHecke.label D (ΛP - ΛR)).dom_eq hv) ((QuiverHecke.label D (ΛP - ΛR)).cod_eq hv)
          (tensorWordVacuumEndpoint D ΛP ΛR _) (tensorWordVacuumEndpoint D ΛP ΛR _)
          pA (tensorSourceLabels_up D ΛP ΛR _) pB (tensorSourceLabels_up D ΛP ΛR _)
          (tensorSourceLabels_colors D ΛP ΛR _) (tensorSourceLabels_colors D ΛP ΛR _) v y hy
      · exact tensorMatrixQuotientObservation_cross_of_eq D Sc m cutoff ΛP ΛR L hP hR s c
          leftward (ΛP - ΛR) (upWord left) (upWord right) i j hij
          (lay_left_colours D _ left right _) (lay_right_colours D _ left right _)
          ((QuiverHecke.label D (ΛP - ΛR)).dom_eq hv) ((QuiverHecke.label D (ΛP - ΛR)).cod_eq hv)
          (tensorWordVacuumEndpoint D ΛP ΛR _) (tensorWordVacuumEndpoint D ΛP ΛR _)
          pA (tensorSourceLabels_up D ΛP ΛR _) pB (tensorSourceLabels_up D ΛP ΛR _)
          (tensorSourceLabels_colors D ΛP ΛR _) (tensorSourceLabels_colors D ΛP ΛR _) v y hy
  · have h' : ¬ SPath.wordContent (tensorSourceLabels D ΛP ΛR G.cod.word) + 0 = cS := by
      rw [hcont]; exact h
    have e := tensorCornerEv_of_ne D Sc m cutoff ΛP ΛR L hP hR s G.dom.word h
    have e' := tensorCornerEv_of_ne D Sc m cutoff ΛP ΛR L hP hR s G.cod.word h'
    have hy0 : y ∈ PowerWordQuotientCoordinates.kernel D Sc cutoff L s G.dom.word :=
      (Submodule.Quotient.mk_eq_zero _).mp
        (hy.symm.trans ((LinearMap.congr_fun e v).trans (LinearMap.zero_apply v)))
    refine (LinearMap.congr_fun e' _).trans ((LinearMap.zero_apply _).trans ?_)
    exact ((Submodule.Quotient.mk_eq_zero _).mpr (TransformedIdeal.comp_mem D Sc hy0 _)).symm

/-- **The corner evaluation of the swapped action** at the source word `s`, for the
tensor matrix vacuum and the raw coefficient action. -/
def tensorCornerEvaluation :
    VacuumCornerEvaluation D Sc (action (ΛP - ΛR)) s
      (tensorMatrixCoefficientAction D Sc m cutoff ΛP ΛR L s (SKM.ob D (ΛP - ΛR) (upWord s)))
      (tensorMatrixVacuum D Sc m cutoff ΛP ΛR L s) where
  K t := PowerWordQuotientCoordinates.kernel D Sc cutoff L s t
  ev t := tensorCornerEv D Sc m cutoff ΛP ΛR L hP hR s t
  ev_layer G hv v y hy := tensorCornerEv_layer D Sc m cutoff ΛP ΛR L hP hR s sy hc G hv v y hy
  ev_vacuum a := by
    rw [tensorCornerEv_eq D Sc m cutoff ΛP ΛR L hP hR s s (tensorSourcePath D ΛP ΛR s)]
    exact tensorWordQuotientObservation_coefficient_vacuum D Sc cutoff L m ΛP ΛR hP hR s a

end SupportedSectors
end OddMath.QuiverHecke.SwappedAssembly
