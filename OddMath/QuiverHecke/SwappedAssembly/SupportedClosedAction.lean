/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SupportedActionLayers
import OddMath.QuiverHecke.SwappedAssembly.WhiskerEvaluation
import OddMath.SKM.SpanBubbleProd

/-! # Closed diagrams beside the strands in the complete supported action

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5, in the
matrix form of `docs/Nondegeneracy/SwappedActionAssembly.md`. A closed diagram `β = cl M`
in the rightmost region, placed to the right of the strands of an upward word
(`SKM.bubAt`), acts in the complete supported upward module action entrywise: at every
summand path `p` of the word, the entry of the image of `x` is the entry of `x` followed by
`F_p` applied to the entry of `β` at the rightmost sector
(`pointwiseUpwardModuleAction_act_bubAt_cl`). This is the evaluation of the bubbles of
`docs/Nondegeneracy/SwappedVacuumBubbles.md`, §5, in the chosen factor chart.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open OddMath.SKM

namespace SPath

universe uP
variable {I X : Type uP}

/-- Appending two empty paths and casting back is the identity. -/
theorem append_nil_nil_cast {l : List (Col I X)} {s t : Sector I} (p : SPath l s t)
    (h : l ++ [] ++ [] = l) : ((p.append (.nil t)).append (.nil t)).cast h = p := by
  induction p with
  | nil s => rfl
  | cons c side s hv p ih =>
    simp only [append]
    rw [cast_cons]
    exact congrArg _ (ih _)

end SPath

end OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance supportedClosedActionHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ) (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  [Finite I] (hF : ProbeActionInputs D Sc m cutoff bound ΛP ΛR hP hR)
  (Gs Ys : ∀ s, H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local notation "c" => elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR hF.dot
local notation "leftward" => pointwiseLeftwardData D Sc m cutoff bound ΛP ΛR hP hR hF.dot
local notation "gens" => ProbeReservoir.swappedGens (P) c leftward
local notation "action" => pointwiseUpwardModuleAction D Sc m cutoff bound ΛP ΛR hP hR hF.dot
        hF.window Gs Ys
local notation "E" => matrixEquiv D Sc m cutoff bound ΛP ΛR hP hR Gs Ys
attribute [local irreducible] elvProbeCrossCoeffOf

/-- **A closed diagram beside the strands, entry by entry.** In the complete supported
upward module action, the closed diagram `cl M` of the rightmost region `μ`, placed to the
right of the upward word of `t`, acts on the chosen-factor entries of `x` at the summand path
`p` by `F_p` of its entry at the rightmost sector. -/
theorem pointwiseUpwardModuleAction_act_bubAt_cl (μ : X) (t : List I)
    (M : List (SKM.LayerData I)) (hM : SKM.SChain [] M [])
    (x : matrixModule D Sc m cutoff bound ΛP ΛR Gs Ys (SKM.ob D μ (upWord t)))
    (s : Sector I)
    (τ : {τ : Sector I // (ΛP - contentWeight D τ.1) + (-ΛR + contentWeight D τ.2) =
      (SKM.ob D μ (upWord t)).endR})
    (p : SPath (SKM.ob D μ (upWord t)).word s τ.1) :
    E (SKM.ob D μ (upWord t))
        ((action μ).act t t (SKM.bubAt D Sc μ (upWord t) (SKM.cl D Sc μ [] [] M)) x) s τ p =
      E (SKM.ob D μ (upWord t)) x s τ p ≫
        ((P).pathFunctor p).map (ProbeReservoir.compDiag gens (SKM.mkD D μ M hM)
          (SPath.nil τ.1) (SPath.nil τ.1) (Ys τ.1).obj) := by
  classical
  have hw : SKM.SChain (upWord t) (M.map (SKM.whL (upWord t) [])) (upWord t) := by
    simpa only [List.append_nil] using hM.whisk (upWord t) []
  rw [SKM.bubAt_cl, SKM.cl_of hw]
  change E _ (((functorOfObligations D Sc m cutoff bound ΛP ΛR hP hR Gs Ys gens
    (pointwiseObligations D Sc m cutoff bound ΛP ΛR hP hR hF.dot hF.window Gs Ys)).map
      ((SKM.pres D Sc).diag (SKM.mkD D μ _ hw))).hom x) s τ p = _
  unfold functorOfObligations
  rw [Presentation.lift_diag]
  erw [LocalInterpretation.functor_map_apply]
  erw [ModuleInterpretation.congrModules_opList]
  change E _ ((E _).symm ((((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
    gens).toLocal.res _) ((((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
    gens).toLocal.opList _) ((((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj)
    gens).toLocal.ext _) (E _ x))))) s τ p = _
  rw [LinearEquiv.apply_symm_apply, SKM.layers_mkD, ← SKM.layList_whisker D μ (upWord t) [] hM]
  have eA : (SKM.ob D μ []).whisker (SKM.ob D μ (upWord t)) [] = SKM.ob D μ (upWord t) :=
    (SKM.ob_whisker D μ (upWord t) [] [] [] rfl).trans (by simp)
  let _ : Fintype (SPath (SKM.ob D μ []).word τ.1 τ.1) := Fintype.ofFinite _
  have key := ProbeReservoir.res_opList_ext_whisker_apply (P) gens (SKM.mkD D μ M hM)
    (SKM.ob D μ (upWord t)) [] (SKM.whiskerOK_ob D μ (upWord t) [] []) eA eA (E _ x)
    τ.2 τ.2 p (SPath.nil τ.1) (SPath.nil τ.1)
  have _ : Subsingleton (SPath (SKM.ob D μ []).word τ.1 τ.1) := SPath.subsingleton_nil _ _
  rw [Fintype.sum_subsingleton (ι := SPath (SKM.ob D μ []).word τ.1 τ.1) _ (SPath.nil τ.1)] at key
  have hp := SPath.append_nil_nil_cast p (congrArg Obj.word eA)
  have gen : ∀ (q : SPath (SKM.ob D μ (upWord t)).word s τ.1)
      (hq : ((p.append (SPath.nil τ.1)).append (SPath.nil τ.1)).cast (congrArg Obj.word eA) = q),
      ((((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj) gens).toLocal.res
          (SKM.ob D μ (upWord t)))
        ((((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj) gens).toLocal.opList
            ((Diagram.layers (SKM.mkD D μ M hM)).map (·.whisker (SKM.ob D μ (upWord t)) [])))
          ((((P).layerRep (fun s => (Gs s).obj) (fun s => (Ys s).obj) gens).toLocal.ext
              (SKM.ob D μ (upWord t))) (E _ x))) :
          (P).Mod (fun s => (Gs s).obj) (fun s => (Ys s).obj) (SKM.ob D μ (upWord t)))
          s τ q =
        E _ x s τ q ≫ eqToHom (congrArg (fun r => ((P).pathFunctor r).obj (Ys τ.1).obj)
          (hq.symm.trans hp)) ≫
          ((P).pathFunctor p).map (ProbeReservoir.compDiag gens (SKM.mkD D μ M hM)
            (SPath.nil τ.1) (SPath.nil τ.1) (Ys τ.1).obj) ≫
          eqToHom (congrArg (fun r => ((P).pathFunctor r).obj (Ys τ.1).obj)
            (hq.symm.trans hp).symm) := by
    intro q hq
    subst hq
    exact key
  refine (gen p hp).trans ?_
  simp

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
