import OddMath.SKM.Rho.InterchangeContexts
import OddMath.SKM.Rho.AllUpwardKernels
import OddMath.SKM.Rho.Inversion
import OddMath.SKM.Rho.Adjunction
import StringDiagrams.InterchangeLayers

/-!
# Relations for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
The corrected linear evaluator annihilates all 25 defining relation families
and signed interchange in arbitrary contexts of the existing presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoEvaluator
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

private theorem rhoLin_relation_other (t : k) (ht : t ^ 2 = -1)
    (R : Rel D) (hR : ¬ RhoUpwardKernel.IsUpward R) (ν : X) (hs : wt D R.ν R.dom = ν) (hr : wt D R.ν R.cod = ν) :
    rhoLin (sy := sy) (hc := hc) t ν R.ν hs hr (relation D Sc R) = 0 := by
  cases R with
  | zigE i μ => subst ν; exact RhoInversionKernel.kernel_zigE (sy := sy) (hc := hc) t μ i
  | zigF i μ => subst ν; exact RhoInversionKernel.kernel_zigF (sy := sy) (hc := hc) t μ i
  | invNe₁ i j μ hij => subst ν; exact RhoInversionKernel.kernel_invNe₁ (sy := sy) (hc := hc) t ht μ i j hij
  | invNe₂ i j μ hij => subst ν; exact RhoInversionKernel.kernel_invNe₂ (sy := sy) (hc := hc) t ht μ i j hij
  | invP₁ i μ hh =>
    have e : μ = ν := by simpa [Rel.ν, Rel.dom, wt_cons, sh, up, dn] using hs
    cases e
    exact RhoInversionKernel.kernel_invP₁ (sy := sy) (hc := hc) t ht ν i hh
  | invP₂ i μ hh =>
    have e : μ = ν := by simpa [Rel.ν, Rel.dom, wt_cons, sh, up, dn] using hs
    cases e
    exact RhoInversionKernel.kernel_invP₂ (sy := sy) (hc := hc) t ht ν i hh
  | invP₃ i μ n hn =>
    have e : μ = ν := by simpa [Rel.ν, Rel.dom, wt_cons, sh, up, dn] using hs
    cases e
    exact RhoInversionKernel.kernel_invP₃ (sy := sy) (hc := hc) t ν i n hn
  | invP₄ i μ n hn =>
    have e : μ = ν := by simpa [Rel.ν, Rel.dom, wt_cons, sh, up, dn] using hs
    cases e
    exact RhoInversionKernel.kernel_invP₄ (sy := sy) (hc := hc) t ν i n hn
  | invP₅ i μ m n hm hn =>
    have e : μ = ν := by simpa [Rel.ν, Rel.dom, wt_cons, sh, up, dn] using hs
    cases e
    exact RhoInversionKernel.kernel_invP₅ (sy := sy) (hc := hc) t ht ν i m n hm hn
  | invM₁ i μ hh =>
    have e : μ = ν := by simpa [Rel.ν, Rel.dom, wt_cons, sh, up, dn] using hs
    cases e
    exact RhoInversionKernel.kernel_invM₁ (sy := sy) (hc := hc) t ht ν i hh
  | invM₂ i μ hh =>
    have e : μ = ν := by simpa [Rel.ν, Rel.dom, wt_cons, sh, up, dn] using hs
    cases e
    exact RhoInversionKernel.kernel_invM₂ (sy := sy) (hc := hc) t ht ν i hh
  | invM₃ i μ n hn =>
    have e : μ = ν := by simpa [Rel.ν, Rel.dom, wt_cons, sh, up, dn] using hs
    cases e
    exact RhoInversionKernel.kernel_invM₃ (sy := sy) (hc := hc) t ν i n hn
  | invM₄ i μ n hn =>
    have e : μ = ν := by simpa [Rel.ν, Rel.dom, wt_cons, sh, up, dn] using hs
    cases e
    exact RhoInversionKernel.kernel_invM₄ (sy := sy) (hc := hc) t ν i n hn
  | invM₅ i μ m n hm hn =>
    have e : μ = ν := by simpa [Rel.ν, Rel.dom, wt_cons, sh, up, dn] using hs
    cases e
    exact RhoInversionKernel.kernel_invM₅ (sy := sy) (hc := hc) t ht ν i m n hm hn
  | dcupZero i μ n hn =>
    have e : μ = ν := by simpa [Rel.ν, Rel.dom, wt_cons, sh, up, dn] using hs
    cases e
    exact RhoInversionKernel.kernel_dcupZero (sy := sy) (hc := hc) t ν i n hn
  | dcapZero i μ n hn =>
    have e : μ = ν := by simpa [Rel.ν, Rel.dom, wt_cons, sh, up, dn] using hs
    cases e
    exact RhoInversionKernel.kernel_dcapZero (sy := sy) (hc := hc) t ν i n hn

  | _ => exact (hR trivial).elim

theorem rhoLin_relation (t : k) (ht : t ^ 2 = -1)
    (R : Rel D) (ν : X) (hs : wt D R.ν R.dom = ν) (hr : wt D R.ν R.cod = ν) :
    rhoLin (sy := sy) (hc := hc) t ν R.ν hs hr (relation D Sc R) = 0 := by
  by_cases hR : RhoUpwardKernel.IsUpward R
  · subst ν
    exact RhoUpwardKernel.rhoLin_upward t ht R hR hr
  · exact rhoLin_relation_other t ht R hR ν hs hr

theorem rhoLin_allRel (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    (R : (pres D Sc).AllRel) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (ha : R.dom = ob D μ s) (hb : R.cod = ob D μ r) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr (LinDiagram.cast R.rel ha hb) = 0 := by
  cases R with
  | user R =>
    change ob D R.ν R.dom = ob D μ s at ha
    change ob D R.ν R.cod = ob D μ r at hb
    have hμ : R.ν = μ := by
      simpa only [ob_endR] using congrArg Obj.endR ha
    subst μ
    have es := ob_injective ha
    have er := ob_injective hb
    subst s r
    simpa only [Presentation.AllRel.rel, LinDiagram.cast_rfl, pres] using
      rhoLin_relation t ht R ν hs hr
  | interchange x hx => exact rhoLin_interchange t ν μ x hx hs hr ha hb

theorem rhoLin_ideal (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    {f : LinDiagram k (ob D μ s) (ob D μ r)}
    (hf : f ∈ (pres D Sc).ideal (ob D μ s) (ob D μ r)) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr f = 0 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨R, u, v, hw, pre, post⟩ := hf
    exact rhoLin_idealGen t ν μ R (fun ν μ _ _ hs hr ha hb =>
      rhoLin_allRel t ht ν μ R hs hr ha hb) u v hw hs hr pre post
  | zero => exact map_zero _
  | add f g _ _ ih ih' => rw [map_add, ih, ih', add_zero]
  | smul c f _ ih => rw [map_smul, ih, smul_zero]

theorem rhoLin_homRel (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    {f g : LinDiagram k (ob D μ s) (ob D μ r)} (hfg : (pres D Sc).homRel f g) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr f = rhoLin t ν μ hs hr g := by
  have h := rhoLin_ideal (sy := sy) (hc := hc) t ht ν μ hs hr hfg
  rw [map_sub, sub_eq_zero] at h
  exact h

end OddMath.SKM.RhoEvaluator
