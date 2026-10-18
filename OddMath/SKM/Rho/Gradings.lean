import OddMath.SKM.Rho.Linear

/-!
# Gradings for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoEvaluator
open CategoryTheory StringDiagrams Supercategory BicategoryStruct RhoWords
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

theorem shift_chain (μ : X) (L : List (LayerData I)) {s r : List (Letter I)}
    (hL : SChain s L r) : rhoShift sy μ s = rhoShift sy μ r := by
  induction L generalizing s with
  | nil => cases hL; rfl
  | cons x L ih =>
    obtain ⟨rfl, hL⟩ := hL
    calc
      rhoShift sy μ (x.1 ++ x.2.1.dom ++ x.2.2) =
          rhoShift sy μ (x.1 ++ x.2.1.cod ++ x.2.2) := by
        simp only [rhoShift_append, ← x.2.1.wt_dom_eq_wt_cod D,
          RhoGenerators.shift_dom_cod]
      _ = rhoShift sy μ r := ih hL

theorem rhoDiagram_parity (t : k) (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (d : ob D μ s ⟶ ob D μ r) :
    rhoDiagram (sy := sy) (hc := hc) t ν μ hs hr d ∈ parity (R := k) _ _
      (Diagram.degree (Presentation.parityDeg (sig D)) d) := by
  obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
  rw [rhoDiagram_mkD, degree_parity_mkD]
  exact rhoRaw_mem_parity t ν μ L hs hr hL

theorem rhoDiagram_degree (t : k) (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν) (d : ob D μ s ⟶ ob D μ r) :
    rhoDiagram (sy := sy) (hc := hc) t ν μ hs hr d ∈ GradedSupercategory.degree (R := k) _ _
      (Diagram.degree (gdeg D sy) d) := by
  obtain ⟨L, hL, rfl⟩ := diag_eq_mkD d
  rw [rhoDiagram_mkD, degree_gdeg_mkD]
  exact rhoRaw_mem_degree t ν μ L hs hr hL

theorem rhoLin_parity (t : k) (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    {f : LinDiagram k (ob D μ s) (ob D μ r)} {p : ZMod 2}
    (hf : f ∈ LinDiagram.homDeg k (Presentation.parityDeg (sig D)) _ _ p) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr f ∈ parity (R := k) _ _ p := by
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    rw [rhoLin_single, one_smul, ← hd]
    exact rhoDiagram_parity t ν μ hs hr d
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem rhoLin_degree (t : k) (ν μ : X) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    {f : LinDiagram k (ob D μ s) (ob D μ r)} {n : ℤ}
    (hf : f ∈ LinDiagram.homDeg k (gdeg D sy) _ _ n) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr f ∈ GradedSupercategory.degree (R := k) _ _ n := by
  rw [LinDiagram.homDeg, Finsupp.supported_eq_span_single] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨d, hd, rfl⟩ := hx
    rw [rhoLin_single, one_smul, ← hd]
    exact rhoDiagram_degree t ν μ hs hr d
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem rhoLin_cast (t : k) (ν μ : X) {s r s' r' : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (hs' : wt D μ s' = ν) (hr' : wt D μ r' = ν)
    (e : s = s') (f : r = r') (z : LinDiagram k (ob D μ s) (ob D μ r)) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs' hr'
      (LinDiagram.cast z (congrArg (ob D μ) e) (congrArg (ob D μ) f)) =
    eqToHom (at_congr ν μ hs' hs e.symm) ≫ rhoLin t ν μ hs hr z ≫
      eqToHom (at_congr ν μ hr hr' f) := by
  cases e; cases f
  simp [LinDiagram.cast]

theorem rhoLin_regions (t : k) {ν μ ν' μ' : X} (e : ν = ν') (f : μ = μ')
    {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (hs' : wt D μ' s = ν') (hr' : wt D μ' r = ν')
    (z : LinDiagram k (ob D μ s) (ob D μ r)) :
    HEq (rhoLin (sy := sy) (hc := hc) t ν' μ' hs' hr'
      (LinDiagram.cast z (congrArg (fun x => ob D x s) f) (congrArg (fun x => ob D x r) f)))
      (rhoLin (sy := sy) (hc := hc) t ν μ hs hr z) := by
  cases e; cases f
  simp [LinDiagram.cast]

end OddMath.SKM.RhoEvaluator
