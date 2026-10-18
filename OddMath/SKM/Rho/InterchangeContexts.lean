import OddMath.SKM.Rho.KernelContexts
import StringDiagrams.InterchangeLayers

/-!
# Interchange Contexts for ρ

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

theorem rhoLin_interchange_context (t : k) (ν μ : X)
    (x : InterchangeData (sig D)) (hx : x.Valid)
    (u : Obj (sig D)) (v : List (Col I X))
    (hw : x.dom.WhiskerOK u v) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (pre : LinDiagram k (ob D μ s) (x.dom.whisker u v))
    (post : LinDiagram k (x.cod.whisker u v) (ob D μ r)) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr
      (pre ≫ LinDiagram.whisker (InterchangeData.rel k hx) u v hw ≫ post) = 0 := by
  exact rhoLin_idealGen t ν μ (.interchange x hx)
    (fun ν μ _ _ hs hr ha hb => rhoLin_interchange t ν μ x hx hs hr ha hb)
    u v hw hs hr pre post

end OddMath.SKM.RhoEvaluator
