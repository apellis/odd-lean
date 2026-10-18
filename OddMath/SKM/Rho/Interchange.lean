import OddMath.SKM.Rho.Exchange
import StringDiagrams.InterchangeLayers

/-!
# Interchange for ρ

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

theorem rhoLin_interchange (t : k) (ν μ : X)
    (x : InterchangeData (sig D)) (hx : x.Valid) {s r : List (Letter I)}
    (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (ha : x.dom = ob D μ s) (hb : x.cod = ob D μ r) :
    rhoLin (sy := sy) (hc := hc) t ν μ hs hr
      (LinDiagram.cast (InterchangeData.rel k hx) ha hb) = 0 := by
  have hgh : psiLayers (Diagram.cast (InterchangeData.ghDiagram hx) ha hb) =
      [([], x.g.1, x.mid.map Col.l ++ x.h.1.dom),
        (x.g.1.cod ++ x.mid.map Col.l, x.h.1, [])] := by
    simp only [psiLayers, Diagram.layers_cast, InterchangeData.ghDiagram, Diagram.layers_mk,
      List.map_cons, List.map_nil, InterchangeData.gh₁, InterchangeData.gh₂,
      List.map_append, sig, wd_map_l]
  have hhg : psiLayers (Diagram.cast (InterchangeData.hgDiagram hx) ha hb) =
      [(x.g.1.dom ++ x.mid.map Col.l, x.h.1, []),
        ([], x.g.1, x.mid.map Col.l ++ x.h.1.cod)] := by
    simp only [psiLayers, Diagram.layers_cast, InterchangeData.hgDiagram, Diagram.layers_mk,
      List.map_cons, List.map_nil, InterchangeData.hg₁, InterchangeData.hg₂,
      List.map_append, sig, wd_map_l]
  have hC := psiLayers_chain (Diagram.cast (InterchangeData.ghDiagram hx) ha hb)
  rw [hgh] at hC
  have hsword : s = x.g.1.dom ++ x.mid.map Col.l ++ x.h.1.dom := by
    simpa only [List.nil_append, List.append_assoc] using hC.1
  have hrword : r = x.g.1.cod ++ x.mid.map Col.l ++ x.h.1.cod := by
    simpa only [List.append_nil] using hC.2.2.symm
  subst s r
  simp only [InterchangeData.rel, LinDiagram.cast_sub, LinDiagram.cast_smul,
    LinDiagram.cast_of, map_sub, map_smul]
  erw [rhoLin_single, rhoLin_single]
  simp only [one_smul, rhoDiagram, hgh, hhg]
  have he : (x.sign : k) = zsign k (x.g.1.parity D * x.h.1.parity D) :=
    interchange_sign x.g.1 x.h.1 x.h.2 x.g.2 x.mid x.start
  rw [rhoRaw_swap₀, he, sub_self]

end OddMath.SKM.RhoEvaluator
