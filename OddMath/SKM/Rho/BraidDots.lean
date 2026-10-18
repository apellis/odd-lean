import OddMath.SKM.Rho.BraidScalars

/-!
# Braid Dots for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.SKM.RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

def reversedDots3 (i j : I) (s q r : ℕ) : List (LayerData I) :=
  (ddotsL i s).map (whL [] [dn j,dn i]) ++
    (ddotsL j q).map (whL [dn i] [dn i]) ++
    (ddotsL i r).map (whL [dn i,dn j] [])

theorem dots3_reverse (ν : X) (i j : I) (r q s : ℕ)
    (hij : (q : ZMod 2) * D.parity j = 0)
    (hrs : ((s : ZMod 2) * D.parity i) * ((r : ZMod 2) * D.parity i) = 0) :
    cl D Sc ν [dn i,dn j,dn i] [dn i,dn j,dn i] (reversedDots3 i j s q r) =
      cl D Sc ν [dn i,dn j,dn i] [dn i,dn j,dn i] (dots3 i j s q r) := by
  have A : SChain [dn i,dn j]
      ((ddotsL i s).map (whL [] [dn j]) ++ (ddotsL j q).map (whL [dn i] [])) [dn i,dn j] :=
    ((sChain_ddotsL i s).wh [] [dn j] rfl rfl).append
      ((sChain_ddotsL j q).wh [dn i] [] rfl rfl)
  have H := cl_interchange (D := D) (Sc := Sc) (μ := ν)
    (S := [dn i,dn j,dn i]) (T := [dn i,dn j,dn i]) [] [] A (sChain_ddotsL i r)
  simp only [List.map_append, List.map_map, Function.comp_def, whL_whL,
    List.nil_append, List.append_nil, parsum_append, parsum_map_whL,
    parsum_ddotsL, hij, add_zero, hrs, zsign_zero, one_smul] at H
  have B : SChain [dn j,dn i] ((ddotsL j q).map (whL [] [dn i])) [dn j,dn i] :=
    (sChain_ddotsL j q).wh [] [dn i] rfl rfl
  have H2 := cl_interchange (D := D) (Sc := Sc) (μ := ν)
    (S := [dn i,dn j,dn i]) (T := [dn i,dn j,dn i])
    ((ddotsL i r).map (whL [dn i,dn j] [])) [] (sChain_ddotsL i s) B
  simp only [List.map_map, Function.comp_def, whL_whL, List.append_nil,
    parsum_map_whL, parsum_ddotsL, hij, mul_zero, zsign_zero, one_smul] at H2
  simp only [List.cons_append, List.nil_append] at H
  simpa [reversedDots3, dots3, List.append_assoc] using
    H.trans (by simpa only [List.append_assoc] using H2)

end OddMath.SKM.RhoCoefficients
