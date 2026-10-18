import OddMath.SKM.Rho.Coefficients
import OddMath.SKM.Rho.Parity

/-!
# Mixed for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoMixed
open CategoryTheory StringDiagrams Supercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

def mixedLayers (i j : I) : List (LayerData I) :=
  [([up i, dn j], Shape.cup i, [])] ++
    (dcrossL j i).map (whL [up i] [up i]) ++
    [([], Shape.cap i, [dn j, up i])]

theorem mixed_chain (i j : I) :
    SChain [up i, dn j] (mixedLayers i j) [dn j, up i] := by
  refine SChain.append (t' := [up i, dn i, dn j, up i])
    (SChain.append (t' := [up i, dn j, dn i, up i]) ?_ ?_) ?_
  · exact ⟨rfl, rfl⟩
  · simpa using (sChain_dcrossL j i).whisk [up i] [up i]
  · exact ⟨rfl, rfl⟩

theorem mixed_layers_eq (ν : X) (i j : I) :
    cl D Sc ν [up i, dn j] [dn j, up i] (mixedLayers i j) =
      cl D Sc ν [up i, dn j] [dn j, up i] (sigmaL j i) := by
  let A := [([up i, dn j], Shape.cup i, [])] ++
    (sigmaL j i).map (whL [] [dn i, up i]) ++ [([dn j], Shape.cap i, [up i])]
  let B := sigmaL j i ++
    [([dn j, up i], Shape.cup i, []), ([dn j], Shape.cap i, [up i])]
  have h1 : cl D Sc ν [up i, dn j] [dn j, up i] (mixedLayers i j) =
      cl D Sc ν [up i, dn j] [dn j, up i] A := by
    apply cl_step (Sc := Sc) ν
      [([up i, dn j], Shape.cup i, [])] [] [] [up i]
      (eq_2_5_b Sc i j (wt D ν [up i])).symm
      (show SChain [up i, dn j] [([up i, dn j], Shape.cup i, [])]
        ([] ++ [up i, dn j, dn i] ++ [up i]) from ⟨rfl, rfl⟩)
      (show SChain ([] ++ [dn j] ++ [up i]) [] [dn j, up i] from rfl)
    · simp [mixedLayers, List.map_append, whL]
    · simp [A, List.map_append, whL]
  have h2 := cl_interchange (D := D) (Sc := Sc) (μ := ν)
    (S := [up i, dn j]) (T := [dn j, up i]) []
    [([dn j], Shape.cap i, [up i])] (s := [up i, dn j]) (s' := [dn j, up i])
    (t := []) (t' := [dn i, up i]) (A := sigmaL j i) (B := [([], Shape.cup i, [])])
    (sChain_sigmaL j i) (show SChain [] [([], Shape.cup i, [])] [dn i, up i] from ⟨rfl,rfl⟩)
  simp only [parsum_cons, parsum_nil, Shape.parity, add_zero, mul_zero,
    zsign_zero, one_smul, List.nil_append] at h2
  have h3 : cl D Sc ν [up i, dn j] [dn j, up i] B =
      cl D Sc ν [up i, dn j] [dn j, up i] (sigmaL j i) := by
    apply cl_step (Sc := Sc) ν (sigmaL j i) [] [dn j] []
      (cl_zigE Sc i (wt D ν [])) (sChain_sigmaL j i)
      (show SChain ([dn j] ++ [up i] ++ []) [] [dn j, up i] from rfl)
    · simp [B, whL]
    · simp
  simp only [List.map_cons, List.map_nil, whL, List.nil_append,
    List.append_nil, List.cons_append, List.append_assoc] at h2
  exact h1.trans (h2.symm.trans h3)

def EF (μ : X) (i j : I) :=
  rhoE (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [dn i]) j ≫ rhoF μ i

def FE (μ : X) (i j : I) :=
  rhoF (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up j]) i ≫ rhoE μ j

def mixedShift (μ : X) (i j : I) : ℤ :=
  sy.d i * (D.h i μ - 1) - sy.d j * (1 + D.h j μ) - sy.d j * D.d j i

theorem EF_par (μ : X) (i j : I) :
    (EF (Sc := Sc) (sy := sy) (hc := hc) μ i j).par = 0 := rfl

theorem FE_par (μ : X) (i j : I) :
    (FE (Sc := Sc) (sy := sy) (hc := hc) μ i j).par = 0 := rfl

theorem EF_shift (μ : X) (i j : I) :
    (EF (Sc := Sc) (sy := sy) (hc := hc) μ i j).obj.shift = mixedShift (sy := sy) μ i j := by
  change sy.d i * (D.h i μ - 1) + rhoUpShift sy (wt D μ [dn i]) [j] = _
  simp [rhoUpShift_single, mixedShift, wt, sh, Datum.h, Datum.d]
  ring

theorem FE_shift (μ : X) (i j : I) :
    (FE (Sc := Sc) (sy := sy) (hc := hc) μ i j).obj.shift = mixedShift (sy := sy) μ i j := by
  change rhoUpShift sy μ [j] + sy.d i * (D.h i (wt D μ [up j]) - 1) = _
  rw [rhoUpShift_single, h_wt_upj]
  unfold mixedShift
  have h := sy.symm i j
  nlinarith

theorem EF_word (μ : X) (i j : I) :
    (EF (Sc := Sc) (sy := sy) (hc := hc) μ i j).obj.obj.obj =
      ob D (wt D μ [up j, dn i]) [up i, dn j] := by
  change (ob D (wt D μ [dn i]) [up i]).tensor
    (ob D (wt D (wt D μ [dn i]) [up j]) [dn j]) = _
  simp [ob, wd, wt, sh, StringDiagrams.Obj.tensor, add_comm, add_left_comm, add_assoc]

theorem FE_word (μ : X) (i j : I) :
    (FE (Sc := Sc) (sy := sy) (hc := hc) μ i j).obj.obj.obj =
      ob D (wt D μ [up j, dn i]) [dn j, up i] := by
  change (ob D (wt D μ [up j]) [dn j]).tensor
    (ob D (wt D (wt D μ [up j]) [dn i]) [up i]) = _
  simp [ob, wd, wt, sh, StringDiagrams.Obj.tensor, add_comm, add_left_comm, add_assoc]

def mixed (t : k) (ν : X) (i j : I) :=
  psiCoeff t (D.parity i * D.parity j) •
    cl D Sc ν [up i, dn j] [dn j, up i] (mixedLayers i j)

theorem mixed_eq (t : k) (ν : X) (i j : I) :
    mixed (Sc := Sc) t ν i j = psiCoeff t (D.parity i * D.parity j) •
      cl D Sc ν [up i, dn j] [dn j, up i] (sigmaL j i) := by
  rw [mixed, mixed_layers_eq]

theorem coeff_inverse (t : k) (ht : t ^ 2 = -1) (p : ZMod 2) :
    psiCoeff t p * psiCoeff (-t) p = 1 := by
  rcases parity_eq_zero_or_one p with h | h
  · simp [psiCoeff, h]
  · simp only [psiCoeff, h, one_ne_zero, ↓reduceIte]
    rw [mul_neg, ← pow_two, ht, neg_neg]

def mixedInverse (t : k) (ν : X) (i j : I) :=
  psiCoeff (-t) (D.parity i * D.parity j) •
    cl D Sc ν [dn j, up i] [up i, dn j] (lcrossL j i)

theorem mixed_invNe₁ (t : k) (ht : t ^ 2 = -1) (ν : X) (i j : I) (hij : i ≠ j) :
    mixed (Sc := Sc) t ν i j ≫ mixedInverse t ν i j = 𝟙 _ := by
  rw [mixed_eq, mixedInverse, Linear.smul_comp, Linear.comp_smul, smul_smul,
    coeff_inverse t ht, one_smul, cl_comp (sChain_sigmaL j i) (sChain_lcrossL j i),
    cl_invNe₁ Sc j i ν hij.symm, cl_nil]

theorem mixed_invNe₂ (t : k) (ht : t ^ 2 = -1) (ν : X) (i j : I) (hij : i ≠ j) :
    mixedInverse (Sc := Sc) t ν i j ≫ mixed t ν i j = 𝟙 _ := by
  rw [mixed_eq, mixedInverse, Linear.smul_comp, Linear.comp_smul, smul_smul,
    mul_comm (psiCoeff (-t) _), coeff_inverse t ht, one_smul,
    cl_comp (sChain_lcrossL j i) (sChain_sigmaL j i), cl_invNe₂ Sc j i ν hij.symm, cl_nil]

end OddMath.SKM.RhoMixed
