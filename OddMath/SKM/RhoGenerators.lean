/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.EnvelopeSRev
import OddMath.SKM.PsiCrossings
import OddMath.SKM.Cyclicity
import OddMath.SKM.ChevalleyGrading

/-!
# Upward generators of ρ in the shifted super-reverse

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 9.8, the upward-strand, dot and crossing assignments in its proof.
We use the super-reverse of Definition 9.5, not the super-opposite: vertical
composition is unchanged, while words reverse order and direction.

The 1-morphism assignments retain the displayed proposition's zero added parity
shift on F. The odd dot has coefficient +t. The definition `rhoCross` below records
only the printed −t odd–odd crossing assignment, for comparison; it is not the
crossing of the corrected functor. `RhoCoefficients.correctedCrossing` uses +t
instead. The printed assignment's dot-slide constraint is proved in
`Rho.PrintedSlideConstraint`, without asserting a nonzero identity witness.

The modules under `OddMath.SKM.Rho` construct the corrected graded functor and
its graded inverse, including both literal whole-functor identities in
`Rho.FunctorInverses`. See the Proposition 9.8 correction in `ERRATA.md`.
The calculations use a purely even commutative coefficient ring, not a field.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- The fixed weight assignment for Proposition 9.8. -/
def rhoObj (μ : X) : TwoSRev k (Uqπ D Sc sy hc) := ⟨⟨⟨⟨μ⟩⟩⟩⟩

/-- Sum of the printed integer shifts on an upward word, using each right region. -/
def rhoUpShift (sy : Symmetrizer D) (μ : X) : List I → ℤ
  | [] => 0
  | i :: w => -(sy.d i * (1 + D.h i (wt D μ (ups w)))) + rhoUpShift sy μ w

/-- Reversing the upward word and its directions returns to the initial weight. -/
theorem rho_wt_dns (μ : X) (w : List I) : wt D (wt D μ (ups w)) (dns w) = μ := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [ups_cons, dns_cons, wt_append]
    have h : wt D (wt D μ (up i :: ups w)) [dn i] = wt D μ (ups w) := by
      simp [wt, sh]
    rw [h, ih]

/-- The shifted image of an upward word with specified endpoint weights. -/
def rhoUpAt (ν μ : X) (w : List I) (h : wt D μ (ups w) = ν) :
    rhoObj (Sc := Sc) (sy := sy) (hc := hc) ν ⟶ rhoObj μ :=
  Envelope.mk 0 (QEnvelope.mk (rhoUpShift sy μ w)
    (psiWordAt μ ν (dns w) (h ▸ rho_wt_dns μ w)))

/-- The E-image has parity shift zero and the printed nonzero integer shift. -/
abbrev rhoE (μ : X) (i : I) :=
  rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up i]) μ [i] rfl

/-- The downward-strand assignment in the displayed statement of Proposition 9.8.
The parity shift is zero, exactly as printed; no cup/cap relation is asserted here. -/
def rhoF (μ : X) (i : I) :
    rhoObj (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [dn i]) ⟶ rhoObj μ :=
  Envelope.mk 0 (QEnvelope.mk (sy.d i * (D.h i μ - 1))
    (psiWordAt μ (wt D μ [dn i]) [up i] (by simp [wt, sh])))

/-- The printed F-image has no added parity shift. -/
@[simp] theorem rhoF_par (μ : X) (i : I) :
    (rhoF (Sc := Sc) (sy := sy) (hc := hc) μ i).par = 0 := rfl

/-- The integer shift of the printed F-image. -/
@[simp] theorem rhoF_shift (μ : X) (i : I) :
    (rhoF (Sc := Sc) (sy := sy) (hc := hc) μ i).obj.shift = sy.d i * (D.h i μ - 1) := rfl

@[simp] theorem rhoUpShift_single (μ : X) (i : I) :
    rhoUpShift sy μ [i] = -(sy.d i * (1 + D.h i μ)) := by
  simp [rhoUpShift, ups]

/-- The two-strand integer shift includes the Cartan cross term. -/
theorem rhoUpShift_pair (μ : X) (i j : I) :
    rhoUpShift sy μ [i, j] = -(sy.d i * (1 + D.h i μ)) -
      sy.d j * (1 + D.h j μ) + sy.d i * D.d i j := by
  simp [rhoUpShift, ups, wt, sh, Datum.d]
  ring

/-- Both boundaries of a crossing have the same integer shift. -/
theorem rhoUpShift_swap (μ : X) (i j : I) :
    rhoUpShift sy μ [i, j] = rhoUpShift sy μ [j, i] := by
  rw [rhoUpShift_pair, rhoUpShift_pair, sy.symm i j]
  ring

/-- The integer shifts add with the region change dictated by horizontal composition. -/
theorem rhoUpShift_append (μ : X) (a b : List I) :
    rhoUpShift sy μ (a ++ b) =
      rhoUpShift sy (wt D μ (ups b)) a + rhoUpShift sy μ b := by
  induction a with
  | nil => simp [rhoUpShift]
  | cons i a ih =>
    simp only [List.cons_append, rhoUpShift, ups_append, wt_append, ih]
    omega

/-- The composite of the two assigned strands is the reversed two-strand word.
This is an equality in the 1-morphism type of the super-reverse. -/
theorem rhoE_comp (μ : X) (i j : I) :
    (rhoE (Sc := Sc) (sy := sy) (hc := hc) (wt D μ [up j]) i) ≫ rhoE μ j =
      rhoUpAt (wt D μ (ups [i, j])) μ [i, j] rfl := by
  apply Envelope.ext
  · change (0 : ZMod 2) + 0 = 0
    rfl
  · apply QEnvelope.ext
    · change rhoUpShift sy μ [j] + rhoUpShift sy (wt D μ [up j]) [i] =
        rhoUpShift sy μ [i, j]
      simp [rhoUpShift, ups, add_comm]
    · apply Presentation.Bicat.Hom.ext
      change (ob D (wt D μ [up j]) [dn j]).tensor
        (ob D (wt D (wt D μ [up j]) [up i]) [dn i]) =
        ob D (wt D μ (ups [i, j])) [dn j, dn i]
      simp [ob, wd, wt, sh, StringDiagrams.Obj.tensor]

/-- The upward dot, with coefficient t exactly for an odd colour. -/
def rhoDot (t : k) (μ : X) (i : I) :
    rhoE (Sc := Sc) (sy := sy) (hc := hc) μ i ⟶ rhoE μ i :=
  psiCoeff t (D.parity i) •
    cl D Sc (wt D μ [up i]) [dn i] [dn i] (ddotL i)

private theorem wt_up_swap (μ : X) (i j : I) :
    wt D μ (ups [j, i]) = wt D μ (ups [i, j]) := by
  simp only [ups, List.map_cons, List.map_nil, wt_cons, wt_nil]
  exact add_left_comm _ _ _

/-- The printed crossing has coefficient −t exactly when both colours are odd.
This is retained for the printed slide constraint; the corrected functor uses
`RhoCoefficients.correctedCrossing`, with coefficient +t in the odd–odd case.
The underlying downward crossing reverses the order of the source colours. -/
def rhoCross (t : k) (ν μ : X) (i j : I) (h : wt D μ (ups [i, j]) = ν) :
    rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [i, j] h ⟶
      rhoUpAt ν μ [j, i] ((wt_up_swap μ i j).trans h) :=
  psiCoeff (-t) (D.parity i * D.parity j) •
    cl D Sc ν [dn j, dn i] [dn i, dn j] (dcrossL j i)

/-- The dot assignment preserves parity, including the target shifts. -/
theorem rhoDot_mem_parity (t : k) (μ : X) (i : I) :
    rhoDot (Sc := Sc) (sy := sy) (hc := hc) t μ i ∈
      parity (R := k) _ _ (D.parity i) := by
  change psiCoeff t (D.parity i) • cl D Sc _ _ _ _ ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (D.parity i + (0 + 0))
  apply Submodule.smul_mem
  unfold cl
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_parity_mkD]
    simp [ddotL, mateL, dotsL, whL, Shape.parity]
  · exact Submodule.zero_mem _

/-- The dot assignment has integer degree 2dᵢ. -/
theorem rhoDot_mem_degree (t : k) (μ : X) (i : I) :
    rhoDot (Sc := Sc) (sy := sy) (hc := hc) t μ i ∈
      GradedSupercategory.degree (R := k) _ _ (2 * sy.d i) := by
  change psiCoeff t (D.parity i) • cl D Sc _ _ _ _ ∈
    (pres D Sc).homDeg (gdeg D sy) _ _ (2 * sy.d i + (_ - _))
  simp only [sub_self, add_zero]
  apply Submodule.smul_mem
  have h := cl_mem_gdeg (Sc := Sc) sy (wt D μ [up i]) [dn i] [dn i] (ddotL i)
  have hd : gsum D sy (wt D μ [up i]) (ddotL i) = 2 * sy.d i := by
    simp [gsum, ddotL, mateL, dotsL, whL, gdeg, Datum.d_self]
    ring
  rw [hd] at h
  exact h

/-- The crossing preserves parity. -/
theorem rhoCross_mem_parity (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i, j]) = ν) :
    rhoCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ∈
      parity (R := k) _ _ (D.parity i * D.parity j) := by
  change psiCoeff (-t) (D.parity i * D.parity j) • cl D Sc _ _ _ _ ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (_ + (0 + 0))
  apply Submodule.smul_mem
  unfold cl
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_parity_mkD]
    simpa only [parsum, add_zero, mul_comm] using parsum_dcrossL (D := D) j i
  · exact Submodule.zero_mem _

/-- The crossing has the source degree dᵢdᵢⱼ, after including both Q-shifts. -/
theorem rhoCross_mem_degree (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i, j]) = ν) :
    rhoCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ∈
      GradedSupercategory.degree (R := k) _ _ (sy.d i * D.d i j) := by
  change psiCoeff (-t) (D.parity i * D.parity j) • cl D Sc _ _ _ _ ∈
    (pres D Sc).homDeg (gdeg D sy) _ _
      (sy.d i * D.d i j + (rhoUpShift sy μ [i, j] - rhoUpShift sy μ [j, i]))
  rw [rhoUpShift_swap μ i j, sub_self, add_zero]
  apply Submodule.smul_mem
  have hg := cl_mem_gdeg (Sc := Sc) sy ν [dn j, dn i] [dn i, dn j] (dcrossL j i)
  have hd : gsum D sy ν (dcrossL j i) = sy.d i * D.d i j := by
    simp [gsum, dcrossL, sigmaL, whL, gdeg, Datum.d_self]
    ring
  rw [hd] at hg
  exact hg

/-- Equal-colour quadratic relation (1.7) in the shifted super-reverse. -/
theorem rhoCross_sq (t : k) (ν μ : X) (i : I)
    (h : wt D μ (ups [i, i]) = ν) :
    rhoCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i i h ≫
      rhoCross t ν μ i i h = 0 := by
  change (psiCoeff (-t) (D.parity i * D.parity i) • cl D Sc ν _ _ _) ≫
    (psiCoeff (-t) (D.parity i * D.parity i) • cl D Sc ν _ _ _) = 0
  rw [Linear.smul_comp, Linear.comp_smul, cl_comp (sChain_dcrossL i i) (sChain_dcrossL i i),
    lemma32_eq Sc, smul_zero, smul_zero]

private theorem rhoCoeff_sq (t : k) (ht : t ^ 2 = -1) (p : ZMod 2) :
    psiCoeff (-t) p * psiCoeff (-t) p = zsign k p := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [psiCoeff, zsign, ← pow_two, ht]

/-- The crossing coefficients supply the sign in the downward quadratic relation (3.7). -/
theorem rhoCross_comp (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i, j]) = ν) :
    rhoCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫
      rhoCross t ν μ j i ((wt_up_swap μ i j).trans h) =
    (show rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [i, j] h ⟶
      rhoUpAt ν μ [i, j] h from
      zsign k (D.parity i * D.parity j) •
        cl D Sc ν [dn j, dn i] [dn j, dn i] (dcrossL j i ++ dcrossL i j)) := by
  change (psiCoeff (-t) (D.parity i * D.parity j) • cl D Sc ν _ _ _) ≫
    (psiCoeff (-t) (D.parity j * D.parity i) • cl D Sc ν _ _ _) = _
  rw [Linear.smul_comp, Linear.comp_smul, smul_smul,
    mul_comm (D.parity j) (D.parity i), rhoCoeff_sq t ht,
    cl_comp (sChain_dcrossL j i) (sChain_dcrossL i j)]

/-- Disconnected-colour quadratic relation (1.7) in the shifted super-reverse. -/
theorem rhoCross_quadZero (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i, j]) = ν) (hij : i ≠ j) (hd : D.d i j = 0) :
    rhoCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫
      rhoCross t ν μ j i ((wt_up_swap μ i j).trans h) = (Sc.t i j : k) • 𝟙 _ := by
  rw [rhoCross_comp t ht]
  change zsign k (D.parity i * D.parity j) • cl D Sc ν _ _ _ =
    (Sc.t i j : k) • 𝟙 ((pres D Sc).obj (ob D ν [dn j, dn i]))
  rw [mul_comm (D.parity i) (D.parity j),
    lemma32_zero Sc j i ν hij.symm ((D.d_eq_zero_iff i j).mp hd),
    ← Sc.t_symm_of_d_eq_zero i j hd, cl_nil]

/-- Image of the dot on the source's left strand: it lies on the right after reversal. -/
def rhoDotLeft (t : k) (ν μ : X) (i j : I) (h : wt D μ (ups [i, j]) = ν) :
    rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [i, j] h ⟶ rhoUpAt ν μ [i, j] h :=
  psiCoeff t (D.parity i) •
    cl D Sc ν [dn j, dn i] [dn j, dn i] ((ddotL i).map (whL [dn j] []))

/-- Image of the dot on the source's right strand: it lies on the left after reversal. -/
def rhoDotRight (t : k) (ν μ : X) (i j : I) (h : wt D μ (ups [i, j]) = ν) :
    rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [i, j] h ⟶ rhoUpAt ν μ [i, j] h :=
  psiCoeff t (D.parity j) •
    cl D Sc ν [dn j, dn i] [dn j, dn i] ((ddotL j).map (whL [] [dn i]))

private theorem downDotLeft_chain (i j : I) :
    SChain [dn i, dn j] ((ddotL i).map (whL [] [dn j])) [dn i, dn j] :=
  (sChain_ddotL i).wh [] [dn j] rfl rfl

private theorem downDotRight_chain (i j : I) :
    SChain [dn i, dn j] ((ddotL j).map (whL [dn i] [])) [dn i, dn j] :=
  (sChain_ddotL j).wh [dn i] [] rfl rfl

/-- First distinct-colour dot-slide relation (1.8), from the downward relation (3.6). -/
theorem rho_slideL (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i, j]) = ν) (hij : i ≠ j) :
    rhoDotLeft (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫ rhoCross t ν μ i j h =
      zsign k (D.parity i * D.parity j) •
        (rhoCross t ν μ i j h ≫ rhoDotRight t ν μ j i ((wt_up_swap μ i j).trans h)) := by
  change (psiCoeff t (D.parity i) • cl D Sc ν _ _ _) ≫
    (psiCoeff (-t) (D.parity i * D.parity j) • cl D Sc ν _ _ _) =
    zsign k (D.parity i * D.parity j) •
      ((psiCoeff (-t) (D.parity i * D.parity j) • cl D Sc ν _ _ _) ≫
        (psiCoeff t (D.parity i) • cl D Sc ν _ _ _))
  simp only [Linear.smul_comp, Linear.comp_smul]
  rw [smul_comm (zsign k _) (psiCoeff t _),
    smul_comm (zsign k _) (psiCoeff (-t) _)]
  conv_lhs => rw [smul_comm]
  apply congrArg (psiCoeff t _ • ·)
  apply congrArg (psiCoeff (-t) _ • ·)
  rw [cl_comp (D := D) (Sc := Sc) (μ := ν) (downDotRight_chain j i) (sChain_dcrossL j i),
    cl_comp (D := D) (Sc := Sc) (μ := ν) (sChain_dcrossL j i) (downDotLeft_chain i j)]
  have H := lemma31_eq6_ne Sc i j ν hij 1
  simp only [ddotsL_one, Nat.cast_one, mul_one] at H
  have H' := congrArg (zsign k (D.parity i * D.parity j) • ·) H
  simpa only [smul_smul, zsign_mul_self, one_smul] using H'

/-- Second distinct-colour dot-slide relation (1.8), from the downward relation (3.5). -/
theorem rho_slideR (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i, j]) = ν) (hij : i ≠ j) :
    rhoCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h ≫
      rhoDotLeft t ν μ j i ((wt_up_swap μ i j).trans h) =
      zsign k (D.parity i * D.parity j) •
        (rhoDotRight t ν μ i j h ≫ rhoCross t ν μ i j h) := by
  change (psiCoeff (-t) (D.parity i * D.parity j) • cl D Sc ν _ _ _) ≫
    (psiCoeff t (D.parity j) • cl D Sc ν _ _ _) =
    zsign k (D.parity i * D.parity j) •
      ((psiCoeff t (D.parity j) • cl D Sc ν _ _ _) ≫
        (psiCoeff (-t) (D.parity i * D.parity j) • cl D Sc ν _ _ _))
  simp only [Linear.smul_comp, Linear.comp_smul]
  rw [smul_comm (zsign k _) (psiCoeff (-t) _),
    smul_comm (zsign k _) (psiCoeff t _)]
  conv_lhs => rw [smul_comm]
  apply congrArg (psiCoeff (-t) _ • ·)
  apply congrArg (psiCoeff t _ • ·)
  rw [cl_comp (D := D) (Sc := Sc) (μ := ν) (sChain_dcrossL j i) (downDotRight_chain i j),
    cl_comp (D := D) (Sc := Sc) (μ := ν) (downDotLeft_chain j i) (sChain_dcrossL j i)]
  have H := lemma31_eq5_ne Sc i j ν hij 1
  simp only [ddotsL_one, Nat.cast_one, mul_one] at H
  have H' := congrArg (zsign k (D.parity i * D.parity j) • ·) H
  simpa only [smul_smul, zsign_mul_self, one_smul] using H'

end OddMath.SKM
