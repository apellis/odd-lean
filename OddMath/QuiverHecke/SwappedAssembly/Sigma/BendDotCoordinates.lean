import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirToProbeBend
import OddMath.QuiverHecke.SwappedAssembly.SlideSame
import OddMath.SKM.RouquierHomReservoirPowers

/-! # Dot coordinates in the prescribed mixed-bend charts

`SwappedHomInversion.md` §3 (3)–(6): the actual RP coefficient charts
carry the two raw dots to the pre/post Hom dots. The PR chart includes
the mixed interchange, so both of its dots retain the same Koszul sign.
These identities precede either lowering functor and output evaluation.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w

private theorem eqToIso_conj_of_heq {C : Type*} [Category C]
    {A B : C} (e : A = B) (f : End A) (g : End B) (h : HEq f g) :
    (eqToIso e).inv ≫ f ≫ (eqToIso e).hom = g := by
  subst e
  obtain rfl := eq_of_heq h
  simp only [eqToIso_refl, Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]

private theorem signed_chart_conjugation {C : Type*} [Category C] [Preadditive C]
    {A B E : C} (J : A ≅ B) (γ : A ≅ E) (x : End B) (y : End A)
    (q : ℤ) (hq : q * q = 1) (hslide : y ≫ J.hom = q • (J.hom ≫ x)) :
    (J.symm ≪≫ γ).inv ≫ x ≫ (J.symm ≪≫ γ).hom =
      q • (γ.inv ≫ y ≫ γ.hom) := by
  have hc : J.hom ≫ x ≫ J.inv = q • y := by
    have h := congrArg (· ≫ J.inv) hslide
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Preadditive.zsmul_comp] at h
    rw [h, smul_smul, hq, one_smul]
  calc
    _ = γ.inv ≫ (J.hom ≫ x ≫ J.inv) ≫ γ.hom := by
      simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Category.assoc]
    _ = _ := by rw [hc, Preadditive.zsmul_comp, Preadditive.comp_zsmul]

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

private theorem post_preDot_heq
    (T W : RouquierFamily (k := k) (B := B) D) (i : I) (β : I →₀ ℕ)
    {a b r r' s : X} (er : r = r') (hP : -b + D.α i = -a)
    (hR : r + D.α i = s) (hR' : r' + D.α i = s)
    (U : homWeightSector T.obj W.obj a r) (U' : homWeightSector T.obj W.obj a r')
    (hU : HEq U U') :
    HEq ((homContentPostE T.obj W i β b hR).map (homReservoirDot T W.obj i r hP U))
      ((homContentPostE T.obj W i β b hR').map (homReservoirDot T W.obj i r' hP U')) := by
  subst er
  obtain rfl := eq_of_heq hU
  rfl

private theorem postDot_pre_heq
    (T W : RouquierFamily (k := k) (B := B) D) (i : I) (β : I →₀ ℕ)
    {a b r r' s : X} (er : r = r') (hP : -b + D.α i = -a)
    (hR : r + D.α i = s) (hR' : r' + D.α i = s)
    (U : homWeightSector T.obj W.obj a r) (U' : homWeightSector T.obj W.obj a r')
    (hU : HEq U U') :
    HEq (homContentPostDot T.obj W i β b hR ((homContentPreE T W.obj i r hP).obj U))
      (homContentPostDot T.obj W i β b hR' ((homContentPreE T W.obj i r' hP).obj U')) := by
  subst er
  obtain rfl := eq_of_heq hU
  rfl

private theorem preDot_post_heq
    (T W : RouquierFamily (k := k) (B := B) D) (i : I)
    {β β' : I →₀ ℕ} {a a' b r s : X} (eβ : β = β') (ea : a = a')
    (hP : -b + D.α i = -a) (hP' : -b + D.α i = -a') (hR : r + D.α i = s)
    (U : homWeightSector T.obj W.obj a r) (U' : homWeightSector T.obj W.obj a' r)
    (hU : HEq U U') :
    HEq (homReservoirDot T W.obj i s hP ((homContentPostE T.obj W i β a hR).obj U))
      (homReservoirDot T W.obj i s hP' ((homContentPostE T.obj W i β' a' hR).obj U')) := by
  subst eβ ea
  obtain rfl := eq_of_heq hU
  rfl

private theorem pre_postDot_heq
    (T W : RouquierFamily (k := k) (B := B) D) (i : I)
    {β β' : I →₀ ℕ} {a a' b r s : X} (eβ : β = β') (ea : a = a')
    (hP : -b + D.α i = -a) (hP' : -b + D.α i = -a') (hR : r + D.α i = s)
    (U : homWeightSector T.obj W.obj a r) (U' : homWeightSector T.obj W.obj a' r)
    (hU : HEq U U') :
    HEq ((homContentPreE T W.obj i s hP).map (homContentPostDot T.obj W i β a hR U))
      ((homContentPreE T W.obj i s hP').map (homContentPostDot T.obj W i β' a' hR U')) := by
  subst eβ ea
  obtain rfl := eq_of_heq hU
  rfl

namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

/-- The XP-to-YR chart carries the inner RP dot to the postcomposition
of the raw probe dot, before the outer lowering functor. -/
theorem probeToReservoirCoefficientIso_preDot (i : I) (t : Sector I)
    (U : P.H (nextSector (true, i) true t)) :
    (P.probeToReservoirCoefficientIso i t U).inv ≫
      P.rpPreDot i (nextSector (false, i) false t) (by simp [StepValid, nextSector])
        ((congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)).symm ▸ U) ≫
      (P.probeToReservoirCoefficientIso i t U).hom =
    (homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)).map
      (homReservoirDot P.T P.W.obj i (P.muM t) (P.muP_preE i t) U) := by
  unfold probeToReservoirCoefficientIso
  apply eqToIso_conj_of_heq
  let tR := nextSector (true, i) false (nextSector (false, i) false t)
  let er := congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)
  have en : P.muM tR = P.muM t := congrArg P.muM (SPath.next_dnUp_false_false (i := i) t)
  have h := post_preDot_heq P.T P.W i t.1 en (P.muP_preE i t)
    (P.muM_postE i (by simp [StepValid, nextSector] :
      StepValid (true, i) false (nextSector (false, i) false t))) (P.muM_postF i t)
    (er.symm ▸ U : P.H (nextSector (true, i) true tR)) U (eqRec_heq _ _)
  simpa only [rpPreDot, homReservoirDot, step, tR, er, nextSector, muP] using h

/-- The outer RP dot becomes the literal content-shifted reservoir dot. -/
theorem probeToReservoirCoefficientIso_postDot (i : I) (t : Sector I)
    (U : P.H (nextSector (true, i) true t)) :
    (P.probeToReservoirCoefficientIso i t U).inv ≫
      P.rpPostDot i (nextSector (false, i) false t) (by simp [StepValid, nextSector])
        ((congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)).symm ▸ U) ≫
      (P.probeToReservoirCoefficientIso i t U).hom =
    homContentPostDot P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t)
      ((homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preE i t)).obj U) := by
  unfold probeToReservoirCoefficientIso
  apply eqToIso_conj_of_heq
  let tR := nextSector (true, i) false (nextSector (false, i) false t)
  let er := congrArg (nextSector (true, i) true) (SPath.next_dnUp_false_false (i := i) t)
  have en : P.muM tR = P.muM t := congrArg P.muM (SPath.next_dnUp_false_false (i := i) t)
  have h := postDot_pre_heq P.T P.W i t.1 en (P.muP_preE i t)
    (P.muM_postE i (by simp [StepValid, nextSector] :
      StepValid (true, i) false (nextSector (false, i) false t))) (P.muM_postF i t)
    (er.symm ▸ U : P.H (nextSector (true, i) true tR)) U (eqRec_heq _ _)
  simpa only [rpPostDot, step, tR, er, nextSector, muP] using h

private theorem reservoirToProbeCoefficientIso_preDot (i : I) (t : Sector I)
    (hb : StepValid (false, i) true t) (hv : StepValid (true, i) false t)
    (U : P.H (nextSector (true, i) false t)) :
    (P.reservoirToProbeCoefficientIso i t hb hv U).inv ≫
      P.prPreDot i i (nextSector (false, i) true t) hv
        ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ U) ≫
      (P.reservoirToProbeCoefficientIso i t hb hv U).hom =
    homReservoirDot P.T P.W.obj i (P.muM t) (P.muP_preF i hb)
      ((homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)).obj U) := by
  unfold reservoirToProbeCoefficientIso
  apply eqToIso_conj_of_heq
  let tP := nextSector (true, i) true (nextSector (false, i) true t)
  let er := congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)
  have ea : P.muP tP = P.muP t := congrArg P.muP (SPath.next_dnUp_true_true hb)
  have eβ : tP.1 = t.1 := congrArg Prod.fst (SPath.next_dnUp_true_true hb)
  have h := preDot_post_heq P.T P.W i eβ ea
    (P.muP_preE i (nextSector (false, i) true t)) (P.muP_preF i hb) (P.muM_postE i hv)
    (er.symm ▸ U : P.H (nextSector (true, i) false tP)) U (eqRec_heq _ _)
  simpa only [prPreDot, homReservoirDot, step, tP, er, nextSector, muM] using h

private theorem reservoirToProbeCoefficientIso_postDot (i : I) (t : Sector I)
    (hb : StepValid (false, i) true t) (hv : StepValid (true, i) false t)
    (U : P.H (nextSector (true, i) false t)) :
    (P.reservoirToProbeCoefficientIso i t hb hv U).inv ≫
      P.prPostDot i i (nextSector (false, i) true t) hv
        ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ U) ≫
      (P.reservoirToProbeCoefficientIso i t hb hv U).hom =
    (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).map
      (homContentPostDot P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv) U) := by
  unfold reservoirToProbeCoefficientIso
  apply eqToIso_conj_of_heq
  let tP := nextSector (true, i) true (nextSector (false, i) true t)
  let er := congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)
  have ea : P.muP tP = P.muP t := congrArg P.muP (SPath.next_dnUp_true_true hb)
  have eβ : tP.1 = t.1 := congrArg Prod.fst (SPath.next_dnUp_true_true hb)
  have h := pre_postDot_heq P.T P.W i eβ ea
    (P.muP_preE i (nextSector (false, i) true t)) (P.muP_preF i hb) (P.muM_postE i hv)
    (er.symm ▸ U : P.H (nextSector (true, i) false tP)) U (eqRec_heq _ _)
  simpa only [prPostDot, step, tP, er, nextSector, muM] using h

/-- The XR-to-YP RP chart retains the interchange sign on its probe dot. -/
theorem reservoirToProbeCoefficientChart_preDot (i : I) (t : Sector I)
    (hb : StepValid (false, i) true t) (hv : StepValid (true, i) false t)
    (U : P.H (nextSector (true, i) false t)) :
    (P.reservoirToProbeCoefficientChart i t hb hv U).inv ≫
      P.rpPreDot i (nextSector (false, i) true t) hv
        ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ U) ≫
      (P.reservoirToProbeCoefficientChart i t hb hv U).hom =
    koszulSign (D.parity i) (D.parity i) •
      homReservoirDot P.T P.W.obj i (P.muM t) (P.muP_preF i hb)
        ((homContentPostE P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv)).obj U) := by
  let U' := (congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ U
  let J := P.mixedJ i i (nextSector (false, i) true t) hv U'
  let γ := P.reservoirToProbeCoefficientIso i t hb hv U
  exact (signed_chart_conjugation J γ
    (P.rpPreDot i (nextSector (false, i) true t) hv U')
    (P.prPreDot i i (nextSector (false, i) true t) hv U')
    (koszulSign (D.parity i) (D.parity i)) (koszulSign_mul_self _ _)
    (P.prPreDot_comp_mixedJ i (nextSector (false, i) true t) hv U')).trans
      (congrArg (fun f => koszulSign (D.parity i) (D.parity i) • f)
        (P.reservoirToProbeCoefficientIso_preDot i t hb hv U))

/-- The same interchange sign occurs on the reservoir dot of the PR chart. -/
theorem reservoirToProbeCoefficientChart_postDot (i : I) (t : Sector I)
    (hb : StepValid (false, i) true t) (hv : StepValid (true, i) false t)
    (U : P.H (nextSector (true, i) false t)) :
    (P.reservoirToProbeCoefficientChart i t hb hv U).inv ≫
      P.rpPostDot i (nextSector (false, i) true t) hv
        ((congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ U) ≫
      (P.reservoirToProbeCoefficientChart i t hb hv U).hom =
    koszulSign (D.parity i) (D.parity i) •
      (homContentPreE P.T P.W.obj i (P.muM t) (P.muP_preF i hb)).map
        (homContentPostDot P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i hv) U) := by
  let U' := (congrArg (nextSector (true, i) false) (SPath.next_dnUp_true_true hb)).symm ▸ U
  let J := P.mixedJ i i (nextSector (false, i) true t) hv U'
  let γ := P.reservoirToProbeCoefficientIso i t hb hv U
  exact (signed_chart_conjugation J γ
    (P.rpPostDot i (nextSector (false, i) true t) hv U')
    (P.prPostDot i i (nextSector (false, i) true t) hv U')
    (koszulSign (D.parity i) (D.parity i)) (koszulSign_mul_self _ _)
    (P.prPostDot_comp_mixedJ i (nextSector (false, i) true t) hv U')).trans
      (congrArg (fun f => koszulSign (D.parity i) (D.parity i) • f)
        (P.reservoirToProbeCoefficientIso_postDot i t hb hv U))

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
