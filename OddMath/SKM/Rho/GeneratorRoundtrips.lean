import OddMath.SKM.Rho.Inverse
import OddMath.SKM.Rho.EnvelopeEvaluations

/-!
# Generator Roundtrips for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
namespace OddMath.SKM.RhoGeneratorRoundtrips
open CategoryTheory StringDiagrams BicategoryStruct RhoWords RhoTwo RhoExtension RhoInverse
  QPiSupercategory Envelope
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}
local instance (a b : TwoSRev k (Uqπ D Sc sy hc)) : QPiSupercategory k (a ⟶ b) :=
  QPiTwoSupercategory.homQPiLeft a b

theorem sigma_hom {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) :
    QPiTwoEnvelope.toHom (QPiSupercategory.σ (R := k) f).hom =
      eqToHom (congrArg (pres D Sc).obj (Obj.nil_tensor f.obj.obj.start_eq)) := by
  change QPiTwoEnvelope.toHom
    (f ◁ (QPiTwoSupercategory.σ (R := k) b).hom ≫ (rightUnitor f).hom) = _
  change QEnvelope.toHom ((Envelope.toHom (Supercategory.twist k f.par
    (QPiTwoSupercategory.σ (R := k) b.unrev).hom)) ▷ f.obj ≫
    (leftUnitor f.obj).hom) = _
  erw [Supercategory.twist_of_mem f.par (QPiTwoSupercategory.σ_hom_mem (R := k) (B := Uqπ D Sc sy hc) b.unrev)]
  simp only [mul_zero, Supercategory.sign_zero, one_smul]
  change (𝟙 _ ▷ f.obj.obj) ≫ (leftUnitor f.obj.obj).hom = _
  erw [TwoSupercategory.id_whiskerRight (R := k), Category.id_comp]
  rfl

theorem sigmabar_hom {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) :
    QPiTwoEnvelope.toHom (QPiSupercategory.σbar (R := k) f).hom =
      eqToHom (congrArg (pres D Sc).obj (Obj.nil_tensor f.obj.obj.start_eq)) := by
  change QPiTwoEnvelope.toHom
    (f ◁ (QPiTwoSupercategory.σbar (R := k) b).hom ≫ (rightUnitor f).hom) = _
  change QEnvelope.toHom ((Envelope.toHom (Supercategory.twist k f.par
    (QPiTwoSupercategory.σbar (R := k) b.unrev).hom)) ▷ f.obj ≫
    (leftUnitor f.obj).hom) = _
  erw [Supercategory.twist_of_mem f.par (QPiTwoSupercategory.σbar_hom_mem (R := k) (B := Uqπ D Sc sy hc) b.unrev)]
  simp only [mul_zero, Supercategory.sign_zero, one_smul]
  change (𝟙 _ ▷ f.obj.obj) ≫ (leftUnitor f.obj.obj).hom = _
  erw [TwoSupercategory.id_whiskerRight (R := k), Category.id_comp]
  rfl

theorem qpow_obj {a b : TwoSRev k (Uqπ D Sc sy hc)} (m : ℤ) (f : a ⟶ b) :
    (qPow k m f).obj.obj.obj = f.obj.obj.obj := by
  rw [qPow_normal]

theorem sigmaPow_hom {a b : TwoSRev k (Uqπ D Sc sy hc)} (m : ℤ) (f : a ⟶ b) :
    QPiTwoEnvelope.toHom (σPow k m f).hom =
      eqToHom (congrArg (pres D Sc).obj (qpow_obj m f)) := by
  cases m with
  | ofNat n =>
    induction n with
    | zero => rfl
    | succ n ih =>
      change QPiTwoEnvelope.toHom (QPiSupercategory.σ (R := k) (qPowNat k n f)).hom ≫
        QPiTwoEnvelope.toHom (σPowNat k n f).hom = _
      rw [sigma_hom]
      erw [ih]
      exact eqToHom_trans
        (congrArg (pres D Sc).obj (Obj.nil_tensor (qPowNat k n f).obj.obj.start_eq))
        (congrArg (pres D Sc).obj (qpow_obj (Int.ofNat n) f))
  | negSucc n =>
    suffices h : ∀ n, QPiTwoEnvelope.toHom (σbarPowNat k n f).hom =
        eqToHom (congrArg (pres D Sc).obj (show (qinvPowNat k n f).obj.obj.obj = f.obj.obj.obj by rw [qinvPowNat_normal])) by
      exact h (n + 1)
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change QPiTwoEnvelope.toHom (QPiSupercategory.σbar (R := k) (qinvPowNat k n f)).hom ≫
        QPiTwoEnvelope.toHom (σbarPowNat k n f).hom = _
      rw [sigmabar_hom, ih]
      exact eqToHom_trans
        (congrArg (pres D Sc).obj (Obj.nil_tensor (qinvPowNat k n f).obj.obj.start_eq))
        (congrArg (pres D Sc).obj (show (qinvPowNat k n f).obj.obj.obj = f.obj.obj.obj by rw [qinvPowNat_normal]))

theorem sigmaPow_inv {a b : TwoSRev k (Uqπ D Sc sy hc)} (m : ℤ) (f : a ⟶ b) :
    QPiTwoEnvelope.toHom (σPow k m f).inv =
      eqToHom (congrArg (pres D Sc).obj (qpow_obj m f)).symm := by
  have h := congrArg (fun x => QPiTwoEnvelope.toHom x) (σPow k m f).hom_inv_id
  change QPiTwoEnvelope.toHom (σPow k m f).hom ≫ QPiTwoEnvelope.toHom (σPow k m f).inv = 𝟙 _ at h
  rw [sigmaPow_hom] at h
  apply (cancel_epi (eqToHom (congrArg (pres D Sc).obj (qpow_obj m f)))).mp
  rw [eqToHom_trans, eqToHom_refl]
  exact h

theorem envelope_zero_heq (t : k) (ht : t ^ 2 = -1)
    {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (hf : f.par = 0) (hg : g.par = 0) (x : f ⟶ g) :
    HEq ((rhoEnvelope t ht).map₂ x) (rhoMap₂ t ht f.obj.obj g.obj.obj (QPiTwoEnvelope.toHom x)) := by
  rcases f with ⟨p, f⟩
  rcases g with ⟨q, g⟩
  change p = 0 at hf
  change q = 0 at hg
  subst p q
  rw [rhoEnvelope_map₂]
  simp only [ζPow_zero, Iso.refl_hom, Iso.refl_inv, Category.comp_id]
  erw [Category.id_comp]
  change HEq (QPiTwoEnvelope.toHom (σPow k f.shift (rhoMap f.obj)).hom ≫
    QPiTwoEnvelope.toHom (rhoMap₂ t ht f.obj g.obj (QPiTwoEnvelope.toHom x)) ≫
    QPiTwoEnvelope.toHom (σPow k g.shift (rhoMap g.obj)).inv) _
  rw [sigmaPow_hom, sigmaPow_inv]
  exact (conj_eqToHom_iff_heq _ _
    (congrArg (pres D Sc).obj (qpow_obj f.shift (rhoMap f.obj)))
    (congrArg (pres D Sc).obj (qpow_obj g.shift (rhoMap g.obj)))).mp rfl

open RhoInversionKernel RhoEvaluator

private theorem rhoMap₂_heq (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} {f g f' g' : a ⟶ b}
    (ef : f = f') (eg : g = g') {x : f ⟶ g} {y : f' ⟶ g'} (h : HEq x y) :
    HEq (rhoMap₂ t ht f g x) (rhoMap₂ t ht f' g' y) := by
  subst f' g'
  cases h
  rfl

private theorem scalar_heq {a b a' b' : (pres D Sc).Presented}
    (ha : a = a') (hb : b = b') (c : k) {x : a ⟶ b} {y : a' ⟶ b'}
    (h : HEq x y) : HEq (c • x) (c • y) := by
  subst a' b'
  cases h
  rfl

theorem envelope_layers_heq (t : k) (ht : t ^ 2 = -1)
    (ν μ : X) {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (L : List (LayerData I)) (hL : SChain s L r) (c : k)
    {f g : (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩}
    (hf : f.par = 0) (hg : g.par = 0)
    (ef : f.obj.obj = psiWordAt ν μ s hs) (eg : g.obj.obj = psiWordAt ν μ r hr)
    (x : f ⟶ g) (hx : HEq x (c • cl D Sc μ s r L)) :
    HEq ((rhoEnvelope t ht).map₂ x)
      ((c * imageCoeff (D := D) t L) • cl D Sc ν (rhoWord s) (rhoWord r) (imageLayers L)) := by
  refine (envelope_zero_heq t ht hf hg x).trans ?_
  have H := rhoMap₂_heq t ht ef eg hx
  rw [rhoMap₂_wordAt, map_smul, cl_of hL] at H
  erw [rhoQuotient_diag, rhoDiagram_mkD] at H
  refine H.trans ?_
  have H' := scalar_heq
    (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ s hs))
    (congrArg (pres D Sc).obj (at_obj (sy := sy) (hc := hc) ν μ r hr)) c
    (raw_formula (sy := sy) (hc := hc) t ν μ L hs hr hL)
  exact H'.trans (heq_of_eq (smul_smul c _ _))

theorem image_word (t : k) (ht : t ^ 2 = -1) (ν μ : X)
    {s : List (Letter I)} (hs : wt D μ s = ν)
    (f : (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩)
    (ef : f.obj.obj = psiWordAt ν μ s hs) :
    ((rhoEnvelope t ht).map f).obj.obj = psiWordAt μ ν (rhoWord s) (hs ▸ rhoWord_wt μ s) := by
  apply Presentation.Bicat.Hom.ext
  rw [rhoEnvelope_map_word, ef]
  change ob D ν (rhoWord ((wd D μ s).map Col.l)) = _
  rw [wd_map_l]
  rfl

theorem twice_layers (t z : k) (ht : t ^ 2 = -1) (hz : z ^ 2 = -1)
    (ν μ : X) {s r : List (Letter I)} (hs : wt D μ s = ν) (hr : wt D μ r = ν)
    (L : List (LayerData I)) (hL : SChain s L r) (m n : ℤ) :
    HEq ((rhoEnvelope z hz).map₂ ((rhoEnvelope t ht).map₂
      (show (⟨0, ⟨m, psiWordAt (Sc := Sc) ν μ s hs⟩⟩ :
        (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩) ⟶
          ⟨0, ⟨n, psiWordAt ν μ r hr⟩⟩ from cl D Sc μ s r L)))
      ((imageCoeff (D := D) t L * imageCoeff (D := D) z (imageLayers L)) •
        cl D Sc μ s r (imageLayers (imageLayers L))) := by
  let f : (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩ := ⟨0, ⟨m, psiWordAt ν μ s hs⟩⟩
  let g : (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩ := ⟨0, ⟨n, psiWordAt ν μ r hr⟩⟩
  let x : f ⟶ g := cl D Sc μ s r L
  have H := envelope_layers_heq t ht ν μ hs hr L hL 1
    (f := f) (g := g) rfl rfl rfl rfl x (heq_of_eq (one_smul k _).symm)
  simp only [one_mul] at H
  have H' := envelope_layers_heq z hz μ ν (hs ▸ rhoWord_wt μ s) (hr ▸ rhoWord_wt μ r)
    (imageLayers L) (image_chain hL) (imageCoeff (D := D) t L)
    (f := (rhoEnvelope t ht).map f) (g := (rhoEnvelope t ht).map g)
    (rhoEnvelope_map_par t ht f) (rhoEnvelope_map_par t ht g)
    (image_word t ht ν μ hs f rfl) (image_word t ht ν μ hr g rfl)
    ((rhoEnvelope t ht).map₂ x) H
  erw [rhoWord_involutive, rhoWord_involutive] at H'
  exact H'

theorem image_single (g : Shape I) : imageLayers [([], g, [])] = RhoGenerators.layers g := by
  simp [imageLayers, rhoWord, flipW]

theorem coeff_single (t : k) (g : Shape I) : imageCoeff (D := D) t [([], g, [])] = RhoGenerators.coeff (D := D) t g := by
  exact mul_one _

theorem psiCoeff_neg_mul (t : k) (ht : t ^ 2 = -1) (p : ZMod 2) :
    psiCoeff (-t) p * psiCoeff t p = 1 := by
  fin_cases p
  · simp [psiCoeff]
  · change psiCoeff (-t) (1 : ZMod 2) * psiCoeff t (1 : ZMod 2) = 1
    simp only [psiCoeff, one_ne_zero, ↓reduceIte]
    rw [neg_mul, ← pow_two, ht, neg_neg]

theorem dot_roundtrip (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (h : wt D μ [up i] = ν) (m n : ℤ) :
    HEq ((rhoInverse t ht).map₂ ((rhoEnvelope t ht).map₂
      (show (⟨0, ⟨m, psiWordAt (Sc := Sc) ν μ [up i] h⟩⟩ :
        (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩) ⟶
          ⟨0, ⟨n, psiWordAt ν μ [up i] h⟩⟩ from cl D Sc μ [up i] [up i] (dotsL [] i [] 1))))
      (cl D Sc μ [up i] [up i] (dotsL [] i [] 1)) := by
  have H := twice_layers (Sc := Sc) (sy := sy) (hc := hc) t (-t) ht (by simpa only [neg_sq] using ht)
    ν μ h h [([], .dot i, [])] (show SChain [up i] [([], .dot i, [])] [up i] from ⟨rfl, rfl⟩) m n
  rw [image_single, coeff_single] at H
  change HEq _ ((psiCoeff t (D.parity i) * imageCoeff (D := D) (-t) (ddotL i)) •
    cl D Sc μ [up i] [up i] (imageLayers (ddotL i))) at H
  rw [RhoMates.ddot_coeff, RhoMates.reflected_ddot, mul_comm, psiCoeff_neg_mul t ht, one_smul] at H
  exact H

theorem crossing_roundtrip (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (hs : wt D μ [up i, up j] = ν) (hr : wt D μ [up j, up i] = ν) (m n : ℤ) :
    HEq ((rhoInverse t ht).map₂ ((rhoEnvelope t ht).map₂
      (show (⟨0, ⟨m, psiWordAt (Sc := Sc) ν μ [up i, up j] hs⟩⟩ :
        (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩) ⟶
          ⟨0, ⟨n, psiWordAt ν μ [up j, up i] hr⟩⟩ from cl D Sc μ [up i, up j] [up j, up i] (crossL [] i j []))))
      (cl D Sc μ [up i, up j] [up j, up i] (crossL [] i j [])) := by
  have H := twice_layers (Sc := Sc) (sy := sy) (hc := hc) t (-t) ht (by simpa only [neg_sq] using ht)
    ν μ hs hr [([], .cross i j, [])] (show SChain [up i, up j] [([], .cross i j, [])] [up j, up i] from ⟨rfl, rfl⟩) m n
  rw [image_single, coeff_single] at H
  change HEq _ ((psiCoeff t (D.parity i * D.parity j) * imageCoeff (D := D) (-t) (dcrossL j i)) •
    cl D Sc μ [up i, up j] [up j, up i] (imageLayers (dcrossL j i))) at H
  rw [RhoMates.dcross_coeff, RhoMates.reflected_dcross, mul_comm, psiCoeff_neg_mul t ht, one_smul] at H
  exact H

theorem cup_roundtrip (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (hs : wt D μ (Shape.cup i).dom = ν) (hr : wt D μ (Shape.cup i).cod = ν) (m n : ℤ) :
    HEq ((rhoInverse t ht).map₂ ((rhoEnvelope t ht).map₂
      (show (⟨0, ⟨m, psiWordAt (Sc := Sc) ν μ (Shape.cup i).dom hs⟩⟩ :
        (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩) ⟶
          ⟨0, ⟨n, psiWordAt ν μ (Shape.cup i).cod hr⟩⟩ from
            cl D Sc μ (Shape.cup i).dom (Shape.cup i).cod [([], .cup i, [])])))
      (cl D Sc μ (Shape.cup i).dom (Shape.cup i).cod [([], .cup i, [])]) := by
  have H := twice_layers (Sc := Sc) (sy := sy) (hc := hc) t (-t) ht (by simpa only [neg_sq] using ht)
    ν μ hs hr [([], .cup i, [])] (show SChain (Shape.cup i).dom [([], .cup i, [])] (Shape.cup i).cod from ⟨rfl, rfl⟩) m n
  rw [image_single, coeff_single] at H
  change HEq _ ((1 * imageCoeff (D := D) (-t) [([], .cup i, [])]) •
    cl D Sc μ (Shape.cup i).dom (Shape.cup i).cod (imageLayers [([], .cup i, [])])) at H
  rw [image_single, coeff_single] at H
  simp only [RhoGenerators.coeff, one_mul, one_smul] at H
  exact H

theorem cap_roundtrip (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I)
    (hs : wt D μ (Shape.cap i).dom = ν) (hr : wt D μ (Shape.cap i).cod = ν) (m n : ℤ) :
    HEq ((rhoInverse t ht).map₂ ((rhoEnvelope t ht).map₂
      (show (⟨0, ⟨m, psiWordAt (Sc := Sc) ν μ (Shape.cap i).dom hs⟩⟩ :
        (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩) ⟶
          ⟨0, ⟨n, psiWordAt ν μ (Shape.cap i).cod hr⟩⟩ from
            cl D Sc μ (Shape.cap i).dom (Shape.cap i).cod [([], .cap i, [])])))
      (cl D Sc μ (Shape.cap i).dom (Shape.cap i).cod [([], .cap i, [])]) := by
  have H := twice_layers (Sc := Sc) (sy := sy) (hc := hc) t (-t) ht (by simpa only [neg_sq] using ht)
    ν μ hs hr [([], .cap i, [])] (show SChain (Shape.cap i).dom [([], .cap i, [])] (Shape.cap i).cod from ⟨rfl, rfl⟩) m n
  rw [image_single, coeff_single] at H
  change HEq _ ((1 * imageCoeff (D := D) (-t) [([], .cap i, [])]) •
    cl D Sc μ (Shape.cap i).dom (Shape.cap i).cod (imageLayers [([], .cap i, [])])) at H
  rw [image_single, coeff_single] at H
  simp only [RhoGenerators.coeff, one_mul, one_smul] at H
  exact H

theorem lcross_roundtrip (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (hs : wt D μ (Shape.lcross i j).dom = ν) (hr : wt D μ (Shape.lcross i j).cod = ν) (m n : ℤ) :
    HEq ((rhoInverse t ht).map₂ ((rhoEnvelope t ht).map₂
      (show (⟨0, ⟨m, psiWordAt (Sc := Sc) ν μ (Shape.lcross i j).dom hs⟩⟩ :
        (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩) ⟶
          ⟨0, ⟨n, psiWordAt ν μ (Shape.lcross i j).cod hr⟩⟩ from
            cl D Sc μ (Shape.lcross i j).dom (Shape.lcross i j).cod [([], .lcross i j, [])])))
      (cl D Sc μ (Shape.lcross i j).dom (Shape.lcross i j).cod [([], .lcross i j, [])]) := by
  have H := twice_layers (Sc := Sc) (sy := sy) (hc := hc) t (-t) ht (by simpa only [neg_sq] using ht)
    ν μ hs hr [([], .lcross i j, [])] (show SChain (Shape.lcross i j).dom [([], .lcross i j, [])] (Shape.lcross i j).cod from ⟨rfl, rfl⟩) m n
  rw [image_single, coeff_single] at H
  change HEq _ ((psiCoeff (-t) (D.parity i * D.parity j) * imageCoeff (D := D) (-t) [([], .lcross j i, [])]) •
    cl D Sc μ (Shape.lcross i j).dom (Shape.lcross i j).cod (imageLayers [([], .lcross j i, [])])) at H
  rw [image_single, coeff_single] at H
  change HEq _ ((psiCoeff (-t) (D.parity i * D.parity j) * psiCoeff (-(-t)) (D.parity j * D.parity i)) •
    cl D Sc μ (Shape.lcross i j).dom (Shape.lcross i j).cod [([], .lcross i j, [])]) at H
  rw [neg_neg, mul_comm (D.parity j), psiCoeff_neg_mul t ht, one_smul] at H
  exact H

theorem dcup_roundtrip (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I) (d : ℕ)
    (hs : wt D μ (Shape.dcup i d).dom = ν) (hr : wt D μ (Shape.dcup i d).cod = ν) (m n : ℤ) :
    HEq ((rhoInverse t ht).map₂ ((rhoEnvelope t ht).map₂
      (show (⟨0, ⟨m, psiWordAt (Sc := Sc) ν μ (Shape.dcup i d).dom hs⟩⟩ :
        (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩) ⟶
          ⟨0, ⟨n, psiWordAt ν μ (Shape.dcup i d).cod hr⟩⟩ from
            cl D Sc μ (Shape.dcup i d).dom (Shape.dcup i d).cod [([], .dcup i d, [])])))
      (cl D Sc μ (Shape.dcup i d).dom (Shape.dcup i d).cod [([], .dcup i d, [])]) := by
  have H := twice_layers (Sc := Sc) (sy := sy) (hc := hc) t (-t) ht (by simpa only [neg_sq] using ht)
    ν μ hs hr [([], .dcup i d, [])] (show SChain (Shape.dcup i d).dom [([], .dcup i d, [])] (Shape.dcup i d).cod from ⟨rfl, rfl⟩) m n
  rw [image_single, coeff_single] at H
  change HEq _ ((RhoMixed.entryCoeff (-t) (D.parity i) d * imageCoeff (D := D) (-t) [([], .dcup i d, [])]) •
    cl D Sc μ (Shape.dcup i d).dom (Shape.dcup i d).cod (imageLayers [([], .dcup i d, [])])) at H
  rw [image_single, coeff_single] at H
  change HEq _ ((RhoMixed.entryCoeff (-t) (D.parity i) d * RhoMixed.entryCoeff (-(-t)) (D.parity i) d) •
    cl D Sc μ (Shape.dcup i d).dom (Shape.dcup i d).cod [([], .dcup i d, [])]) at H
  rw [neg_neg, mul_comm, RhoMixed.entryCoeff_inverse t ht, one_smul] at H
  exact H

theorem dcap_roundtrip (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i : I) (d : ℕ)
    (hs : wt D μ (Shape.dcap i d).dom = ν) (hr : wt D μ (Shape.dcap i d).cod = ν) (m n : ℤ) :
    HEq ((rhoInverse t ht).map₂ ((rhoEnvelope t ht).map₂
      (show (⟨0, ⟨m, psiWordAt (Sc := Sc) ν μ (Shape.dcap i d).dom hs⟩⟩ :
        (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩) ⟶
          ⟨0, ⟨n, psiWordAt ν μ (Shape.dcap i d).cod hr⟩⟩ from
            cl D Sc μ (Shape.dcap i d).dom (Shape.dcap i d).cod [([], .dcap i d, [])])))
      (cl D Sc μ (Shape.dcap i d).dom (Shape.dcap i d).cod [([], .dcap i d, [])]) := by
  have H := twice_layers (Sc := Sc) (sy := sy) (hc := hc) t (-t) ht (by simpa only [neg_sq] using ht)
    ν μ hs hr [([], .dcap i d, [])] (show SChain (Shape.dcap i d).dom [([], .dcap i d, [])] (Shape.dcap i d).cod from ⟨rfl, rfl⟩) m n
  rw [image_single, coeff_single] at H
  change HEq _ ((RhoMixed.entryCoeff (-t) (D.parity i) d * imageCoeff (D := D) (-t) [([], .dcap i d, [])]) •
    cl D Sc μ (Shape.dcap i d).dom (Shape.dcap i d).cod (imageLayers [([], .dcap i d, [])])) at H
  rw [image_single, coeff_single] at H
  change HEq _ ((RhoMixed.entryCoeff (-t) (D.parity i) d * RhoMixed.entryCoeff (-(-t)) (D.parity i) d) •
    cl D Sc μ (Shape.dcap i d).dom (Shape.dcap i d).cod [([], .dcap i d, [])]) at H
  rw [neg_neg, mul_comm, RhoMixed.entryCoeff_inverse t ht, one_smul] at H
  exact H

theorem shape_roundtrip (t : k) (ht : t ^ 2 = -1) (ν μ : X) (g : Shape I)
    (hs : wt D μ g.dom = ν) (hr : wt D μ g.cod = ν) (m n : ℤ) :
    HEq ((rhoInverse t ht).map₂ ((rhoEnvelope t ht).map₂
      (show (⟨0, ⟨m, psiWordAt (Sc := Sc) ν μ g.dom hs⟩⟩ :
        (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩) ⟶
          ⟨0, ⟨n, psiWordAt ν μ g.cod hr⟩⟩ from cl D Sc μ g.dom g.cod [([], g, [])])))
      (cl D Sc μ g.dom g.cod [([], g, [])]) := by
  cases g with
  | dot i => exact dot_roundtrip t ht ν μ i hs m n
  | cross i j => exact crossing_roundtrip t ht ν μ i j hs hr m n
  | cup i => exact cup_roundtrip t ht ν μ i hs hr m n
  | cap i => exact cap_roundtrip t ht ν μ i hs hr m n
  | lcross i j => exact lcross_roundtrip t ht ν μ i j hs hr m n
  | dcup i d => exact dcup_roundtrip t ht ν μ i d hs hr m n
  | dcap i d => exact dcap_roundtrip t ht ν μ i d hs hr m n

theorem shape_reverse_roundtrip (t : k) (ht : t ^ 2 = -1) (ν μ : X) (g : Shape I)
    (hs : wt D μ g.dom = ν) (hr : wt D μ g.cod = ν) (m n : ℤ) :
    HEq ((rhoEnvelope t ht).map₂ ((rhoInverse t ht).map₂
      (show (⟨0, ⟨m, psiWordAt (Sc := Sc) ν μ g.dom hs⟩⟩ :
        (⟨⟨⟨⟨μ⟩⟩⟩⟩ : TwoSRev k (Uqπ D Sc sy hc)) ⟶ ⟨⟨⟨⟨ν⟩⟩⟩⟩) ⟶
          ⟨0, ⟨n, psiWordAt ν μ g.cod hr⟩⟩ from cl D Sc μ g.dom g.cod [([], g, [])])))
      (cl D Sc μ g.dom g.cod [([], g, [])]) := by
  have H := shape_roundtrip (Sc := Sc) (sy := sy) (hc := hc) (-t)
    (by simpa only [neg_sq] using ht) ν μ g hs hr m n
  change HEq ((rhoEnvelope (-(-t)) _).map₂ ((rhoEnvelope (-t) _).map₂
    (show (⟨0, ⟨m, psiWordAt (Sc := Sc) ν μ g.dom hs⟩⟩ :
      (⟨⟨⟨ν⟩⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨⟨μ⟩⟩⟩) ⟶
        ⟨0, ⟨n, psiWordAt ν μ g.cod hr⟩⟩ from cl D Sc μ g.dom g.cod [([], g, [])]))) _ at H
  have e : rhoEnvelope (sy := sy) (hc := hc) (-(-t)) (by simpa only [neg_sq] using ht) = rhoEnvelope t ht := by
    congr 1
    exact neg_neg t
  rw [e] at H
  exact H

end OddMath.SKM.RhoGeneratorRoundtrips
