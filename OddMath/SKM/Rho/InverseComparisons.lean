import OddMath.SKM.Rho.Inverse

/-!
# Inverse Comparisons for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/

noncomputable section
namespace OddMath.SKM.RhoInverse
open CategoryTheory StringDiagrams BicategoryStruct RhoWords RhoTwo RhoExtension
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}

variable (t : k) (ht : t ^ 2 = -1)

theorem rhoForwardInverse_mapId (a : Uqπ D Sc sy hc) :
    ((rhoEnvelope t ht).comp (rhoInverse t ht)).mapId a =
      eqToIso (rhoInverse_rho_map t ht (𝟙 a)).symm := by
  apply Iso.ext
  simp only [TwoSuperfunctor.comp_mapId, Iso.trans_hom, TwoSuperfunctor.map₂Iso_hom]
  rw [rhoInverse_mapId, rhoEnvelope_mapId, rhoEnvelope_mapId]
  change 𝟙 _ ≫ (rhoInverse t ht).map₂ (𝟙 _) = _
  rw [TwoSuperfunctor.map₂_id, Category.id_comp]
  rfl

theorem rhoInverseForward_mapId (a : TwoSRev k (Uqπ D Sc sy hc)) :
    ((rhoInverse t ht).comp (rhoEnvelope t ht)).mapId a =
      eqToIso (rho_rhoInverse_map t ht (𝟙 a)).symm := by
  apply Iso.ext
  simp only [TwoSuperfunctor.comp_mapId, Iso.trans_hom, TwoSuperfunctor.map₂Iso_hom]
  rw [rhoInverse_mapId, rhoEnvelope_mapId, rhoEnvelope_mapId]
  change 𝟙 _ ≫ (rhoEnvelope t ht).map₂ (𝟙 _) = _
  rw [TwoSuperfunctor.map₂_id, Category.id_comp]
  rfl
open QPiSupercategory Envelope Supercategory
local instance (a b : TwoSRev k (Uqπ D Sc sy hc)) : QPiSupercategory k (a ⟶ b) :=
  QPiTwoSupercategory.homQPiLeft a b

private theorem sigma_hom {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) :
    QPiTwoEnvelope.toHom (QPiSupercategory.σ (R := k) f).hom =
      eqToHom (congrArg (pres D Sc).obj (Obj.nil_tensor f.obj.obj.start_eq)) := by
  change QEnvelope.toHom (Envelope.toHom (twist k f.par
    (QPiTwoSupercategory.σ (R := k) b.unrev).hom) ▷ f.obj ≫ (leftUnitor f.obj).hom) = _
  rw [twist_of_mem _ (QPiTwoSupercategory.σ_hom_mem b.unrev), mul_zero, sign_zero, one_smul]
  change (𝟙 _ ▷ f.obj.obj) ≫ (leftUnitor f.obj.obj).hom = _
  rw [TwoSupercategory.id_whiskerRight (R := k), Category.id_comp]
  rfl

private theorem sigmabar_hom {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) :
    QPiTwoEnvelope.toHom (QPiSupercategory.σbar (R := k) f).hom =
      eqToHom (congrArg (pres D Sc).obj (Obj.nil_tensor f.obj.obj.start_eq)) := by
  change QEnvelope.toHom (Envelope.toHom (twist k f.par
    (QPiTwoSupercategory.σ (R := k) b.unrev).hom) ▷ f.obj ≫ (leftUnitor f.obj).hom) = _
  rw [twist_of_mem _ (QPiTwoSupercategory.σ_hom_mem b.unrev), mul_zero, sign_zero, one_smul]
  change (𝟙 _ ▷ f.obj.obj) ≫ (leftUnitor f.obj.obj).hom = _
  rw [TwoSupercategory.id_whiskerRight (R := k), Category.id_comp]
  rfl

private theorem source_eq {a b : UGr D Sc sy hc} {f g : a ⟶ b} (e : f = g) :
    eqToHom e = eqToHom (congrArg (fun z : a ⟶ b => (pres D Sc).obj z.obj) e) := by
  cases e
  rfl

private theorem sigma_bicat {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) :
    QPiTwoEnvelope.toHom (QPiSupercategory.σ (R := k) f).hom =
      eqToHom (source_left f.obj.obj) :=
  (sigma_hom f).trans (source_eq (source_left f.obj.obj)).symm

private theorem sigmabar_bicat {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) :
    QPiTwoEnvelope.toHom (QPiSupercategory.σbar (R := k) f).hom =
      eqToHom (source_left f.obj.obj) :=
  (sigmabar_hom f).trans (source_eq (source_left f.obj.obj)).symm

theorem rhoQPow_word {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (m : ℤ) :
    (qPow k m f).obj.obj = f.obj.obj := by
  rw [qPow_normal]

theorem rhoSigmaPow_hom {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (m : ℤ) :
    QPiTwoEnvelope.toHom (σPow k m f).hom = eqToHom (rhoQPow_word f m) := by
  cases m with
  | ofNat n =>
    induction n with
    | zero => rfl
    | succ n ih =>
      change QPiTwoEnvelope.toHom (QPiSupercategory.σ (R := k) (qPowNat k n f)).hom ≫
        QPiTwoEnvelope.toHom (σPowNat k n f).hom = _
      change QPiTwoEnvelope.toHom (σPowNat k n f).hom = _ at ih
      rw [sigma_bicat, ih]
      exact eqToHom_trans _ _
  | negSucc n =>
    suffices h : ∀ n, QPiTwoEnvelope.toHom (σbarPowNat k n f).hom =
        eqToHom (congrArg (fun z => z.obj.obj) (qinvPowNat_normal f n)) by
      exact h (n + 1)
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      change QPiTwoEnvelope.toHom (QPiSupercategory.σbar (R := k) (qinvPowNat k n f)).hom ≫
        QPiTwoEnvelope.toHom (σbarPowNat k n f).hom = _
      rw [sigmabar_bicat, ih]
      exact eqToHom_trans _ _
theorem rhoSigmaPow_inv {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (m : ℤ) :
    QPiTwoEnvelope.toHom (σPow k m f).inv = eqToHom (rhoQPow_word f m).symm := by
  have h := congrArg (fun x => QPiTwoEnvelope.toHom x) (σPow k m f).hom_inv_id
  change QPiTwoEnvelope.toHom (σPow k m f).hom ≫
    QPiTwoEnvelope.toHom (σPow k m f).inv = 𝟙 _ at h
  rw [rhoSigmaPow_hom] at h
  apply (cancel_epi (eqToHom (rhoQPow_word f m))).mp
  simpa only [eqToHom_trans, eqToHom_refl] using h

theorem rhoPiPow_word {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (p : ZMod 2) :
    (piPow k p f).obj.obj = f.obj.obj := by
  rw [piPow_normal]

private theorem zeta_hom_zero {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b)
    (hf : f.par = 0) :
    QPiTwoEnvelope.toHom (PiSupercategory.ζ (R := k) f).hom =
      eqToHom (source_left f.obj.obj) := by
  change QEnvelope.toHom (Envelope.toHom (twist k f.par
    (PiTwoSupercategory.ζ (R := k) b.unrev).hom) ▷ f.obj ≫ (leftUnitor f.obj).hom) = _
  rw [hf, twist_zero]
  change (𝟙 _ ▷ f.obj.obj) ≫ (leftUnitor f.obj.obj).hom = _
  rw [TwoSupercategory.id_whiskerRight (R := k), Category.id_comp]
  exact source_left_hom f.obj.obj

theorem rhoZetaPow_hom_zero {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b)
    (p : ZMod 2) (hf : f.par = 0) :
    QPiTwoEnvelope.toHom (ζPow k p f).hom = eqToHom (rhoPiPow_word f p) := by
  fin_cases p
  · rfl
  · exact zeta_hom_zero f hf

theorem rhoZetaPow_inv_zero {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b)
    (p : ZMod 2) (hf : f.par = 0) :
    QPiTwoEnvelope.toHom (ζPow k p f).inv = eqToHom (rhoPiPow_word f p).symm := by
  have h := congrArg (fun x => QPiTwoEnvelope.toHom x) (ζPow k p f).hom_inv_id
  change QPiTwoEnvelope.toHom (ζPow k p f).hom ≫
    QPiTwoEnvelope.toHom (ζPow k p f).inv = 𝟙 _ at h
  rw [rhoZetaPow_hom_zero f p hf] at h
  apply (cancel_epi (eqToHom (rhoPiPow_word f p))).mp
  simpa only [eqToHom_trans, eqToHom_refl] using h
private theorem underlying_eq {a b : TwoSRev k (Uqπ D Sc sy hc)} {f g : a ⟶ b}
    (e : f = g) : QPiTwoEnvelope.toHom (eqToHom e) =
      eqToHom (congrArg (fun z => z.obj.obj) e) := by
  cases e
  rfl

private theorem right_eq {a b c : TwoSRev k (Uqπ D Sc sy hc)}
    {f g : a ⟶ b} (x : f ⟶ g) (h : b ⟶ c) (e : f.obj.obj = g.obj.obj)
    (hx : QPiTwoEnvelope.toHom x = eqToHom e) :
    QPiTwoEnvelope.toHom (x ▷ h) = eqToHom (congrArg (h.obj.obj ≫ ·) e) := by
  change QEnvelope.toHom (h.obj ◁ twist k h.par (Envelope.toHom x)) = _
  have he : Envelope.toHom x ∈ parity (R := k) _ _ 0 := by
    change QPiTwoEnvelope.toHom x ∈ parity (R := k) _ _ 0
    rw [hx]
    exact eqToHom_mem e
  rw [twist_of_mem _ he, mul_zero, sign_zero, one_smul]
  change h.obj.obj ◁ QPiTwoEnvelope.toHom x = _
  rw [hx, TwoSupercategory.whiskerLeft_eqToHom k]

private theorem left_eq_zero {a b c : TwoSRev k (Uqπ D Sc sy hc)}
    (f : a ⟶ b) {g h : b ⟶ c} (x : g ⟶ h) (hf : f.par = 0)
    (e : g.obj.obj = h.obj.obj) (hx : QPiTwoEnvelope.toHom x = eqToHom e) :
    QPiTwoEnvelope.toHom (f ◁ x) = eqToHom (congrArg (· ≫ f.obj.obj) e) := by
  change QEnvelope.toHom (Envelope.toHom (twist k f.par x) ▷ f.obj) = _
  rw [hf, twist_zero]
  change QPiTwoEnvelope.toHom x ▷ f.obj.obj = _
  rw [hx, TwoSupercategory.eqToHom_whiskerRight k]

private theorem qpar {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (m : ℤ) :
    (qPow k m f).par = f.par := by rw [qPow_normal]

private theorem rhoEnvelope_normal {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    (rhoEnvelope t ht).map f =
      ⟨f.par, ⟨f.obj.shift + (rhoMap f.obj.obj).obj.shift, (rhoMap f.obj.obj).obj.obj⟩⟩ := by
  rw [rhoEnvelope_map, piPow_normal, qPow_normal]
  apply Envelope.ext
  · exact add_zero _
  · rfl

theorem rhoEnvelope_map_comp_eq {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    (rhoEnvelope t ht).map (f ≫ g) = (rhoEnvelope t ht).map f ≫ (rhoEnvelope t ht).map g := by
  rw [rhoEnvelope_normal, rhoEnvelope_normal, rhoEnvelope_normal]
  change (⟨f.par + g.par, ⟨f.obj.shift + g.obj.shift + (rhoMap (f.obj.obj ≫ g.obj.obj)).obj.shift,
    (rhoMap (f.obj.obj ≫ g.obj.obj)).obj.obj⟩⟩ :
      (rhoEnvelope t ht).obj a ⟶ (rhoEnvelope t ht).obj c) = _
  rw [rhoMap_comp]
  apply Envelope.ext
  · exact add_comm _ _
  · apply QEnvelope.ext
    · change _ + _ + (_ + _) = _ + _ + (_ + _)
      abel
    · rfl
private theorem underlying_comp {a b : TwoSRev k (Uqπ D Sc sy hc)}
    {f g h : a ⟶ b} (x : f ⟶ g) (y : g ⟶ h) :
    QPiTwoEnvelope.toHom (x ≫ y) = QPiTwoEnvelope.toHom x ≫ QPiTwoEnvelope.toHom y := rfl

private theorem underlying_smul {a b : TwoSRev k (Uqπ D Sc sy hc)}
    {f g : a ⟶ b} (r : k) (x : f ⟶ g) :
    QPiTwoEnvelope.toHom (r • x) = r • QPiTwoEnvelope.toHom x := rfl

private theorem comparison_normal {a b c : TwoSRev k (Uqπ D Sc sy hc)}
    (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) (e : h = f ≫ g)
    (hf : f.par = 0) (hg : g.par = 0) (hh : h.par = 0)
    (m n : ℤ) (p q : ZMod 2)
    (ee : (piPow k q (qPow k n g)).obj.obj ≫ (piPow k p (qPow k m f)).obj.obj =
      (piPow k (p + q) (qPow k (m + n) h)).obj.obj) :
    QPiTwoEnvelope.toHom
      ((ζPow k p _).hom ▷ piPow k q (qPow k n g) ≫
       qPow k m f ◁ (ζPow k q _).hom ≫
       ((σPow k m f).hom ▷ qPow k n g ≫
        f ◁ (σPow k n g).hom ≫ eqToHom e.symm ≫ (σPow k (m + n) h).inv) ≫
       (ζPow (B := a ⟶ c) k (p + q) (qPow k (m + n) h)).inv) = eqToHom ee := by
  have hfm : (qPow k m f).par = 0 := (qpar f m).trans hf
  have hgn : (qPow k n g).par = 0 := (qpar g n).trans hg
  have hhmn : (qPow k (m + n) h).par = 0 := (qpar h (m+n)).trans hh
  simp only [underlying_comp]
  rw [right_eq _ _ _ (rhoZetaPow_hom_zero _ _ hfm),
    left_eq_zero _ _ hfm _ (rhoZetaPow_hom_zero _ _ hgn),
    right_eq _ _ _ (rhoSigmaPow_hom _ _),
    left_eq_zero _ _ hf _ (rhoSigmaPow_hom _ _),
    underlying_eq, rhoSigmaPow_inv, rhoZetaPow_inv_zero _ _ hhmn]
  simp only [eqToHom_trans]

theorem rhoEnvelope_mapComp_scalar {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    ((rhoEnvelope t ht).mapComp f g).hom = sign k (f.par * g.par) •
      eqToHom (rhoEnvelope_map_comp_eq t ht f g).symm := by
  change QPiTwoEnvelope.toHom ((rhoEnvelope t ht).mapComp f g).hom =
    sign k (f.par * g.par) • QPiTwoEnvelope.toHom (eqToHom (rhoEnvelope_map_comp_eq t ht f g).symm)
  rw [rhoEnvelope_mapComp_hom, underlying_smul, underlying_eq]
  exact congrArg (sign k (f.par * g.par) • ·)
    (comparison_normal (rhoMap f.obj.obj) (rhoMap g.obj.obj) (rhoMap (f.obj.obj ≫ g.obj.obj))
      (rhoMap_comp _ _) rfl rfl rfl f.obj.shift g.obj.shift f.par g.par _)

theorem rhoInverse_map_comp_eq {a b c : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (g : b ⟶ c) :
    (rhoInverse t ht).map (f ≫ g) = (rhoInverse t ht).map f ≫ (rhoInverse t ht).map g :=
  rhoEnvelope_map_comp_eq (-t) (by simpa using ht) g f

theorem rhoInverse_mapComp_scalar {a b c : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (g : b ⟶ c) :
    ((rhoInverse t ht).mapComp f g).hom = sign k (f.par * g.par) •
      eqToHom (rhoInverse_map_comp_eq t ht f g).symm := by
  rw [rhoInverse_mapComp, rhoEnvelope_mapComp_scalar]
  rw [mul_comm]

theorem rhoForwardInverse_comp_eq {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    ((rhoEnvelope t ht).comp (rhoInverse t ht)).map (f ≫ g) =
      ((rhoEnvelope t ht).comp (rhoInverse t ht)).map f ≫
      ((rhoEnvelope t ht).comp (rhoInverse t ht)).map g := by
  simp only [TwoSuperfunctor.comp_map, rhoInverse_rho_map]

theorem rhoInverseForward_comp_eq {a b c : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (g : b ⟶ c) :
    ((rhoInverse t ht).comp (rhoEnvelope t ht)).map (f ≫ g) =
      ((rhoInverse t ht).comp (rhoEnvelope t ht)).map f ≫
      ((rhoInverse t ht).comp (rhoEnvelope t ht)).map g := by
  simp only [TwoSuperfunctor.comp_map, rho_rhoInverse_map]

private theorem signed_transport_comp {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {x y z : C} (e : x = y) (d : y = z) (p : ZMod 2) :
    (sign k p • eqToHom e) ≫ (sign k p • eqToHom d) = eqToHom (e.trans d) := by
  rw [Linear.smul_comp, Linear.comp_smul, smul_smul, sign_mul_self, one_smul, eqToHom_trans]

private theorem rhoInverse_par {a b : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) :
    ((rhoInverse t ht).map f).par = f.par :=
  rhoEnvelope_map_par (-t) (by simpa only [neg_sq] using ht) f

private theorem rhoInverse_map_eq {a b : TwoSRev k (Uqπ D Sc sy hc)} {f g : a ⟶ b} (e : f = g) :
    (rhoInverse t ht).map₂ (eqToHom e) = eqToHom (congrArg (rhoInverse t ht).map e) := by
  cases e
  exact TwoSuperfunctor.map₂_id _ _

private theorem rhoEnvelope_map_eq {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (e : f = g) :
    (rhoEnvelope t ht).map₂ (eqToHom e) = eqToHom (congrArg (rhoEnvelope t ht).map e) := by
  cases e
  exact TwoSuperfunctor.map₂_id _ _

private theorem comparison_cancel
    {B C : Type*} [BicategoryStruct B] [BicategoryStruct C]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
    [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear k (a ⟶ b)]
    [∀ a b : C, Supercategory k (a ⟶ b)] [TwoSupercategory k C]
    (F : TwoSuperfunctor k B C) (G : TwoSuperfunctor k C B)
    {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
    (eF : F.map (f ≫ g) = F.map f ≫ F.map g)
    (eG : G.map (F.map f ≫ F.map g) = G.map (F.map f) ≫ G.map (F.map g))
    (p : ZMod 2)
    (hF : (F.mapComp f g).hom = sign k p • eqToHom eF.symm)
    (hG : (G.mapComp (F.map f) (F.map g)).hom = sign k p • eqToHom eG.symm) :
    (F.comp G).mapComp f g = eqToIso ((congrArg G.map eF).trans eG).symm := by
  apply Iso.ext
  simp only [TwoSuperfunctor.comp_mapComp, Iso.trans_hom, TwoSuperfunctor.map₂Iso_hom]
  rw [hG, hF, TwoSuperfunctor.map₂_smul]
  have he : G.map₂ (eqToHom eF.symm) = eqToHom (congrArg G.map eF.symm) := by
    have map_eq {x y : F.obj a ⟶ F.obj c} (e : x = y) :
        G.map₂ (eqToHom e) = eqToHom (congrArg G.map e) := by
      cases e
      exact G.map₂_id _
    exact map_eq _
  rw [he]
  exact signed_transport_comp _ _ _

theorem rhoForwardInverse_mapComp {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    ((rhoEnvelope t ht).comp (rhoInverse t ht)).mapComp f g =
      eqToIso (rhoForwardInverse_comp_eq t ht f g).symm := by
  apply comparison_cancel (rhoEnvelope t ht) (rhoInverse t ht) f g
    (rhoEnvelope_map_comp_eq t ht f g)
    (rhoInverse_map_comp_eq t ht _ _) (f.par * g.par)
  · exact rhoEnvelope_mapComp_scalar t ht f g
  · simpa only [rhoEnvelope_map_par] using
      rhoInverse_mapComp_scalar t ht ((rhoEnvelope t ht).map f) ((rhoEnvelope t ht).map g)

theorem rhoInverseForward_mapComp {a b c : TwoSRev k (Uqπ D Sc sy hc)} (f : a ⟶ b) (g : b ⟶ c) :
    ((rhoInverse t ht).comp (rhoEnvelope t ht)).mapComp f g =
      eqToIso (rhoInverseForward_comp_eq t ht f g).symm := by
  apply comparison_cancel (rhoInverse t ht) (rhoEnvelope t ht) f g
    (rhoInverse_map_comp_eq t ht f g)
    (rhoEnvelope_map_comp_eq t ht _ _) (f.par * g.par)
  · exact rhoInverse_mapComp_scalar t ht f g
  · simpa only [rhoInverse_par] using
      rhoEnvelope_mapComp_scalar t ht ((rhoInverse t ht).map f) ((rhoInverse t ht).map g)
theorem rhoForwardInverse_isStrict :
    ((rhoEnvelope (sy := sy) (hc := hc) t ht).comp (rhoInverse t ht)).IsStrict where
  map_comp := rhoForwardInverse_comp_eq t ht
  map_id a := rhoInverse_rho_map t ht (𝟙 a)
  mapComp_eq := rhoForwardInverse_mapComp t ht
  mapId_eq := rhoForwardInverse_mapId t ht

theorem rhoInverseForward_isStrict :
    ((rhoInverse (sy := sy) (hc := hc) t ht).comp (rhoEnvelope t ht)).IsStrict where
  map_comp := rhoInverseForward_comp_eq t ht
  map_id a := rho_rhoInverse_map t ht (𝟙 a)
  mapComp_eq := rhoInverseForward_mapComp t ht
  mapId_eq := rhoInverseForward_mapId t ht

end OddMath.SKM.RhoInverse
