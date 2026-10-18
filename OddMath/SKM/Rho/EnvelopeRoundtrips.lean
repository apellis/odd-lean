import OddMath.SKM.Rho.InverseComparisons

/-!
# Envelope Roundtrips for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
Reduction of arbitrary, possibly nonhomogeneous, envelope 2-morphisms to
the quotient roundtrip. The quotient premise is discharged in MapInverses.
-/

noncomputable section
namespace OddMath.SKM.RhoInverse
open CategoryTheory StringDiagrams BicategoryStruct RhoWords RhoTwo RhoExtension
  QPiSupercategory Envelope
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D}
  {hc : Sc.Homogeneous}
local instance (a b : TwoSRev k (Uqπ D Sc sy hc)) : QPiSupercategory k (a ⟶ b) :=
  QPiTwoSupercategory.homQPiLeft a b

theorem rhoEnvelope_base (t : k) (ht : t ^ 2 = -1)
    {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    ((rhoEnvelope t ht).map f).obj.obj = (rhoMap f.obj.obj).obj.obj := by
  rw [rhoEnvelope_map, rhoPiPow_word, rhoQPow_word]

theorem rhoEnvelope_map₂_base_heq (t : k) (ht : t ^ 2 = -1)
    {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g) :
    HEq ((rhoEnvelope t ht).map₂ η)
      (rhoMap₂ t ht f.obj.obj g.obj.obj (QPiTwoEnvelope.toHom η)) := by
  rw [rhoEnvelope_map₂]
  change HEq (QPiTwoEnvelope.toHom (ζPow (B := (rhoEnvelope t ht).obj a ⟶ (rhoEnvelope t ht).obj b) k f.par _).hom ≫
    (QPiTwoEnvelope.toHom (σPow k f.obj.shift (rhoMap f.obj.obj)).hom ≫
      QPiTwoEnvelope.toHom (rhoMap₂ t ht f.obj.obj g.obj.obj (QPiTwoEnvelope.toHom η)) ≫
      QPiTwoEnvelope.toHom (σPow k g.obj.shift (rhoMap g.obj.obj)).inv) ≫
    QPiTwoEnvelope.toHom (ζPow (B := (rhoEnvelope t ht).obj a ⟶ (rhoEnvelope t ht).obj b) k g.par _).inv) _
  have hf : (qPow k f.obj.shift (rhoMap f.obj.obj)).par = 0 := by
    rw [qPow_normal]; rfl
  have hg : (qPow k g.obj.shift (rhoMap g.obj.obj)).par = 0 := by
    rw [qPow_normal]; rfl
  rw [rhoZetaPow_hom_zero _ _ hf, rhoZetaPow_inv_zero _ _ hg,
    rhoSigmaPow_hom, rhoSigmaPow_inv]
  simp only [← Category.assoc, comp_eqToHom_heq_iff, eqToHom_trans,
    eqToHom_comp_heq_iff]
  rfl

private theorem rhoMap₂_congr_heq (t : k) (ht : t ^ 2 = -1)
    {a b : UGr D Sc sy hc} {f g f' g' : a ⟶ b}
    (ef : f = f') (eg : g = g') {η : f ⟶ g} {θ : f' ⟶ g'} (h : HEq η θ) :
    HEq (rhoMap₂ t ht f g η) (rhoMap₂ t ht f' g' θ) := by
  subst f' g'
  cases h
  rfl

theorem rhoEnvelope_map₂_relabel_heq (t : k) (ht : t ^ 2 = -1)
    {a b : Uqπ D Sc sy hc} {f g f' g' : a ⟶ b}
    (ef : f.obj.obj = f'.obj.obj) (eg : g.obj.obj = g'.obj.obj)
    {η : f ⟶ g} {θ : f' ⟶ g'} (h : HEq η θ) :
    HEq ((rhoEnvelope t ht).map₂ η) ((rhoEnvelope t ht).map₂ θ) := by
  exact (rhoEnvelope_map₂_base_heq t ht η).trans
    ((rhoMap₂_congr_heq t ht ef eg h).trans (rhoEnvelope_map₂_base_heq t ht θ).symm)

theorem rhoEnvelope_twice_relabel_heq (t z : k) (ht : t ^ 2 = -1) (hz : z ^ 2 = -1)
    {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g) :
    HEq ((rhoEnvelope z hz).map₂ ((rhoEnvelope t ht).map₂ η))
      ((rhoEnvelope z hz).map₂ ((rhoEnvelope t ht).map₂
        (show (⟨0, ⟨0, f.obj.obj⟩⟩ : a ⟶ b) ⟶ ⟨0, ⟨0, g.obj.obj⟩⟩ from η))) := by
  apply rhoEnvelope_map₂_relabel_heq z hz
  · exact (rhoEnvelope_base t ht f).trans (rhoEnvelope_base t ht ⟨0, ⟨0, f.obj.obj⟩⟩).symm
  · exact (rhoEnvelope_base t ht g).trans (rhoEnvelope_base t ht ⟨0, ⟨0, g.obj.obj⟩⟩).symm
  · exact rhoEnvelope_map₂_relabel_heq (f := f) (g := g)
      (f' := ⟨0, ⟨0, f.obj.obj⟩⟩) (g' := ⟨0, ⟨0, g.obj.obj⟩⟩)
      t ht rfl rfl (HEq.rfl)

theorem rhoEnvelope_bare_roundtrip_of_homogeneous
    (t z : k) (ht : t ^ 2 = -1) (hz : z ^ 2 = -1)
    (h₀ : ∀ {a b : UGr D Sc sy hc} {f g : a ⟶ b} (p : ZMod 2) (η : f ⟶ g),
      η ∈ Supercategory.parity (R := k) f g p →
      HEq ((rhoEnvelope z hz).map₂ ((rhoEnvelope t ht).map₂
        (QPiTwoEnvelope.J2 (R := k) η))) η)
    {a b : UGr D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g) :
    HEq ((rhoEnvelope z hz).map₂ ((rhoEnvelope t ht).map₂
      (QPiTwoEnvelope.J2 (R := k) η))) η := by
  let ef := rhoEnvelope_map_roundtrip t z ht hz (QPiTwoEnvelope.Jm (R := k) f)
  let eg := rhoEnvelope_map_roundtrip t z ht hz (QPiTwoEnvelope.Jm (R := k) g)
  apply (conj_eqToHom_iff_heq _ _ ef eg).mp
  refine Supercategory.induction_on (R := k) η ?_ (fun p x hx => ?_)
    (fun x y hx hy => ?_)
  · simp only [QPiTwoEnvelope.J2, Envelope.ofHom, QEnvelope.ofHom,
      TwoSuperfunctor.map₂_zero, Limits.comp_zero, Limits.zero_comp]
  · exact (conj_eqToHom_iff_heq _ _ ef eg).mpr (h₀ p x hx)
  · change (rhoEnvelope z hz).map₂ ((rhoEnvelope t ht).map₂
      ((QPiTwoEnvelope.J2 (R := k) x) + (QPiTwoEnvelope.J2 (R := k) y))) = _
    rw [TwoSuperfunctor.map₂_add, TwoSuperfunctor.map₂_add, hx, hy]
    simp only [Preadditive.comp_add, Preadditive.add_comp]

theorem rhoEnvelope_lift_roundtrip (t z : k) (ht : t ^ 2 = -1) (hz : z ^ 2 = -1)
    (h₀ : ∀ {a b : UGr D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g),
      HEq ((rhoEnvelope z hz).map₂ ((rhoEnvelope t ht).map₂
        (QPiTwoEnvelope.J2 (R := k) η))) η)
    {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g) :
    (rhoEnvelope z hz).map₂ ((rhoEnvelope t ht).map₂ η) =
      eqToHom (rhoEnvelope_map_roundtrip t z ht hz f) ≫ η ≫
        eqToHom (rhoEnvelope_map_roundtrip t z ht hz g).symm := by
  apply (conj_eqToHom_iff_heq _ _
    (rhoEnvelope_map_roundtrip t z ht hz f)
    (rhoEnvelope_map_roundtrip t z ht hz g)).mpr
  exact (rhoEnvelope_twice_relabel_heq t z ht hz η).trans (h₀ (QPiTwoEnvelope.toHom η))

theorem rhoForwardInverse_map₂_of_bare (t : k) (ht : t ^ 2 = -1)
    (h₀ : ∀ {a b : UGr D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g),
      HEq ((rhoEnvelope (-t) (by simpa only [neg_sq] using ht)).map₂
        ((rhoEnvelope t ht).map₂ (QPiTwoEnvelope.J2 (R := k) η))) η)
    {a b : Uqπ D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g) :
    ((rhoEnvelope t ht).comp (rhoInverse t ht)).map₂ η =
      eqToHom (rhoInverse_rho_map t ht f) ≫ η ≫ eqToHom (rhoInverse_rho_map t ht g).symm :=
  rhoEnvelope_lift_roundtrip t (-t) ht (by simpa only [neg_sq] using ht) h₀ η

theorem rhoInverseForward_map₂_of_bare (t : k) (ht : t ^ 2 = -1)
    (h₀ : ∀ {a b : UGr D Sc sy hc} {f g : a ⟶ b} (η : f ⟶ g),
      HEq ((rhoEnvelope t ht).map₂
        ((rhoEnvelope (-t) (by simpa only [neg_sq] using ht)).map₂
          (QPiTwoEnvelope.J2 (R := k) η))) η)
    {a b : TwoSRev k (Uqπ D Sc sy hc)} {f g : a ⟶ b} (η : f ⟶ g) :
    ((rhoInverse t ht).comp (rhoEnvelope t ht)).map₂ η =
      eqToHom (rho_rhoInverse_map t ht f) ≫ η ≫ eqToHom (rho_rhoInverse_map t ht g).symm :=
  rhoEnvelope_lift_roundtrip (-t) t (by simpa only [neg_sq] using ht) ht h₀ η

end OddMath.SKM.RhoInverse
