import OddMath.Frontier.EQLiftSmallDerived
import DG.HalfGraded.DiagonalTransportComp

/-!
# Ellis–Qi §4.4 on half-graded modules: Definitions 4.14, 4.15, 4.18, 4.20, Corollaries 4.19, 4.21

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definitions 4.14, 4.15, 4.18, 4.20 and Corollaries 4.19, 4.21 (printed numbering), over `ℤ`.

Theorems 3.18, 4.17 and Lemma 4.16 are about half-graded dg modules (the setting of §2.2.4: an
internal `ℤ`-grading and an independent parity, `K₀` of the super derived category). The functors of
§4.4 are derived tensor products with dg bimodules; on half-graded modules each is the derived tensor
product with the diagonally regraded bimodule over the weight dg categories (`DG.Diagonal.derivedTensor`):

* `JH a b` (**Definition 4.18**): `(Z_{a+b}^∨)ᵈ ⊗^L_{ONH_{a+b}} (-)`; `J2H a b`: `(Z_a^∨ ⊠ Z_b^∨)ᵈ ⊗^L (-)` on
  `ONH_a ⊗ ONH_b`;
* `IH a b` (**Definition 4.14**): `(Z_{a,b}^∨)ᵈ ⊗^L_{OΛ_a ⊗ OΛ_b} (-)`;
* `RH a b` (**Definition 4.15**): the derived tensor product with `OΛ_a ⊗ OΛ_b` as an
  `(OΛ_a ⊗ OΛ_b, OΛ_{a+b})`-bimodule through the block swap (`Z^♮_{a,b}`, ERRATA [EQ] 24, 25);
* `IndH a b` ((3.40)): the derived tensor product with `ONH_{a+b}` as an `(ONH_{a+b}, ONH_a ⊗ ONH_b)`-bimodule
  through `ι_{a,b}`;
* `ResNatH a b` (**Definition 4.20**): `(ONH^♮_{a+b})ᵈ ⊗^L (-)`.

Each is identified with the diagonal transport of the corresponding functor on `ℤ`-graded modules
(`DG.Diagonal.derivedTensorTransportIso`; for `IndH`, `RH` with `DG.DGBimodule.derivedTensorIsoInduction`),
and the transport is functorial (`DG.Diagonal.transportCompIso`, `DG.Diagonal.transportMapIso`). Hence:

* **Corollary 4.21 on half-graded modules** (`indIsoH`, `resIsoH`): `J ∘ Ind ≅ I ∘ J` and `R ∘ J ≅ J ∘ Res^♮`
  as functors of half-graded derived categories, for all `a`, `b`, transported from `EQLift.indIsoDAny`,
  `EQLift.resNatIsoDAny`;
* **Corollary 4.19 on half-graded modules** (`jHFullyFaithful`): `J` is fully faithful in every rank: for
  `a + b ≥ 2` the half-graded derived category of `ONH_{a+b}` is zero (`isZero_halfGraded_of_d_eq_one`, from
  an element `t` of degree `-1` with `d t = 1`), and for `a + b ≤ 1`, `J ≅ χ^*` with `χ : ONH_{a+b} ≅ OΛ_{a+b}`
  bijective, an equivalence whose transport is an equivalence (`transportFullyFaithfulOfIsEquivalence`).

The `K₀` statement of Corollary 4.19 is `OddMath.Frontier.EQCor419K0`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open CategoryTheory Limits

namespace OddMath.Frontier.EQLift

open OddMath.Frontier.EQSkewDifferential (osymDG Zn)
open OddMath.Frontier.EQK0Int (ONHAll ONHTensor)
open OddMath.Frontier.EQFunctor
open DG DG.HalfGradedDGRing MulOpposite

/-! ### Half-graded modules over a dg ring with a contracting element -/

section Contraction

variable {A : Type} [Ring A] [DGAddCommGroup A] [DGRing A] {t : A} (ht : t ∈ DG.grading (-1 : ℤ))
  (hd : DG.d t = 1)

/-- `t` placed in cohomological degree `-1` and weight `0` of the diagonal regraded ring. -/
def contractionPlace : (ofDGRing A).Regraded :=
  (ofDGRing A).place (-1, 0) t (by rw [ofDGRing_hgrading_halfDegree_zero]; exact ht)

theorem contractionPlace_mem_wgrading : contractionPlace ht ∈ wgrading (M := (ofDGRing A).Regraded) 0 :=
  place_mem_wgrading (H := ofDGRing A) (-1, 0) _

include hd in
theorem d_contractionPlace : DG.d (contractionPlace ht) = 1 := by
  rw [contractionPlace, d_place, one_eq_place]
  exact place_congr (by decide) hd _ _

/-- The contracting endomorphism of every object of the weight dg category. -/
def contractionPlaceHom (X : WeightCategory (ofDGRing A).Regraded) : X ⟶ X :=
  WeightCategory.homMk (contractionPlace ht) (by simpa using contractionPlace_mem_wgrading ht)

theorem contractionPlaceHom_mem_grading (X : WeightCategory (ofDGRing A).Regraded) :
    contractionPlaceHom ht X ∈ DG.grading (-1 : ℤ) :=
  place_mem_grading (H := ofDGRing A) (-1, 0) _

include hd in
theorem d_contractionPlaceHom (X : WeightCategory (ofDGRing A).Regraded) :
    DG.d (contractionPlaceHom ht X) = 𝟙 X :=
  WeightCategory.hom_ext (d_contractionPlace ht hd)

include ht hd in
/-- **Every half-graded module over a dg ring with `d t = 1`, `t` of degree `-1`, is acyclic.** -/
theorem isAcyclic_halfGraded_of_d_eq_one (M : CatModule.{0} (WeightCategory (ofDGRing A).Regraded)) :
    CatModule.IsAcyclic M := by
  intro X
  refine DG.isAcyclic_iff.mpr fun k m hm hdm => ⟨(contractionPlaceHom ht X) • m, ?_, ?_⟩
  · have h := CatModule.smul_mem_grading (contractionPlaceHom_mem_grading ht X) hm
    simpa only [neg_add_eq_sub] using h
  · rw [CatModule.d_smul (contractionPlaceHom_mem_grading ht X), d_contractionPlaceHom ht hd,
      CatModule.id_smul, hdm, CatModule.smul_zero, smul_zero, add_zero]

include ht hd in
/-- **The half-graded derived category of a dg ring with `d t = 1`, `t` of degree `-1`, is zero.** -/
theorem isZero_halfGraded_of_d_eq_one
    [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing A).Regraded)]
    (X : CatModule.DerivedCategory.{0, 0} (WeightCategory (ofDGRing A).Regraded)) : IsZero X := by
  have := Localization.essSurj (CatModule.DerivedCategory.Q (C := WeightCategory (ofDGRing A).Regraded))
    (CatModule.quasiIso (WeightCategory (ofDGRing A).Regraded))
  exact ((CatModule.DerivedCategory.isZero_Q_obj_iff _).mpr
    (isAcyclic_halfGraded_of_d_eq_one ht hd _)).of_iso
    (CatModule.DerivedCategory.Q.objObjPreimageIso X).symm

end Contraction

/-! ### Generic facts -/

/-- A bijective morphism of dg rings is a quasi-isomorphism. -/
theorem isQuasiIso_of_bijective {A B : Type*} [Ring A] [DGAddCommGroup A] [Ring B] [DGAddCommGroup B]
    (f : A →ᵈᵍ+* B) (hf : Function.Bijective f) : f.IsQuasiIso := fun n => by
  have h1 : f.comp (DGRingHom.invOfBijective f hf) = DGRingHom.id :=
    DGRingHom.ext (DGRingHom.apply_invOfBijective f hf)
  have h2 : (DGRingHom.invOfBijective f hf).comp f = DGRingHom.id :=
    DGRingHom.ext (DGRingHom.invOfBijective_apply f hf)
  refine ⟨Function.LeftInverse.injective (g := (DGRingHom.invOfBijective f hf).cohomologyMap n)
    fun x => ?_, Function.RightInverse.surjective (g := (DGRingHom.invOfBijective f hf).cohomologyMap n)
    fun y => ?_⟩
  · rw [← AddMonoidHom.comp_apply, ← DGRingHom.cohomologyMap_comp, h2, DGRingHom.cohomologyMap_id]
    rfl
  · rw [← AddMonoidHom.comp_apply, ← DGRingHom.cohomologyMap_comp, h1, DGRingHom.cohomologyMap_id]
    rfl

/-- A functor out of a category whose objects are all zero is fully faithful onto zero objects. -/
def fullyFaithfulOfIsZero {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    [HasZeroMorphisms D] (F : C ⥤ D) [F.PreservesZeroMorphisms] (hz : ∀ X : C, IsZero X) :
    F.FullyFaithful where
  preimage _ := 0
  map_preimage {X _} _ := (F.map_isZero (hz X)).eq_of_src _ _
  preimage_map {X _} _ := (hz X).eq_of_src _ _

section TransportEquivalence

variable {A B : Type} [Ring A] [DGAddCommGroup A] [DGRing A] [Ring B] [DGAddCommGroup B] [DGRing B]
  [DG.HasDerivedCategory.{0, 0} A] [DG.HasDerivedCategory.{0, 0} B]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing A).Regraded)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing B).Regraded)]

/-- The diagonal transport of a triangulated equivalence is fully faithful. -/
def transportFullyFaithfulOfIsEquivalence
    (F : DG.DerivedCategory.{0, 0} A ⥤ DG.DerivedCategory.{0, 0} B) [F.CommShift ℤ] [F.IsTriangulated]
    [F.IsEquivalence] : (Diagonal.transport.{0, 0, 0, 0, 0, 0, 0, 0} A B F).FullyFaithful := by
  let E := F.asEquivalence
  letI : E.functor.CommShift ℤ := (inferInstance : F.CommShift ℤ)
  haveI : E.functor.IsTriangulated := (inferInstance : F.IsTriangulated)
  letI : E.inverse.CommShift ℤ := E.commShiftInverse ℤ
  haveI : E.CommShift ℤ := E.commShift_of_functor ℤ
  haveI : E.IsTriangulated := Equivalence.IsTriangulated.mk' E inferInstance
  exact Diagonal.transportFullyFaithful F E.inverse E.unitIso.symm E.counitIso

end TransportEquivalence

/-! ### The half-graded functors -/

variable (a b : ℕ)
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ONHTensor a b))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (ONHAll (a + b)))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (LABg a b))]
  [CatModule.HasDerivedCategory.{0, 0} (SingleObj (osymDG (a + b)))]
  [DG.HasDerivedCategory.{0, 0} (ONHTensor a b)] [DG.HasDerivedCategory.{0, 0} (ONHAll (a + b))]
  [DG.HasDerivedCategory.{0, 0} (LABg a b)] [DG.HasDerivedCategory.{0, 0} (osymDG (a + b))]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (ONHTensor a b)).Regraded)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (ONHAll (a + b))).Regraded)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (LABg a b)).Regraded)]
  [CatModule.HasDerivedCategory.{0, 0} (WeightCategory (ofDGRing (osymDG (a + b))).Regraded)]

/-- `ONH_{a+b}` is K-projective as a left module over itself (as an `(ONH_{a+b}, ONH_a ⊗ ONH_b)`-bimodule). -/
theorem iotaBimodule_isKProjective : IsKProjective.{0} (ONHAll (a + b)) (iotaAll a b).Bimodule :=
  isKProjective_self (ONHAll (a + b))

/-- `OΛ_a ⊗ OΛ_b` is K-projective as a left module over itself (as a bimodule through the block swap). -/
theorem swapBimodule_isKProjective : IsKProjective.{0} (LABg a b) (swapDGG a b).Bimodule :=
  isKProjective_self (LABg a b)

/-- **Definition 4.18 on half-graded modules**: `J = (Z^∨)ᵈ ⊗^L_{ONH_{a+b}} (-)`. -/
abbrev JH :=
  Diagonal.derivedTensor (osymDG (a + b)) (ONHAll (a + b)) (RightDual (osymDG (a + b)) (Zn (a + b)))
    (znDual_isKProjective (a + b))

/-- `J` on half-graded `ONH_a ⊗ ONH_b`-modules: `(Z_a^∨ ⊠ Z_b^∨)ᵈ ⊗^L (-)`. -/
abbrev J2H :=
  Diagonal.derivedTensor (LABg a b) (ONHTensor a b) (ZZDualg a b)
    (ExternalTensor.isKProjective (znDual_isKProjective a) (znDual_isKProjective b))

/-- **Definition 4.14 on half-graded modules**: `I = (Z_{a,b}^∨)ᵈ ⊗^L_{OΛ_a ⊗ OΛ_b} (-)`. -/
abbrev IH :=
  Diagonal.derivedTensor (osymDG (a + b)) (LABg a b) (ZabDualG a b) (zdual_isKProjective (a := a) (b := b))

/-- **Definition 4.15 on half-graded modules**: `R`, the derived tensor product with `OΛ_a ⊗ OΛ_b` as a bimodule
through the block swap. -/
abbrev RH :=
  Diagonal.derivedTensor (LABg a b) (osymDG (a + b)) (swapDGG a b).Bimodule (swapBimodule_isKProjective a b)

/-- `Ind` ((3.40)) on half-graded modules: the derived tensor product with `ONH_{a+b}` as a bimodule through
`ι_{a,b}`. -/
abbrev IndH :=
  Diagonal.derivedTensor (ONHAll (a + b)) (ONHTensor a b) (iotaAll a b).Bimodule (iotaBimodule_isKProjective a b)

/-- **Definition 4.20 on half-graded modules**: `Res^♮ = (ONH^♮)ᵈ ⊗^L (-)`. -/
abbrev ResNatH :=
  Diagonal.derivedTensor (ONHTensor a b) (ONHAll (a + b)) (ONHNatAll a b) (onhNatAll_isKProjective_all a b)

/-! ### Identification with the transports of the `ℤ`-graded functors -/

/-- `ONH_{a+b} ⊗^L_{ONH_a ⊗ ONH_b} (-)` is derived induction along `ι_{a,b}`. -/
def indBimoduleIso :
    DGBimodule.derivedTensor.{0, 0, 0, 0} (ONHAll (a + b)) (ONHTensor a b) (iotaAll a b).Bimodule
        (iotaBimodule_isKProjective a b) ≅ IndDAll.{0, 0} a b :=
  DGBimodule.derivedTensorIsoInduction (iotaAll a b) (iotaBimodule_isKProjective a b) (AddEquiv.refl _)
    Iff.rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- `(OΛ_a ⊗ OΛ_b) ⊗^L_{OΛ_{a+b}} (-)` is derived induction along the block swap. -/
def swapBimoduleIso :
    DGBimodule.derivedTensor.{0, 0, 0, 0} (LABg a b) (osymDG (a + b)) (swapDGG a b).Bimodule
        (swapBimodule_isKProjective a b) ≅ RDAll.{0, 0} a b :=
  DGBimodule.derivedTensorIsoInduction (swapDGG a b) (swapBimodule_isKProjective a b) (AddEquiv.refl _)
    Iff.rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/-- `J` on half-graded modules is the transport of `J`. -/
def jHTransportIso :
    JH a b ≅ Diagonal.transport.{0, 0, 0, 0, 0, 0, 0, 0} (ONHAll (a + b)) (osymDG (a + b)) (JDAll.{0, 0} a b) :=
  Diagonal.derivedTensorTransportIso _ _ _ _

def j2HTransportIso :
    J2H a b ≅ Diagonal.transport.{0, 0, 0, 0, 0, 0, 0, 0} (ONHTensor a b) (LABg a b) (J2DAll.{0, 0} a b) :=
  Diagonal.derivedTensorTransportIso _ _ _ _

def iHTransportIso :
    IH a b ≅ Diagonal.transport.{0, 0, 0, 0, 0, 0, 0, 0} (LABg a b) (osymDG (a + b)) (IDAll.{0, 0} a b) :=
  Diagonal.derivedTensorTransportIso _ _ _ _

def resNatHTransportIso :
    ResNatH a b ≅
      Diagonal.transport.{0, 0, 0, 0, 0, 0, 0, 0} (ONHAll (a + b)) (ONHTensor a b) (ResNatDAllAny.{0} a b) :=
  Diagonal.derivedTensorTransportIso _ _ _ _

def indHTransportIso :
    IndH a b ≅ Diagonal.transport.{0, 0, 0, 0, 0, 0, 0, 0} (ONHTensor a b) (ONHAll (a + b)) (IndDAll.{0, 0} a b) :=
  Diagonal.derivedTensorTransportIso _ _ _ _ ≪≫ Diagonal.transportMapIso _ _ (indBimoduleIso a b)

def rHTransportIso :
    RH a b ≅ Diagonal.transport.{0, 0, 0, 0, 0, 0, 0, 0} (osymDG (a + b)) (LABg a b) (RDAll.{0, 0} a b) :=
  Diagonal.derivedTensorTransportIso _ _ _ _ ≪≫ Diagonal.transportMapIso _ _ (swapBimoduleIso a b)

/-! ### Corollary 4.21 on half-graded modules -/

/-- **Ellis–Qi, Corollary 4.21, induction half, on half-graded modules**: `J ∘ Ind ≅ I ∘ J`. -/
def indIsoH : IndH a b ⋙ JH a b ≅ J2H a b ⋙ IH a b :=
  Functor.isoWhiskerRight (indHTransportIso a b) _ ≪≫ Functor.isoWhiskerLeft _ (jHTransportIso a b) ≪≫
    (Diagonal.transportCompIso _ _).symm ≪≫ Diagonal.transportMapIso _ _ (indIsoDAny.{0} a b) ≪≫
    Diagonal.transportCompIso _ _ ≪≫ Functor.isoWhiskerRight (j2HTransportIso a b).symm _ ≪≫
    Functor.isoWhiskerLeft _ (iHTransportIso a b).symm

/-- **Ellis–Qi, Corollary 4.21, restriction half, on half-graded modules**: `R ∘ J ≅ J ∘ Res^♮`. -/
def resIsoH : JH a b ⋙ RH a b ≅ ResNatH a b ⋙ J2H a b :=
  Functor.isoWhiskerRight (jHTransportIso a b) _ ≪≫ Functor.isoWhiskerLeft _ (rHTransportIso a b) ≪≫
    (Diagonal.transportCompIso _ _).symm ≪≫ Diagonal.transportMapIso _ _ (resNatIsoDAny.{0} a b) ≪≫
    Diagonal.transportCompIso _ _ ≪≫ Functor.isoWhiskerRight (resNatHTransportIso a b).symm _ ≪≫
    Functor.isoWhiskerLeft _ (j2HTransportIso a b).symm

/-! ### Corollary 4.19 on half-graded modules -/

/-- **Ellis–Qi, Corollary 4.19 on half-graded modules**: `J` is fully faithful in every rank. -/
def jHFullyFaithful : (JH a b).FullyFaithful :=
  if h : 2 ≤ a + b then
    fullyFaithfulOfIsZero _ fun X => by
      obtain ⟨_, ht, hd⟩ := exists_d_eq_one_ONHAll (a + b) h
      exact isZero_halfGraded_of_d_eq_one ht hd X
  else
    have hAB : a + b ≤ 1 := by omega
    haveI : (chiE hAB (ONHAll (a + b))).derivedInduction.{0, 0, 0, 0}.IsEquivalence :=
      DGRingHom.derivedInduction_isEquivalence _
        (isQuasiIso_of_bijective _ (chiE_bijective hAB (fullActionAll (a + b))))
    haveI : (JDAll.{0, 0} a b).IsEquivalence := Functor.isEquivalence_of_iso (jDAllIsoChi a b hAB).symm
    (transportFullyFaithfulOfIsEquivalence (JDAll.{0, 0} a b)).ofIso (jHTransportIso a b).symm

end OddMath.Frontier.EQLift
