import StringDiagrams.Super.GradedTwoEnvelopeUniversal

/-!
# The general extension into a super-reverse

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §9,
the definition of the super-reverse and Lemma 9.6. The input functor may already
have shifted values. This is the extension used in the subsequent construction of ρ.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams StringDiagrams.Supercategory
  StringDiagrams.GradedSupercategory StringDiagrams.BicategoryStruct
  StringDiagrams.TwoSupercategory

universe r u v w u' v' w'

/-- The super-reverse of BE2 §9: reverse 1-morphisms, retaining each hom category. -/
structure TwoSRev (R : Type r) (B : Type u) where
  unrev : B

namespace TwoSRev
variable {R : Type r} {B : Type u} [BicategoryStruct.{w, v} B]

instance bicategoryStruct : BicategoryStruct (TwoSRev R B) where
  Hom a b := b.unrev ⟶ a.unrev
  id a := 𝟙 a.unrev
  comp f g := g ≫ f
  homCategory a b := inferInstanceAs (Category (b.unrev ⟶ a.unrev))
  whiskerLeft f _ _ η := η ▷ f
  whiskerRight η h := h ◁ η
  associator f g h := (associator h g f).symm
  leftUnitor f := rightUnitor f
  rightUnitor f := leftUnitor f

/-- Vertical composition is unchanged in the super-reverse. -/
theorem comp₂_eq {a b : TwoSRev R B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) :
    η ≫ θ = CategoryStruct.comp (obj := b.unrev ⟶ a.unrev) η θ := rfl

variable [CommRing R]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]

instance (a b : TwoSRev R B) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive (b.unrev ⟶ a.unrev))
instance (a b : TwoSRev R B) : Linear R (a ⟶ b) :=
  inferInstanceAs (Linear R (b.unrev ⟶ a.unrev))
instance (a b : TwoSRev R B) : Supercategory R (a ⟶ b) :=
  inferInstanceAs (Supercategory R (b.unrev ⟶ a.unrev))

instance twoSupercategory : TwoSupercategory R (TwoSRev R B) where
  whiskerLeft_id f g := id_whiskerRight (R := R) (B := B) g f
  whiskerLeft_comp f _ _ _ η θ := comp_whiskerRight (R := R) (B := B) η θ f
  id_whiskerLeft η := whiskerRight_id (R := R) (B := B) η
  comp_whiskerLeft f g _ _ η := whiskerRight_comp (R := R) (B := B) η g f
  id_whiskerRight f g := whiskerLeft_id (R := R) (B := B) g f
  comp_whiskerRight η θ i := whiskerLeft_comp (R := R) (B := B) i η θ
  whiskerRight_id η := id_whiskerLeft (R := R) (B := B) η
  whiskerRight_comp η g h := comp_whiskerLeft (R := R) (B := B) h g η
  whisker_assoc f g g' η h := by
    change whiskerLeft (B := B) h (whiskerRight (B := B) η f) =
      (associator (B := B) h g f).inv ≫
        whiskerRight (B := B) (whiskerLeft (B := B) h η) f ≫
          (associator (B := B) h g' f).hom
    rw [whisker_assoc (R := R) (B := B) h η f]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  pentagon f g h i := pentagon_inv R (B := B) i h g f
  triangle f g := by
    change (associator (B := B) g _ f).inv ≫
      whiskerRight (B := B) (rightUnitor (B := B) g).hom f =
        whiskerLeft (B := B) g (leftUnitor (B := B) f).hom
    rw [← triangle (R := R) (B := B) g f]
    simp only [Iso.inv_hom_id_assoc]
  whiskerLeft_add f _ _ η θ := add_whiskerRight (R := R) (B := B) η θ f
  add_whiskerRight η θ h := whiskerLeft_add (R := R) (B := B) h η θ
  whiskerLeft_smul f _ _ s η := smul_whiskerRight (B := B) s η f
  smul_whiskerRight s η h := whiskerLeft_smul (B := B) h s η
  whiskerLeft_mem f _ _ _ _ hη := whiskerRight_mem (B := B) f hη
  whiskerRight_mem h hη := whiskerLeft_mem (B := B) h hη
  super_interchange {_ _ _ f g h i p q η θ} hη hθ := by
    change whiskerLeft (B := B) h η ≫ whiskerRight (B := B) θ g =
      koszulSign p q • (whiskerRight (B := B) θ f ≫ whiskerLeft (B := B) i η)
    rw [super_interchange (R := R) (B := B) hθ hη, koszulSign_smul (R := R),
      koszulSign_smul (R := R), mul_comm q p, sign_smul_sign_smul]
  associator_hom_mem f g h := inv_mem _ (associator_hom_mem (R := R) (B := B) h g f)
  leftUnitor_hom_mem f := rightUnitor_hom_mem (R := R) (B := B) f
  rightUnitor_hom_mem f := leftUnitor_hom_mem (R := R) (B := B) f

/-- The homogeneous horizontal composition is reversed with the Koszul sign,
as in the definition preceding Lemma 9.6. -/
theorem hcomp_eq {a b c : TwoSRev R B} {f g : a ⟶ b} {h i : b ⟶ c}
    {p q : ZMod 2} {η : f ⟶ g} {θ : h ⟶ i}
    (hη : η ∈ parity (R := R) f g p) (hθ : θ ∈ parity (R := R) h i q) :
    TwoSupercategory.hcomp (B := TwoSRev R B) η θ =
      sign R (p * q) • TwoSupercategory.hcomp (B := B) θ η := by
  change whiskerLeft (B := B) h η ≫ whiskerRight (B := B) θ g =
    sign R (p * q) • (whiskerRight (B := B) θ f ≫ whiskerLeft (B := B) i η)
  rw [super_interchange (R := R) (B := B) hθ hη, koszulSign_smul (R := R),
    mul_comm q p, sign_smul_sign_smul]

section Graded
variable [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R B]

instance (a b : TwoSRev R B) : GradedSupercategory R (a ⟶ b) :=
  inferInstanceAs (GradedSupercategory R (b.unrev ⟶ a.unrev))

instance gradedTwoSupercategory : GradedTwoSupercategory R (TwoSRev R B) where
  whiskerLeft_mem_degree f _ _ _ _ hη := GradedTwoSupercategory.whiskerRight_mem_degree (B := B) f hη
  whiskerRight_mem_degree h hη := GradedTwoSupercategory.whiskerLeft_mem_degree (B := B) h hη
  associator_hom_mem_degree f g h := GradedTwoSupercategory.associator_inv_mem_degree (B := B) h g f
  leftUnitor_hom_mem_degree f := GradedTwoSupercategory.rightUnitor_hom_mem_degree (B := B) f
  rightUnitor_hom_mem_degree f := GradedTwoSupercategory.leftUnitor_hom_mem_degree (B := B) f

/-- The structure maps preceding Lemma 9.6 are retained, not inverted;
in particular the two integer shift objects are not exchanged. -/
instance qpiTwoSupercategory [QPiTwoSupercategory R B] :
    QPiTwoSupercategory R (TwoSRev R B) where
  pi a := PiTwoSupercategory.pi (B := B) (R := R) a.unrev
  ζ a := PiTwoSupercategory.ζ (B := B) (R := R) a.unrev
  ζ_hom_mem a := PiTwoSupercategory.ζ_hom_mem (B := B) a.unrev
  ζ_hom_mem_degree a := QPiTwoSupercategory.ζ_hom_mem_degree (B := B) a.unrev
  q a := QPiTwoSupercategory.q (B := B) (R := R) a.unrev
  qinv a := QPiTwoSupercategory.qinv (B := B) (R := R) a.unrev
  σ a := QPiTwoSupercategory.σ (B := B) (R := R) a.unrev
  σbar a := QPiTwoSupercategory.σbar (B := B) (R := R) a.unrev
  σ_hom_mem a := QPiTwoSupercategory.σ_hom_mem (B := B) a.unrev
  σ_hom_mem_degree a := QPiTwoSupercategory.σ_hom_mem_degree (B := B) a.unrev
  σbar_hom_mem a := QPiTwoSupercategory.σbar_hom_mem (B := B) a.unrev
  σbar_hom_mem_degree a := QPiTwoSupercategory.σbar_hom_mem_degree (B := B) a.unrev
end Graded
end TwoSRev

section Extension
variable {R : Type r} [CommRing R]
  {A : Type u} [BicategoryStruct.{w, v} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A]
  [∀ a b : A, GradedSupercategory R (a ⟶ b)]
  {B : Type u'} [BicategoryStruct.{w', v'} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R B]

/-- **Lemma 9.6.** Extend an arbitrary functor into the super-reverse of the
already-shifted target; no factorization through an unshifted target is required. -/
def extendEnvelopeSRev (F : TwoSuperfunctor R A (TwoSRev R (QPiTwoEnvelope R B))) :
    TwoSuperfunctor R (QPiTwoEnvelope R A) (TwoSRev R (QPiTwoEnvelope R B)) :=
  QPiTwoEnvelope.extendQPi F

omit [∀ a b : A, GradedSupercategory R (a ⟶ b)] in
/-- Agreement on 2-morphisms with no added shifts. -/
theorem extendEnvelopeSRev_map₂_J
    (F : TwoSuperfunctor R A (TwoSRev R (QPiTwoEnvelope R B)))
    {a b : A} {f g : a ⟶ b} (η : f ⟶ g) :
    (extendEnvelopeSRev F).map₂ (QPiTwoEnvelope.J2 (R := R) η) = F.map₂ η :=
  QPiTwoEnvelope.extendQPi_map₂_J F η

omit [∀ a b : A, GradedSupercategory R (a ⟶ b)] in
/-- The original composition comparison is recovered on the unshifted source. -/
theorem extendEnvelopeSRev_mapComp_J
    (F : TwoSuperfunctor R A (TwoSRev R (QPiTwoEnvelope R B)))
    {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    ((extendEnvelopeSRev F).mapComp (QPiTwoEnvelope.Jm (R := R) f)
      (QPiTwoEnvelope.Jm g)).hom = (F.mapComp f g).hom :=
  letI : ∀ a b : TwoSRev R (QPiTwoEnvelope R B), QPiSupercategory R (a ⟶ b) :=
    fun a b => QPiTwoSupercategory.homQPiLeft a b
  QPiTwoEnvelope.extendComp_J F f g

omit [∀ a b : A, GradedSupercategory R (a ⟶ b)] in
/-- The extension retains the entire unit comparison isomorphism. -/
theorem extendEnvelopeSRev_mapId
    (F : TwoSuperfunctor R A (TwoSRev R (QPiTwoEnvelope R B)))
    (a : QPiTwoEnvelope R A) : (extendEnvelopeSRev F).mapId a = F.mapId a.as.as := rfl

omit [∀ a b : A, GradedSupercategory R (a ⟶ b)] in
/-- Restriction recovers the original functor, including both comparison isomorphisms. -/
theorem twoJ_comp_extendEnvelopeSRev
    (F : TwoSuperfunctor R A (TwoSRev R (QPiTwoEnvelope R B))) :
    (QPiTwoEnvelope.twoJ R A).comp (extendEnvelopeSRev F) = F :=
  QPiTwoEnvelope.twoJ_comp_extendQPi F

/-- The extension in Lemma 9.6 preserves integer degrees, including those of its comparisons. -/
theorem extendEnvelopeSRev_isGraded
    (F : TwoSuperfunctor R A (TwoSRev R (QPiTwoEnvelope R B))) (hF : F.IsGraded) :
    (extendEnvelopeSRev F).IsGraded :=
  QPiTwoEnvelope.extendQPi_isGraded F hF

/-- **Lemma 9.6**, with gradedness and agreement on restriction. -/
theorem exists_graded_envelopeSRev_extension
    (F : TwoSuperfunctor R A (TwoSRev R (QPiTwoEnvelope R B))) (hF : F.IsGraded) :
    ∃ G : TwoSuperfunctor R (QPiTwoEnvelope R A) (TwoSRev R (QPiTwoEnvelope R B)),
      G.IsGraded ∧ (QPiTwoEnvelope.twoJ R A).comp G = F :=
  ⟨extendEnvelopeSRev F, extendEnvelopeSRev_isGraded F hF,
    twoJ_comp_extendEnvelopeSRev F⟩
end Extension
end OddMath.SKM
