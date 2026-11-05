import OddMath.QuiverHecke.CyclotomicAction.ELVProbeScalarHomDescent
import Mathlib.LinearAlgebra.Quotient.Bilinear

/-! # The literal ordinary probe content category
Homs are the existing ordinary cycHom quotients. Canonical scalar
specialization is full, and actual scalar-evaluated old modules descend
through it with their original arrow action.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (a : I → Polynomial k)

/-- Fixed-content words with the existing ordinary cyclotomic Hom quotients. -/
structure OrdinaryContentCategory (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (a : I → Polynomial k) (ν : List I) where
  word : List I
  wordPerm : word.Perm ν

def ordinaryContentComp (v t w : List I) :
    (((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t)) ⧸ cycHom D Sc a v t) →ₗ[k]
    (((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D w)) ⧸ cycHom D Sc a t w) →ₗ[k]
    (((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) ⧸ cycHom D Sc a v w) :=
  LinearMap.liftQ₂ _ _
    ({ toFun := fun f =>
        { toFun := fun g => (cycHom D Sc a v w).mkQ (f ≫ g)
          map_add' := by intros; simp only [Preadditive.comp_add, map_add]
          map_smul' := by intros; simp only [Linear.comp_smul, map_smul, RingHom.id_apply] }
       map_add' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk,
         Preadditive.add_comp, map_add, LinearMap.add_apply]
       map_smul' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk,
         Linear.smul_comp, map_smul, LinearMap.smul_apply, RingHom.id_apply] } :
      ((pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t)) →ₗ[k]
      ((pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D w)) →ₗ[k] _)
    (by
      intro f hf
      ext g
      exact (Submodule.Quotient.mk_eq_zero _).mpr (cycHom_comp_right D Sc hf g))
    (by
      intro g hg
      ext f
      exact (Submodule.Quotient.mk_eq_zero _).mpr (cycHom_comp_left D Sc f hg))

@[simp] theorem ordinaryContentComp_mk (v t w : List I)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D t))
    (g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D w)) :
    ordinaryContentComp D Sc a v t w ((cycHom D Sc a v t).mkQ f) ((cycHom D Sc a t w).mkQ g) =
      (cycHom D Sc a v w).mkQ (f ≫ g) := rfl

instance ordinaryContentCategory (ν : List I) : Category (OrdinaryContentCategory D Sc a ν) where
  Hom v w := ((pres D Sc).obj (ob D v.word) ⟶ (pres D Sc).obj (ob D w.word)) ⧸ cycHom D Sc a v.word w.word
  id v := (cycHom D Sc a v.word v.word).mkQ (𝟙 _)
  comp {v t w} f g := ordinaryContentComp D Sc a v.word t.word w.word f g
  id_comp := by
    intro v w f
    obtain ⟨f,rfl⟩ := (cycHom D Sc a v.word w.word).mkQ_surjective f
    exact congrArg (cycHom D Sc a v.word w.word).mkQ (Category.id_comp f)
  comp_id := by
    intro v w f
    obtain ⟨f,rfl⟩ := (cycHom D Sc a v.word w.word).mkQ_surjective f
    exact congrArg (cycHom D Sc a v.word w.word).mkQ (Category.comp_id f)
  assoc := by
    intro v t w z f g h
    obtain ⟨f,rfl⟩ := (cycHom D Sc a v.word t.word).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (cycHom D Sc a t.word w.word).mkQ_surjective g
    obtain ⟨h,rfl⟩ := (cycHom D Sc a w.word z.word).mkQ_surjective h
    exact congrArg (cycHom D Sc a v.word z.word).mkQ (Category.assoc f g h)

instance ordinaryContentPreadditive (ν : List I) : Preadditive (OrdinaryContentCategory D Sc a ν) where
  homGroup v w := inferInstanceAs (AddCommGroup (((pres D Sc).obj (ob D v.word) ⟶
    (pres D Sc).obj (ob D w.word)) ⧸ cycHom D Sc a v.word w.word))
  add_comp := by intro v w z f g h; exact LinearMap.map_add₂ (ordinaryContentComp D Sc a v.word w.word z.word) f g h
  comp_add := by intro v w z f g h; exact (ordinaryContentComp D Sc a v.word w.word z.word f).map_add g h

instance ordinaryContentLinear (ν : List I) : Linear k (OrdinaryContentCategory D Sc a ν) where
  homModule v w := inferInstanceAs (Module k (((pres D Sc).obj (ob D v.word) ⟶
    (pres D Sc).obj (ob D w.word)) ⧸ cycHom D Sc a v.word w.word))
  smul_comp := by intro v w z r f g; exact LinearMap.map_smul₂ (ordinaryContentComp D Sc a v.word w.word z.word) r f g
  comp_smul := by intro v w z f r g; exact (ordinaryContentComp D Sc a v.word w.word z.word f).map_smul r g

variable (m : I → ℕ) (ν : List I)
local notation "cut" => probeCutoff D m
local notation "probe" => probePolynomial (k := k) (probeDotExponent D) m
local notation "C" => ELVOld.OldContentCategory D Sc cut ν
local notation "Q" => OrdinaryContentCategory D Sc probe ν

/-- Actual scalar specialization, on the literal ordinary quotient category. -/
def probeOldOrdinaryFunctor : C ⥤ Q where
  obj v := ⟨v.obj.word,v.wordPerm⟩
  map {v w} := elvProbeOldHom D m Sc v.obj.word w.obj.word
  map_id v := by
    change (cycHom D Sc probe v.obj.word v.obj.word).mkQ
      (elvProbeScalarHom D m Sc v.obj.word v.obj.word (𝟙 (ELVOld.obj D Sc cut v.obj.word))) = _
    rw [elvProbeScalarHom_id]
    rfl
  map_comp {v t w} f g := by
    obtain ⟨f,rfl⟩ := (ELVOld.ideal D Sc cut v.obj.word t.obj.word).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (ELVOld.ideal D Sc cut t.obj.word w.obj.word).mkQ_surjective g
    change (cycHom D Sc probe v.obj.word w.obj.word).mkQ
      (elvProbeScalarHom D m Sc v.obj.word w.obj.word (f ≫ g)) =
      ordinaryContentComp D Sc probe v.obj.word t.obj.word w.obj.word
        ((cycHom D Sc probe v.obj.word t.obj.word).mkQ (elvProbeScalarHom D m Sc _ _ f))
        ((cycHom D Sc probe t.obj.word w.obj.word).mkQ (elvProbeScalarHom D m Sc _ _ g))
    rw [ordinaryContentComp_mk, elvProbeScalarHom_comp]

instance : (probeOldOrdinaryFunctor D Sc m ν).Full where
  map_surjective {v w} f := elvProbeOldHom_surjective D m Sc v.obj.word w.obj.word f
instance : (probeOldOrdinaryFunctor D Sc m ν).Additive where
  map_add {v w} f g := (elvProbeOldHom D m Sc v.obj.word w.obj.word).map_add f g
instance : (probeOldOrdinaryFunctor D Sc m ν).Linear k where
  map_smul {v w} f r := (elvProbeOldHom D m Sc v.obj.word w.obj.word).map_smul r f

/-- The same actual word, viewed in the source old content category. -/
def probeOrdinaryOldObject (v : Q) : C := ⟨⟨v.word⟩,v.wordPerm⟩

variable
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N)

/-- The actual descended ordinary module on precisely the original old module values. -/
def probeOrdinaryModuleFunctor : Q ⥤ SVec k where
  obj v := N.obj (probeOrdinaryOldObject D Sc m ν v)
  map {v w} := probeOrdinaryModuleHom D m Sc ν N hN
    (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν w)
  map_id v := by
    change probeOldModuleRawAction D m Sc ν N
      (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν v)
      (ELVOld.affineUnit D Sc cut v.word v.word (𝟙 _)) = _
    rw [ELVOld.affineUnit_id]
    exact N.toFunctor.map_id _
  map_comp {v t w} f g := by
    obtain ⟨f,rfl⟩ := (cycHom D Sc probe v.word t.word).mkQ_surjective f
    obtain ⟨g,rfl⟩ := (cycHom D Sc probe t.word w.word).mkQ_surjective g
    change probeOldModuleRawAction D m Sc ν N
      (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν w)
      (ELVOld.affineUnit D Sc cut v.word w.word (f ≫ g)) =
      probeOldModuleRawAction D m Sc ν N
        (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν t)
        (ELVOld.affineUnit D Sc cut v.word t.word f) ≫
      probeOldModuleRawAction D m Sc ν N
        (probeOrdinaryOldObject D Sc m ν t) (probeOrdinaryOldObject D Sc m ν w)
        (ELVOld.affineUnit D Sc cut t.word w.word g)
    rw [ELVOld.affineUnit_comp]
    exact N.toFunctor.map_comp
      (show probeOrdinaryOldObject D Sc m ν v ⟶ probeOrdinaryOldObject D Sc m ν t from
        (ELVOld.ideal D Sc cut v.word t.word).mkQ (ELVOld.affineUnit D Sc cut v.word t.word f))
      (show probeOrdinaryOldObject D Sc m ν t ⟶ probeOrdinaryOldObject D Sc m ν w from
        (ELVOld.ideal D Sc cut t.word w.word).mkQ (ELVOld.affineUnit D Sc cut t.word w.word g))

instance : (probeOrdinaryModuleFunctor D Sc m ν N hN).Additive where
  map_add {v w} f g := (probeOrdinaryModuleHom D m Sc ν N hN
    (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν w)).map_add f g
instance : (probeOrdinaryModuleFunctor D Sc m ν N hN).Linear k where
  map_smul {v w} f r := (probeOrdinaryModuleHom D m Sc ν N hN
    (probeOrdinaryOldObject D Sc m ν v) (probeOrdinaryOldObject D Sc m ν w)).map_smul r f

/-- Restriction along the full scalar functor recovers the existing old module exactly. -/
theorem probeOrdinaryModuleFunctor_restrict :
    probeOldOrdinaryFunctor D Sc m ν ⋙ probeOrdinaryModuleFunctor D Sc m ν N hN = N.toFunctor := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro v
    rfl
  case h_map =>
    intro v w f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact probeOrdinaryModuleHom_old D m Sc ν N hN v w f

end OddMath.QuiverHecke

