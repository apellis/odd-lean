/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientTruncation
import Mathlib.LinearAlgebra.Quotient.Bilinear
import StringDiagrams.Super.GSBim

/-! # The coefficient-truncated ELV category

Words carry the quotient Hom modules `TruncatedOld`. Composition descends through
both two-sided ideals. The integer grading and super parity are independent.
No monoidal structure is asserted: prepending need not preserve the first-position
cyclotomic relation.
-/

noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Words in the coefficient-truncated old ELV category. -/
structure TruncatedCategory (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
    (cutoff : I → ℕ) (N : ℕ) where
  word : List I

/-- Quotient composition, in categorical order. -/
def truncatedComp (v t w : List I) :
    TruncatedOld D Sc cutoff N v t →ₗ[k]
      TruncatedOld D Sc cutoff N t w →ₗ[k] TruncatedOld D Sc cutoff N v w :=
  LinearMap.liftQ₂ _ _
    ({ toFun := fun f =>
        { toFun := fun g => (truncatedIdeal D Sc cutoff N v w).mkQ (f ≫ g)
          map_add' := by intros; simp only [Preadditive.comp_add, map_add]
          map_smul' := by intros; simp only [Linear.comp_smul, map_smul, RingHom.id_apply] }
       map_add' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk, Preadditive.add_comp, map_add, LinearMap.add_apply]
       map_smul' := by intros; ext g; simp only [LinearMap.coe_mk, AddHom.coe_mk, Linear.smul_comp, map_smul, LinearMap.smul_apply, RingHom.id_apply] } :
       hom D Sc cutoff v t →ₗ[k] hom D Sc cutoff t w →ₗ[k] TruncatedOld D Sc cutoff N v w)
    (by
      intro f hf
      ext g
      exact (Submodule.Quotient.mk_eq_zero _).mpr (truncatedIdeal_comp D Sc cutoff N hf g))
    (by
      intro g hg
      ext f
      exact (Submodule.Quotient.mk_eq_zero _).mpr (comp_truncatedIdeal D Sc cutoff N f hg))

@[simp] theorem truncatedComp_mk (v t w : List I)
    (f : hom D Sc cutoff v t) (g : hom D Sc cutoff t w) :
    truncatedComp D Sc cutoff N v t w
      ((truncatedIdeal D Sc cutoff N v t).mkQ f)
      ((truncatedIdeal D Sc cutoff N t w).mkQ g) =
      (truncatedIdeal D Sc cutoff N v w).mkQ (f ≫ g) := rfl

instance truncatedCategory : Category (TruncatedCategory D Sc cutoff N) where
  Hom v w := TruncatedOld D Sc cutoff N v.word w.word
  id v := (truncatedIdeal D Sc cutoff N v.word v.word).mkQ (𝟙 _)
  comp {v t w} f g := truncatedComp D Sc cutoff N v.word t.word w.word f g
  id_comp := by
    intro v w f
    obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word w.word).mkQ_surjective f
    exact congrArg (truncatedIdeal D Sc cutoff N v.word w.word).mkQ (Category.id_comp f)
  comp_id := by
    intro v w f
    obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word w.word).mkQ_surjective f
    exact congrArg (truncatedIdeal D Sc cutoff N v.word w.word).mkQ (Category.comp_id f)
  assoc := by
    intro v t w z f g h
    obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word t.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (truncatedIdeal D Sc cutoff N t.word w.word).mkQ_surjective g
    obtain ⟨h, rfl⟩ := (truncatedIdeal D Sc cutoff N w.word z.word).mkQ_surjective h
    exact congrArg (truncatedIdeal D Sc cutoff N v.word z.word).mkQ (Category.assoc f g h)

instance truncatedPreadditive : Preadditive (TruncatedCategory D Sc cutoff N) where
  homGroup v w := inferInstanceAs (AddCommGroup (TruncatedOld D Sc cutoff N v.word w.word))
  add_comp := by
    intro v t w f g h
    exact LinearMap.map_add₂ (truncatedComp D Sc cutoff N v.word t.word w.word) f g h
  comp_add := by
    intro v t w f g h
    exact (truncatedComp D Sc cutoff N v.word t.word w.word f).map_add g h

instance truncatedLinear : Linear k (TruncatedCategory D Sc cutoff N) where
  homModule v w := inferInstanceAs (Module k (TruncatedOld D Sc cutoff N v.word w.word))
  smul_comp := by
    intro v t w r f g
    exact LinearMap.map_smul₂ (truncatedComp D Sc cutoff N v.word t.word w.word) r f g
  comp_smul := by
    intro v t w f r g
    exact (truncatedComp D Sc cutoff N v.word t.word w.word f).map_smul r g

instance truncatedSupercategory : Supercategory k (TruncatedCategory D Sc cutoff N) where
  parity v w := truncatedParity D Sc cutoff N v.word w.word
  isInternal v w := truncatedParity_internal D Sc cutoff N v.word w.word
  id_mem v := Submodule.mem_map_of_mem (Supercategory.id_mem (obj D Sc cutoff v.word))
  comp_mem := by
    rintro v t w p q f g ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact Submodule.mem_map_of_mem (Supercategory.comp_mem ha hb)

/-- The categorical projection agrees with the descended quotient projection. -/
theorem truncatedCategory_proj (v w : TruncatedCategory D Sc cutoff N)
    (p : ZMod 2) (f : v ⟶ w) :
    Supercategory.proj k p f = truncatedProj D Sc cutoff N v.word w.word p f := by
  refine Supercategory.induction_on (R := k) f (by simp) (fun q f hf => ?_)
    (fun f g hf hg => by simp only [map_add, hf, hg])
  ·
    rw [truncatedProj_of_mem D Sc cutoff N hf p]
    by_cases h : q = p
    · subst q
      rw [ite_eq_left rfl, Supercategory.proj_of_mem hf]
    · rw [ite_eq_right h, Supercategory.proj_of_mem_ne hf h]

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

@[instance_reducible]
def truncatedGradedSupercategory :
    GradedSupercategory k (TruncatedCategory D Sc cutoff N) where
  degree v w := truncatedDegree D Sc cutoff sy hc N v.word w.word
  isInternal_degree v w := truncatedDegree_internal D Sc cutoff sy hc N v.word w.word
  proj_mem_degree := by
    intro v w n f p hf
    rw [truncatedCategory_proj]
    obtain ⟨a, ha, rfl⟩ := hf
    rw [truncatedProj_mk]
    let _ := elvHomGrading D sy Sc hc cutoff
    exact Submodule.mem_map_of_mem (GradedSupercategory.proj_mem_degree p ha)
  id_mem_degree v := by
    let _ := elvHomGrading D sy Sc hc cutoff
    exact Submodule.mem_map_of_mem (GradedSupercategory.id_mem_degree (obj D Sc cutoff v.word))
  comp_mem_degree := by
    rintro v t w m n f g ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    let _ := elvHomGrading D sy Sc hc cutoff
    exact Submodule.mem_map_of_mem (GradedSupercategory.comp_mem_degree ha hb)

/-- Integer projections are the established quotient projections. -/
theorem truncatedCategory_dproj (v w : TruncatedCategory D Sc cutoff N)
    (n : ℤ) (f : v ⟶ w) :
    letI := truncatedGradedSupercategory D Sc cutoff N sy hc
    dproj k n f = truncatedDproj D Sc cutoff sy hc N v.word w.word n f := by
  let _ := truncatedGradedSupercategory D Sc cutoff N sy hc
  refine induction_on_degree (R := k) f (by simp) (fun m f hf => ?_)
    (fun f g hf hg => by simp only [map_add, hf, hg])
  rw [truncatedDproj_of_mem D Sc cutoff sy hc N hf n]
  by_cases h : m = n
  · subst m
    rw [ite_eq_left rfl, dproj_of_mem hf]
  · rw [ite_eq_right h, dproj_of_mem_ne hf h]

/-- Ordinary endomorphisms: multiplication is reverse categorical composition. -/
abbrev TruncatedEnd (v : List I) := End (⟨v⟩ : TruncatedCategory D Sc cutoff N)

/-- Multiplication retains the ordinary endomorphism convention, with no extra sign. -/
theorem truncatedEnd_mul (v : List I) (f g : TruncatedEnd D Sc cutoff N v) :
    f * g = truncatedComp D Sc cutoff N v v v g f := rfl

/-- Parity parts of the endomorphism ring. -/
def truncatedEndParity (v : List I) : ZMod 2 → Submodule k (TruncatedEnd D Sc cutoff N v) :=
  truncatedParity D Sc cutoff N v v

/-- Integer degree parts of the endomorphism ring. -/
def truncatedEndDegree (v : List I) : ℤ → Submodule k (TruncatedEnd D Sc cutoff N v) :=
  truncatedDegree D Sc cutoff sy hc N v v

instance truncatedEndParityMonoid (v : List I) :
    SetLike.GradedMonoid (truncatedEndParity D Sc cutoff N v) where
  one_mem := Supercategory.id_mem (⟨v⟩ : TruncatedCategory D Sc cutoff N)
  mul_mem p q f g hf hg := by
    change g ≫ f ∈ truncatedParity D Sc cutoff N v v (p + q)
    rw [add_comm]
    exact Supercategory.comp_mem (R := k)
      (X := (⟨v⟩ : TruncatedCategory D Sc cutoff N)) (Y := ⟨v⟩) (Z := ⟨v⟩) hg hf

instance truncatedEndParityGrading (v : List I) :
    GradedAlgebra (truncatedEndParity D Sc cutoff N v) :=
  { (truncatedParity_internal D Sc cutoff N v v).chooseDecomposition with }

instance truncatedEndDegreeMonoid (v : List I) :
    SetLike.GradedMonoid (truncatedEndDegree D Sc cutoff N sy hc v) where
  one_mem := by
    let _ := truncatedGradedSupercategory D Sc cutoff N sy hc
    exact GradedSupercategory.id_mem_degree (⟨v⟩ : TruncatedCategory D Sc cutoff N)
  mul_mem p q f g hf hg := by
    let _ := truncatedGradedSupercategory D Sc cutoff N sy hc
    change g ≫ f ∈ truncatedDegree D Sc cutoff sy hc N v v (p + q)
    rw [add_comm]
    exact GradedSupercategory.comp_mem_degree (R := k)
      (X := (⟨v⟩ : TruncatedCategory D Sc cutoff N)) (Y := ⟨v⟩) (Z := ⟨v⟩) hg hf

instance truncatedEndDegreeGrading (v : List I) :
    GradedAlgebra (truncatedEndDegree D Sc cutoff N sy hc v) :=
  { (truncatedDegree_internal D Sc cutoff sy hc N v v).chooseDecomposition with }

/-- The endomorphism graded superalgebra of a word in the truncated ELV category. -/
def truncatedEndGSuperAlg (v : List I) : GSuperAlg k where
  carrier := TruncatedEnd D Sc cutoff N v
  grading := truncatedEndParity D Sc cutoff N v
  degree := truncatedEndDegree D Sc cutoff N sy hc v
  decompose_mem := by
    intro n a p ha
    let _ := truncatedGradedSupercategory D Sc cutoff N sy hc
    exact GradedSupercategory.proj_mem_degree (R := k)
      (X := (⟨v⟩ : TruncatedCategory D Sc cutoff N)) (Y := ⟨v⟩) p ha

end OddMath.QuiverHecke.ELVOld
