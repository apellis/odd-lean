import Mathlib.LinearAlgebra.Quotient.Bilinear
import StringDiagrams.Super.GSBim
import StringDiagrams.Super.GSCat
import OddMath.QuiverHecke.CyclotomicAction.PrefixScalarRelations.ScalarSpecializationFunctor
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading

/-!
# Truncated append

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The coefficient-truncated ELV category

Words carry the quotient Hom modules `TruncatedOld`. Composition descends through
both two-sided ideals. The integer grading and super parity are independent.
No monoidal structure is asserted: prepending need not preserve the first-position
cyclotomic relation.
-/

noncomputable section
open CategoryTheory StringDiagrams GradedSupercategory
namespace OddMath.QuiverHecke.ELV
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

/-- Ordinary endomorphisms: multiplication is reverse categorical composition. -/
abbrev TruncatedEnd (v : List I) := End (⟨v⟩ : TruncatedCategory D Sc cutoff N)

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

end OddMath.QuiverHecke.ELV
end

end

section

/-! # Right append on the coefficient-truncated ELV category

Right contexts preserve both the first-position cyclotomic ideal and the
coefficient weight ideal. The resulting functors use the original signed
coefficient composition; no left-context stability is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

@[simp] theorem rightContext_id (σ v : List I) :
    rightContext D Sc cutoff σ v v (𝟙 (obj D Sc cutoff v)) =
      𝟙 (obj D Sc cutoff (v ++ σ)) := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    ((𝟙 ((pres D Sc).obj (ob D v))) ▷ (pres D Sc).obj (ob D σ)) = _
  rw [MonoidalSupercategory.id_whiskerRight (R := k)]
  rfl

@[simp] theorem rightContext_coefficientIdentity (σ t : List I) (a : SKM.SYM D k) :
    rightContext D Sc cutoff σ t t (coefficientIdentity D Sc cutoff t a) =
      coefficientIdentity D Sc cutoff (t ++ σ) a := by
  change SKM.SYM.elvCoefficientQuotient D cutoff a ⊗ₜ[k]
    ((𝟙 ((pres D Sc).obj (ob D t))) ▷ (pres D Sc).obj (ob D σ)) = _
  rw [MonoidalSupercategory.id_whiskerRight (R := k)]
  rfl

/-- Coefficient weights do not change when spectator strands are appended. -/
theorem coefficientHomIdeal_rightContext (N : ℕ) (σ : List I)
    {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ coefficientHomIdeal D Sc cutoff N v w) :
    rightContext D Sc cutoff σ v w f ∈
      coefficientHomIdeal D Sc cutoff N (v ++ σ) (w ++ σ) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨t, a, ha, l, r, rfl⟩ := hf
    rw [rightContext_comp, rightContext_comp, rightContext_coefficientIdentity]
    exact Submodule.subset_span ⟨t ++ σ, a, ha,
      rightContext D Sc cutoff σ v t l, rightContext D Sc cutoff σ t w r, rfl⟩
  | zero => simpa only [map_zero] using
      (coefficientHomIdeal D Sc cutoff N (v ++ σ) (w ++ σ)).zero_mem
  | add f g _ _ hf hg => simpa only [map_add] using Submodule.add_mem _ hf hg
  | smul c f _ hf => simpa only [map_smul] using Submodule.smul_mem _ c hf

theorem truncatedIdeal_rightContext (N : ℕ) (σ : List I)
    {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ truncatedIdeal D Sc cutoff N v w) :
    rightContext D Sc cutoff σ v w f ∈
      truncatedIdeal D Sc cutoff N (v ++ σ) (w ++ σ) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨_, ideal_rightContext D Sc cutoff σ ha,
    _, coefficientHomIdeal_rightContext D Sc cutoff N σ hb, rfl⟩

variable (N : ℕ)

/-- Right extension on the two-ideal quotient. -/
def truncatedRightContext (σ v w : List I) :
    TruncatedOld D Sc cutoff N v w →ₗ[k]
      TruncatedOld D Sc cutoff N (v ++ σ) (w ++ σ) :=
  (truncatedIdeal D Sc cutoff N v w).mapQ
    (truncatedIdeal D Sc cutoff N (v ++ σ) (w ++ σ))
    (rightContext D Sc cutoff σ v w)
    (fun _ hf => truncatedIdeal_rightContext D Sc cutoff N σ hf)

@[simp] theorem truncatedRightContext_mk (σ v w : List I) (f : hom D Sc cutoff v w) :
    truncatedRightContext D Sc cutoff N σ v w
      ((truncatedIdeal D Sc cutoff N v w).mkQ f) =
      (truncatedIdeal D Sc cutoff N (v ++ σ) (w ++ σ)).mkQ
        (rightContext D Sc cutoff σ v w f) := rfl

/-- Append an arbitrary word, without changing coefficients or their cutoff. -/
def truncatedAppend (σ : List I) :
    TruncatedCategory D Sc cutoff N ⥤ TruncatedCategory D Sc cutoff N where
  obj v := ⟨v.word ++ σ⟩
  map {v w} := truncatedRightContext D Sc cutoff N σ v.word w.word
  map_id v := congrArg (truncatedIdeal D Sc cutoff N _ _).mkQ
    (rightContext_id D Sc cutoff σ v.word)
  map_comp {v w z} f g := by
    obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word w.word).mkQ_surjective f
    obtain ⟨g, rfl⟩ := (truncatedIdeal D Sc cutoff N w.word z.word).mkQ_surjective g
    exact congrArg (truncatedIdeal D Sc cutoff N _ _).mkQ
      (rightContext_comp D Sc cutoff σ f g)

instance truncatedAppend_additive (σ : List I) :
    (truncatedAppend D Sc cutoff N σ).Additive where
  map_add := map_add (truncatedRightContext D Sc cutoff N σ _ _) _ _

instance truncatedAppend_linear (σ : List I) :
    Functor.Linear k (truncatedAppend D Sc cutoff N σ) where
  map_smul f c := map_smul (truncatedRightContext D Sc cutoff N σ _ _) c f

theorem rightContext_proj (σ : List I) {v w : List I} (p : ZMod 2)
    (f : hom D Sc cutoff v w) :
    rightContext D Sc cutoff σ v w (Supercategory.proj k p f) =
      Supercategory.proj k p (rightContext D Sc cutoff σ v w f) := by
  induction f using BoxProd.induction_on_homogeneous with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | tmul q r a f ha hf =>
    have hs := BoxProd.tmul_mem_parity ha hf
    have ht := BoxProd.tmul_mem_parity (X := obj D Sc cutoff (v ++ σ))
      (Y := obj D Sc cutoff (w ++ σ)) ha
      (MonoidalSupercategory.whiskerRight_mem ((pres D Sc).obj (ob D σ)) hf)
    by_cases h : q + r = p
    · subst p
      rw [Supercategory.proj_of_mem hs]
      exact (Supercategory.proj_of_mem ht).symm
    · rw [Supercategory.proj_of_mem_ne hs h, map_zero]
      exact (Supercategory.proj_of_mem_ne ht h).symm

theorem rightContext_mem_parity (σ : List I) {v w : List I} {p : ZMod 2}
    {f : hom D Sc cutoff v w}
    (hf : f ∈ Supercategory.parity (R := k) (obj D Sc cutoff v) (obj D Sc cutoff w) p) :
    rightContext D Sc cutoff σ v w f ∈ Supercategory.parity (R := k)
      (obj D Sc cutoff (v ++ σ)) (obj D Sc cutoff (w ++ σ)) p := by
  apply Supercategory.mem_iff_proj.mpr
  rw [← rightContext_proj, Supercategory.proj_of_mem hf]

instance truncatedAppend_super (σ : List I) :
    IsSuperfunctor k (truncatedAppend D Sc cutoff N σ) where
  map_mem := by
    rintro v w p f ⟨a, ha, rfl⟩
    exact Submodule.mem_map_of_mem (rightContext_mem_parity D Sc cutoff σ ha)

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

theorem rightContext_mem_degree (σ : List I) {v w : List I} {n : ℤ}
    {f : hom D Sc cutoff v w} (hf : f ∈ elvHomDegree D sy Sc hc cutoff v w n) :
    rightContext D Sc cutoff σ v w f ∈
      elvHomDegree D sy Sc hc cutoff (v ++ σ) (w ++ σ) n := by
  let _ := elvCoefficientCategoryGrading (k := k) D sy cutoff
  let _ := gradedSupercategory D sy Sc hc
  let _ := gradedMonoidalSupercategory D sy Sc hc
  refine BoxProd.map_mem_of_homDeg (X := obj D Sc cutoff v)
    (Y := obj D Sc cutoff w) (rightContext D Sc cutoff σ v w) _ ?_ hf
  intro r s hrs a ha g hg
  subst n
  exact BoxProd.tmulHom_mem_degree (X := obj D Sc cutoff (v ++ σ))
    (Y := obj D Sc cutoff (w ++ σ)) ha
    (GradedMonoidalSupercategory.whiskerRight_mem_degree ((pres D Sc).obj (ob D σ)) hg)

end OddMath.QuiverHecke.ELV
end

end
