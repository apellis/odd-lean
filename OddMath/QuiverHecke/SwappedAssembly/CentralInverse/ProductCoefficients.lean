/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ModuleCoefficients
import OddMath.QuiverHecke.CyclotomicAction.PiWeightSpaces
/-! # Coefficients on content subcategories and their products

For `SwappedHomInversion.md` §4, restrict the regular coefficient realization to full
Π-stable module subcategories, as in `PiWeightSpaces`. Each algebra's explicit upper
support bound supplies its own coefficient ideal. Inverses of fixed finite matrices of
supernatural transformations assemble across arbitrary products; no finite block set or
uniform bound is required. This does not construct ELV algebras, homogeneous closures,
or `CentralInvertible`.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly.RegularReservoir
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
universe u
variable {k : Type u} [CommRing k]

section Restriction
variable {C : Type (u+1)} [Category.{u} C] [Preadditive C] [Linear k C]
  [Supercategory k C] (P : ObjectProperty C)

def restrictCoeff (t : Superfunctor.id k C ⟶ Superfunctor.id k C) :
    Superfunctor.id k P.FullSubcategory ⟶ Superfunctor.id k P.FullSubcategory where
  app p M := ⟨t.app p M.obj⟩
  app_mem p M := t.app_mem p M.obj
  naturality p _M _N _q f hf := InducedCategory.hom_ext (t.naturality p f.hom hf)

theorem restrictCoeff_comp (s t : Superfunctor.id k C ⟶ Superfunctor.id k C) :
    restrictCoeff P (s ≫ t) = restrictCoeff P s ≫ restrictCoeff P t := by
  apply Superfunctor.hom_ext
  intro p M
  rfl

theorem restrictCoeff_mem {p : ZMod 2}
    {t : Superfunctor.id k C ⟶ Superfunctor.id k C}
    (ht : t ∈ parity (R := k) _ _ p) :
    restrictCoeff P t ∈ parity (R := k) _ _ p := by
  rw [Superfunctor.mem_parity_iff] at ht ⊢
  funext M
  apply InducedCategory.hom_ext
  exact congrFun ht M.obj

def restrictCoeffLinear : (Superfunctor.id k C ⟶ Superfunctor.id k C) →ₗ[k]
    (Superfunctor.id k P.FullSubcategory ⟶ Superfunctor.id k P.FullSubcategory) where
  toFun := restrictCoeff P
  map_add' _ _ := by apply Superfunctor.hom_ext; intros; rfl
  map_smul' _ _ := by apply Superfunctor.hom_ext; intros; rfl

theorem restrictCoeff_proj (p : ZMod 2)
    (t : Superfunctor.id k C ⟶ Superfunctor.id k C) :
    restrictCoeff P (proj k p t) = proj k p (restrictCoeff P t) := by
  symm
  apply proj_eq_of_add (h := restrictCoeff P (proj k (p + 1) t))
  · change restrictCoeffLinear P t = restrictCoeffLinear P (proj k p t) +
      restrictCoeffLinear P (proj k (p + 1) t)
    rw [← map_add, proj_add_proj_add_one]
  · exact restrictCoeff_mem P (proj_mem _ _)
  · exact restrictCoeff_mem P (proj_mem _ _)
end Restriction

section FullModules
variable (A : GSuperAlg k) (P : ObjectProperty (Modules A))
  (hP : ∀ M, P M → P ((PiSupercategory.pi (R := k)).obj M))

abbrev fullModuleTarget : PiSCat k :=
  letI := CyclotomicAction.fullPiSupercategory P hP
  PiSCat.of k P.FullSubcategory

def fullRealize (c : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg) :
    𝟙 (fullModuleTarget A P hP) ⟶ 𝟙 (fullModuleTarget A P hP) :=
  restrictCoeff P (realize A c)

theorem fullRealize_total (c : 𝟙 A.toSuperAlg ⟶ 𝟙 A.toSuperAlg)
    (M : P.FullSubcategory) :
    ((fullRealize A P hP c).total M).hom = ProbeWindow.postCoeff M.obj c :=
  realize_total A c M.obj

def fullCoeffGrading : ProbeWindow.CoeffGrading k (fullModuleTarget A P hP) where
  deg n := {t | ∃ c ∈ (coeffGrading A).deg n, fullRealize A P hP c = t}
  id_mem := ⟨_, (coeffGrading A).id_mem, by
    unfold fullRealize
    rw [realize_id]
    apply Superfunctor.hom_ext
    intro p M
    rcases parity_eq_zero_or_one p with rfl | rfl <;> rfl⟩
  comp_mem := by
    rintro m n x y ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    refine ⟨c ≫ d, (coeffGrading A).comp_mem hc hd, ?_⟩
    unfold fullRealize
    rw [realize_comp, restrictCoeff_comp]
  proj_mem := by
    rintro n p x ⟨c, hc, rfl⟩
    refine ⟨proj k p c, (coeffGrading A).proj_mem p hc, ?_⟩
    unfold fullRealize
    rw [realize_proj, restrictCoeff_proj]
    rfl

theorem full_coefficient_eq_zero (K : ℕ)
    (hK : ∀ d : ℤ, (K : ℤ) ≤ d → A.degree d = ⊥)
    (d : ℤ) (hd : (K : ℤ) ≤ d)
    (t : 𝟙 (fullModuleTarget A P hP) ⟶ 𝟙 (fullModuleTarget A P hP))
    (ht : t ∈ (fullCoeffGrading A P hP).deg d) : t = 0 := by
  obtain ⟨c, hc, rfl⟩ := ht
  unfold fullRealize
  rw [realize_eq_zero_of_high_degree A K hK c hc hd]
  exact (restrictCoeffLinear P).map_zero

def fullCoefficientIdeal (T : PiSCat k) (K : ℕ)
    (hK : ∀ d : ℤ, (K : ℤ) ≤ d → A.degree d = ⊥) :
    ProbeWindow.CoefficientIdeal (T ⟶ fullModuleTarget A P hP) :=
  ProbeWindow.reservoirCoefficientIdeal T (fullCoeffGrading A P hP) K
    (full_coefficient_eq_zero A P hP K hK)
end FullModules

section Products
variable {k : Type u} [CommRing k] {B : Type u}
  (C : B → Type (u+1)) [∀ b, Category.{u} (C b)] [∀ b, Preadditive (C b)]
  [∀ b, Linear k (C b)] [∀ b, Supercategory k (C b)]
  (T : Type (u+1)) [Category.{u} T] [Preadditive T] [Linear k T] [Supercategory k T]

def productEvalSF (b : B) : Superfunctor k (∀ b, C b) (C b) :=
  ⟨CategoryTheory.Pi.eval C b⟩

def evalHomFunctor (b : B) :
    Superfunctor k T (∀ b, C b) ⥤ Superfunctor k T (C b) where
  obj F := F.comp (productEvalSF C b)
  map η := Superfunctor.whiskerRight η (productEvalSF C b)
  map_id F := by
    apply Superfunctor.hom_ext
    intro p t
    rcases parity_eq_zero_or_one p with rfl | rfl <;> rfl
  map_comp η θ := by
    apply Superfunctor.hom_ext
    intro p t
    rfl

instance (b : B) : (evalHomFunctor (k := k) C T b).Additive where
  map_add := by
    intros
    apply Superfunctor.hom_ext
    intro p t
    rfl

abbrev evalMat (b : B) := (evalHomFunctor (k := k) C T b).mapMat_

/-- The comparison is entrywise evaluation, without modifying the matrix indexing. -/
theorem evalMat_map_apply (b : B)
    {X Y : Mat_ (Superfunctor k T (∀ b, C b))} (f : X ⟶ Y)
    (i : X.ι) (j : Y.ι) (p : ZMod 2) (t : T) :
    (((evalMat (k := k) C T b).map f) i j).app p t = (f i j).app p t b := rfl

def assemble
    {X Y : Mat_ (Superfunctor k T (∀ b, C b))}
    (g : ∀ b, (evalMat (k := k) C T b).obj X ⟶ (evalMat (k := k) C T b).obj Y) : X ⟶ Y :=
  fun i j =>
    { app := fun p t b => (g b i j).app p t
      app_mem := fun p t b => (g b i j).app_mem p t
      naturality := by
        intro p t t' q f hf
        funext b
        exact (g b i j).naturality p f hf }

theorem eval_assemble
    {X Y : Mat_ (Superfunctor k T (∀ b, C b))}
    (g : ∀ b, (evalMat (k := k) C T b).obj X ⟶ (evalMat (k := k) C T b).obj Y) (b : B) :
    (evalMat (k := k) C T b).map (assemble C T g) = g b := by
  apply Mat_.hom_ext
  intro i j
  apply Superfunctor.hom_ext
  intro p t
  rfl

theorem eval_joint_injective
    {X Y : Mat_ (Superfunctor k T (∀ b, C b))}
    {f g : X ⟶ Y}
    (h : ∀ b, (evalMat (k := k) C T b).map f = (evalMat (k := k) C T b).map g) : f = g := by
  apply Mat_.hom_ext
  intro i j
  apply Superfunctor.hom_ext
  intro p t
  funext b
  exact congrArg (fun z => (z i j).app p t) (h b)

def assembleIso
    {X Y : Mat_ (Superfunctor k T (∀ b, C b))}
    (f : X ⟶ Y)
    (g : ∀ b, (evalMat (k := k) C T b).obj Y ⟶ (evalMat (k := k) C T b).obj X)
    (hfg : ∀ b, (evalMat (k := k) C T b).map f ≫ g b = 𝟙 ((evalMat (k := k) C T b).obj X))
    (hgf : ∀ b, g b ≫ (evalMat (k := k) C T b).map f = 𝟙 ((evalMat (k := k) C T b).obj Y)) : X ≅ Y where
  hom := f
  inv := assemble C T g
  hom_inv_id := by
    apply eval_joint_injective C T
    intro b
    rw [(evalMat (k := k) C T b).map_comp, (evalMat (k := k) C T b).map_id, eval_assemble]
    exact hfg b
  inv_hom_id := by
    apply eval_joint_injective C T
    intro b
    rw [(evalMat (k := k) C T b).map_comp, (evalMat (k := k) C T b).map_id, eval_assemble]
    exact hgf b

theorem isIso_of_eval
    {X Y : Mat_ (Superfunctor k T (∀ b, C b))}
    (f : X ⟶ Y) (hf : ∀ b, IsIso ((evalMat (k := k) C T b).map f)) : IsIso f := by
  let := hf
  exact (assembleIso C T f (fun b => inv ((evalMat (k := k) C T b).map f))
    (fun b => IsIso.hom_inv_id _) (fun b => IsIso.inv_hom_id _)).isIso_hom
end Products

section Bounds
variable {B : Type u} (A : B → GSuperAlg k)
  (P : ∀ b, ObjectProperty (Modules (A b)))
  (hP : ∀ b M, P b M → P b ((PiSupercategory.pi (R := k)).obj M))

/-- The product target uses exactly the full-subcategory and product Π constructions
of `PiWeightSpaces`, without any restriction on the block index. -/
abbrev productModuleTarget : PiSCat k :=
  letI := fun b => CyclotomicAction.fullPiSupercategory (P b) (hP b)
  letI := CyclotomicAction.productPiSupercategory (k := k) (fun b => (P b).FullSubcategory)
  PiSCat.of k (∀ b, (P b).FullSubcategory)

/-- A family of regular coefficients acts componentwise, with both parity components. -/
def productRealize (c : ∀ b, 𝟙 (A b).toSuperAlg ⟶ 𝟙 (A b).toSuperAlg) :
    𝟙 (productModuleTarget A P hP) ⟶ 𝟙 (productModuleTarget A P hP) where
  app p M b := (fullRealize (A b) (P b) (hP b) (c b)).app p (M b)
  app_mem p M b := (fullRealize (A b) (P b) (hP b) (c b)).app_mem p (M b)
  naturality p _M _N _q f hf := by
    funext b
    exact (fullRealize (A b) (P b) (hP b) (c b)).naturality p (f b) (hf b)

/-- Restriction and componentwise realization preserve the parity projections. -/
theorem productRealize_proj (p : ZMod 2)
    (c : ∀ b, 𝟙 (A b).toSuperAlg ⟶ 𝟙 (A b).toSuperAlg) :
    productRealize A P hP (fun b => proj k p (c b)) = proj k p (productRealize A P hP c) := by
  apply Superfunctor.hom_ext
  intro q M
  funext b
  change (restrictCoeff (P b) (realize (A b) (proj k p (c b)))).app q (M b) = _
  rw [realize_proj, restrictCoeff_proj, Superfunctor.proj_app, Superfunctor.proj_app]
  split_ifs <;> rfl

/-- Evaluation retains the balanced tensor action and its unitors. -/
theorem productRealize_total (c : ∀ b, 𝟙 (A b).toSuperAlg ⟶ 𝟙 (A b).toSuperAlg)
    (M : ∀ b, (P b).FullSubcategory) (b : B) :
    ((productRealize A P hP c).total M b).hom = ProbeWindow.postCoeff (M b).obj (c b) :=
  fullRealize_total (A b) (P b) (hP b) (c b) (M b)

/-- Componentwise algebra support gives matrix inversion on the product. Each block has
its own bound `K b`; inverses, not nilpotence exponents, are assembled. The comparison
matrix and the positive-coefficient error retain their original entries under evaluation. -/
theorem isIso_of_component_coefficient_error (T : PiSCat k) (K : B → ℕ)
    (hK : ∀ b d, (K b : ℤ) ≤ d → (A b).degree d = ⊥)
    {X Y : Mat_ (T ⟶ productModuleTarget A P hP)} (F G : X ⟶ Y)
    (hG : ∀ b, IsIso ((evalMat (k := k) (fun b => (P b).FullSubcategory) T b).map G))
    (hFG : ∀ b i j,
      (((evalMat (k := k) (fun b => (P b).FullSubcategory) T b).map F -
        (evalMat (k := k) (fun b => (P b).FullSubcategory) T b).map G) i j) ∈
          ProbeWindow.coeffIdeal (fullCoeffGrading (A b) (P b) (hP b)) 1 _ _) :
    IsIso F := by
  apply isIso_of_eval (fun b => (P b).FullSubcategory) T F
  intro b
  let := hG b
  exact (fullCoefficientIdeal (A b) (P b) (hP b) T (K b) (hK b)).isIso_of_sub_mem _ _
    (fun _ _ => ProbeWindow.mem_coeffIdeal_zero _) (hFG b)
end Bounds

section WeightSpaces
open CyclotomicAction
variable {I : Type u} {W : Type u} [AddCommGroup W] (D : SKM.Datum I W)
  (Sc : SKM.Scalars D k) [Fintype I] (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a)

/-- Restriction on the literal content-support category, not a replacement category.
An integer grading or a support bound on the cyclotomic algebra is not assumed here. -/
def contentRestrictCoeff (β : Multiset I)
    (t : Superfunctor.id k (HeightModules D Sc a ha β.card) ⟶
      Superfunctor.id k (HeightModules D Sc a ha β.card)) :
    Superfunctor.id k (GlobalContentModules D Sc a ha β) ⟶
      Superfunctor.id k (GlobalContentModules D Sc a ha β) :=
  restrictCoeff (heightContentSupported D Sc a ha β.card β) t

/-- The inverse-assembly theorem applies to the literal weight-space product, including
infinite `WeightBlocks`. No uniform support assertion is part of this comparison. -/
theorem weightSpace_isIso_of_eval (Λ x : W) (T : PiSCat k)
    {X Y : Mat_ (Superfunctor k T (globalWeightSpace D Sc a ha Λ x))}
    (F : X ⟶ Y)
    (hF : ∀ β : WeightBlocks D Λ x,
      IsIso ((evalMat (k := k) (fun β : WeightBlocks D Λ x =>
        GlobalContentModules D Sc a ha β.1) T β).map F)) : IsIso F :=
  isIso_of_eval _ T F hF
end WeightSpaces

end OddMath.QuiverHecke.SwappedAssembly.RegularReservoir
