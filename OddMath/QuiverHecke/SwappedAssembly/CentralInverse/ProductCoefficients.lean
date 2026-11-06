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

end Restriction

section FullModules
variable (A : GSuperAlg k) (P : ObjectProperty (Modules A))
  (hP : ∀ M, P M → P ((PiSupercategory.pi (R := k)).obj M))

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

end Bounds

section WeightSpaces
open CyclotomicAction
variable {I : Type u} {W : Type u} [AddCommGroup W] (D : SKM.Datum I W)
  (Sc : SKM.Scalars D k) [Fintype I] (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a)

end WeightSpaces

end OddMath.QuiverHecke.SwappedAssembly.RegularReservoir
