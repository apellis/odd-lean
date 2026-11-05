import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReservoir
import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedCoefficientEvaluation
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ProbeToReservoirBend
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirToProbeBend

/-! # Output evaluation for the two prescribed mixed bends

`SwappedHomInversion.md` §3 (3)–(6): total evaluation on the full Hom
category, including the parity shifts and the successor block used by
reservoir restriction. These comparisons keep the coefficient carriers
of the bends in `Sigma/ProbeToReservoirBend` and
`Sigma/ReservoirToProbeBend`.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicAction
universe u

local instance bendEvaluationHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

/-- Ordinary total evaluation on a category of superfunctors. -/
def homTotalEvaluation {k C B : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category B] [Preadditive B] [Linear k B] [Supercategory k B] (M : C) :
    Superfunctor k C B ⥤ B where
  obj F := F.obj M
  map f := f.total M
  map_id F := SuperNatTrans.id_total F.toFunctor M
  map_comp f g := Superfunctor.comp_total f g M

instance {k C B : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category B] [Preadditive B] [Linear k B] [Supercategory k B] (M : C) :
    (homTotalEvaluation (k := k) (B := B) M).Additive where
  map_add := (supernaturalTotalLinearMap _ _ M).map_add _ _

instance {k C B : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category B] [Preadditive B] [Linear k B] [Supercategory k B] (M : C) :
    (homTotalEvaluation (k := k) (B := B) M).Linear k where
  map_smul f r := (supernaturalTotalLinearMap _ _ M).map_smul r f

/-- Evaluation at a probe input and an exact reservoir content block. -/
def homContentEvaluation {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (A : PiSCat.{u,u,u+1} k) (M : A) (δ : WeightBlocks D Λ x) :
    (A ⟶ elvWeightSpace D Sc cutoff bound Λ x) ⥤ ContentModules D Sc cutoff bound δ.1 :=
  homTotalEvaluation M ⋙ Pi.eval _ δ

instance homContentEvaluation_additive {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (A : PiSCat.{u,u,u+1} k) (M : A) (δ : WeightBlocks D Λ x) :
    (homContentEvaluation D Sc cutoff bound Λ x A M δ).Additive where
  map_add := by
    intro F G f g
    exact congrArg (fun a => a δ) ((supernaturalTotalLinearMap F G M).map_add f g)

instance homContentEvaluation_linear {I X k : Type u} [AddCommGroup X] [CommRing k]
    (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
    (Λ x : X) (A : PiSCat.{u,u,u+1} k) (M : A) (δ : WeightBlocks D Λ x) :
    (homContentEvaluation D Sc cutoff bound Λ x A M δ).Linear k where
  map_smul f r :=
    congrArg (fun a => a δ) ((supernaturalTotalLinearMap _ _ M).map_smul r f)

section Product
variable {k J : Type u} [CommRing k] (C : J → Type (u+1))
  [∀ j, Category.{u} (C j)] [∀ j, Preadditive (C j)]
  [∀ j, Linear k (C j)] [∀ j, Supercategory k (C j)] [∀ j, PiSupercategory k (C j)]

/-- Componentwise parity transport of an endomorphism. It is a ring map,
so it preserves finite nilpotence bounds without any bound on the product. -/
def productPiEndEvaluation (M : ∀ j, C j) (j : J) :
    letI := productPiSupercategory (k := k) C
    End (M j) →+* End ((PiSupercategory.pi (R := k) (C := ∀ j, C j)).obj M j) := by
  let _ := productPiSupercategory (k := k) C
  let e : ((PiSupercategory.pi (R := k) (C := ∀ j, C j)).obj M j) ≅ M j :=
    { hom := (PiSupercategory.ζ (R := k) M).hom j
      inv := (PiSupercategory.ζ (R := k) M).inv j
      hom_inv_id := congrArg (fun f => f j) (PiSupercategory.ζ (R := k) M).hom_inv_id
      inv_hom_id := congrArg (fun f => f j) (PiSupercategory.ζ (R := k) M).inv_hom_id }
  exact
    { toFun := fun f => e.hom ≫ twist k 1 f ≫ e.inv
      map_zero' := by
        change e.hom ≫ twist k 1 (0 : End (M j)) ≫ e.inv = 0
        rw [map_zero, Limits.zero_comp, Limits.comp_zero]
      map_one' := by
        change e.hom ≫ twist k 1 (𝟙 (M j)) ≫ e.inv = 𝟙 _
        rw [twist_id, Category.id_comp, Iso.hom_inv_id]
      map_add' := by
        intro f g
        change e.hom ≫ twist k 1 (f + g) ≫ e.inv =
          (e.hom ≫ twist k 1 f ≫ e.inv) + (e.hom ≫ twist k 1 g ≫ e.inv)
        rw [map_add, Preadditive.add_comp, Preadditive.comp_add]
      map_mul' := by
        intro f g
        change e.hom ≫ twist k 1 (g ≫ f) ≫ e.inv =
          (e.hom ≫ twist k 1 g ≫ e.inv) ≫ (e.hom ≫ twist k 1 f ≫ e.inv)
        simp only [twist_comp, Category.assoc, Iso.inv_hom_id_assoc] }

/-- Parity transport at one block depends only on that same block. -/
theorem productPi_map_end_component (M : ∀ j, C j) (f : End M) (j : J) :
    letI := productPiSupercategory (k := k) C
    ((PiSupercategory.pi (R := k) (C := ∀ j, C j)).map f) j =
      productPiEndEvaluation C M j (f j) := by
  let _ := productPiSupercategory (k := k) C
  rw [PiSupercategory.pi_map_eq]
  change (PiSupercategory.ζ (R := k) M).hom j ≫ (twist k 1 f) j ≫
    (PiSupercategory.ζ (R := k) M).inv j =
    (PiSupercategory.ζ (R := k) M).hom j ≫ twist k 1 (f j) ≫
    (PiSupercategory.ζ (R := k) M).inv j
  have ht : (twist k 1 f) j = twist k 1 (f j) :=
    map_twist (R := k) (Pi.eval C j) 1 f
  rw [ht]

end Product

section Components
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (Λ x : X) (A : PiSCat.{u,u,u+1} k)
local notation "B" => elvWeightSpace D Sc cutoff bound Λ x

/-- A further Hom parity shift preserves a nilpotence bound at the
same reservoir block, including on odd maps. -/
theorem homParityShift_component_isNilpotent (p : ZMod 2) (F : A ⟶ B)
    (f : End F) (M : A) (δ : WeightBlocks D Λ x)
    (hf : IsNilpotent (End.of (f.total M δ))) :
    IsNilpotent (End.of (((SKM.homParityShift (k := k) (C := A ⟶ B) p).map f).total M δ)) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · let Q : ((A ⟶ B) ⥤ (A ⟶ B)) → Prop :=
      fun G => IsNilpotent (End.of ((G.map f).total M δ))
    exact (congrArg Q (SKM.homParityShift_zero (k := k) (C := A ⟶ B))).mpr hf
  · rw [SKM.homParityShift_one]
    let _ := elvWeightPi D Sc cutoff bound Λ x
    change IsNilpotent (End.of
      (((PiSupercategory.pi (R := k) (C := ELVWeightProduct D Sc cutoff bound Λ x)).map
          (f.app 0 M)) δ +
       ((PiSupercategory.pi (R := k) (C := ELVWeightProduct D Sc cutoff bound Λ x)).map
          (f.app 1 M)) δ))
    rw [productPi_map_end_component, productPi_map_end_component]
    let ψ := productPiEndEvaluation (k := k)
      (fun β : WeightBlocks D Λ x => ContentModules D Sc cutoff bound β.1) (F.obj M) δ
    have h := hf.map ψ
    change IsNilpotent (ψ (End.of (f.app 0 M δ) + End.of (f.app 1 M δ))) at h
    exact (ψ.map_add (End.of (f.app 0 M δ)) (End.of (f.app 1 M δ))) ▸ h

end Components

section Restriction
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)
  (i : I) (Λ : X) {x y : X} (h : x + D.α i = y) (A : PiSCat.{u,u,u+1} k)
  (F : A ⟶ elvWeightSpace D Sc cutoff bound Λ y) (f : End F)

/-- Reservoir restriction reads precisely the successor of the output
content block. The input probe module remains arbitrary. -/
theorem homPost_elvF_total (M : A) (δ : WeightBlocks D Λ x) :
    (((SKM.homPost (k := k) (elvF D Sc cutoff bound i Λ h)).map f).total M) δ =
      (elvBlockRes D Sc cutoff bound i Λ h δ).map
        ((f.total M) (blockSucc D Λ i h δ)) := by
  change (elvBlockRes D Sc cutoff bound i Λ h δ).map
      (f.app 0 M (blockSucc D Λ i h δ)) +
    (elvBlockRes D Sc cutoff bound i Λ h δ).map
      (f.app 1 M (blockSucc D Λ i h δ)) = _
  rw [← Functor.map_add]
  rfl

/-- Restriction and the prescribed extra parity shift preserve a bound
constructed at the successor content block. -/
theorem shiftedPostRestriction_component_isNilpotent (p : ZMod 2)
    (M : A) (δ : WeightBlocks D Λ x)
    (hf : IsNilpotent (End.of (f.total M (blockSucc D Λ i h δ)))) :
    IsNilpotent
      (End.of (((SKM.homParityShift (k := k) p ⋙ SKM.homPost (k := k)
        (elvF D Sc cutoff bound i Λ h)).map f).total M δ)) := by
  let g := (SKM.homParityShift (k := k) p).map f
  let R := (elvBlockRes D Sc cutoff bound i Λ h δ).toFunctor
  let V := ((SKM.homParityShift (k := k) p).obj F).obj M (blockSucc D Λ i h δ)
  let ψ : End V →*₀ End (R.obj V) :=
    { R.mapEnd V with map_zero' := R.map_zero V V }
  have hg := homParityShift_component_isNilpotent D Sc cutoff bound Λ y A p F f M
    (blockSucc D Λ i h δ) hf
  have hmap := hg.map ψ
  change IsNilpotent (End.of
    (R.map (g.app 0 M (blockSucc D Λ i h δ)) + R.map (g.app 1 M (blockSucc D Λ i h δ))))
  change IsNilpotent (End.of (R.map
    (g.app 0 M (blockSucc D Λ i h δ) + g.app 1 M (blockSucc D Λ i h δ)))) at hmap
  rw [Functor.map_add] at hmap
  exact hmap

end Restriction

end OddMath.QuiverHecke.ELVOld
