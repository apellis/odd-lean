import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.QuiverHecke.CyclotomicAction.InductionMixed
import OddMath.QuiverHecke.CyclotomicAction.ProbeVacuumCharts
import OddMath.SKM.FiniteModuleLocalInverse
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate
import OddMath.SKM.RouquierHomPostNaturalInverse
import OddMath.SKM.AugmentedInverseNaturality
import OddMath.Algebra.HomogeneousSuperfunctorIso

/-!
# Induction grid matrix

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Prescribed finite matrix families on a changing-category induction grid

Brundan--Ellis (1.13)--(1.14) and DeformedMatrixComparison (4), (5) use
canonical parity families and the specified crossing mate, unit/dot columns,
and dot/counit rows. Here the two inductions may change categories. The
entries assemble as actual even module morphisms and literal finite value
components, independently of any inverse or comparison assumption.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
local instance gridMatrixModulePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory

/-- The literal canonical shifted sources of the finite unit matrix. -/
def gridUnitMatrixFamily (p : ZMod 2) (N : Superfunctor k A (SVec k)) (m : ℕ) :
    Option (Fin m) → Superfunctor k A (SVec k)
  | none => (SKM.homParityShift (k := k) p).obj (induced J ((restriction J).obj N))
  | some r => (SKM.homParityShift (k := k) (r.val • p)).obj N

/-- The literal canonical shifted targets of the finite cap matrix. -/
def gridCapMatrixFamily (p : ZMod 2) (N : Superfunctor k A (SVec k)) (m : ℕ) :
    Option (Fin m) → Superfunctor k A (SVec k)
  | none => (SKM.homParityShift (k := k) p).obj ((restriction K).obj (induced K N))
  | some r => (SKM.homParityShift (k := k) (r.val • p)).obj N

variable {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ t, K.obj t ⟶ K.obj t} (hβ : IsSupernatural k p β)

/-- The prescribed mate and unit/dot entries, with no column rescaling. -/
def gridUnitMatrixEntry (N : Superfunctor k A (SVec k)) (m : ℕ) (a : Option (Fin m)) :
    gridUnitMatrixFamily J p N m a ⟶ (restriction K).obj (induced K N) :=
  match a with
  | none => ((SKM.homParityShiftDatum (k := k) p).iso
      (induced J ((restriction J).obj N))).hom ≫ orderedGridMateComponent J K hγ N
  | some r => shiftedUnitDotColumn K hβ N r.val

/-- The prescribed mate and dot/counit entries, with their given target shifts. -/
def gridCapMatrixEntry (N : Superfunctor k A (SVec k)) (m : ℕ) (a : Option (Fin m)) :
    induced J ((restriction J).obj N) ⟶ gridCapMatrixFamily K p N m a :=
  match a with
  | none => orderedGridMateComponent J K hγ N ≫
      ((SKM.homParityShiftDatum (k := k) p).iso ((restriction K).obj (induced K N))).inv
  | some r => shiftedCapDotRow J hα N r.val

/-- Every unit-matrix entry is an even map of the actual shifted modules. -/
theorem gridUnitMatrixEntry_mem (N : Superfunctor k A (SVec k)) (m : ℕ) (a : Option (Fin m)) :
    gridUnitMatrixEntry J K hγ hβ N m a ∈ parity (R := k) _ _ 0 := by
  cases a with
  | none =>
    dsimp only [gridUnitMatrixEntry, gridUnitMatrixFamily]
    simpa only [SKM.zmod2_add_self] using comp_mem
      ((SKM.homParityShiftDatum (k := k) p).hom_mem (induced J ((restriction J).obj N)))
      (orderedGridMateComponent_mem J K hγ N)
  | some r => exact shiftedUnitDotColumn_mem K hβ N r.val

/-- Every cap-matrix entry is an even map of the actual shifted modules. -/
theorem gridCapMatrixEntry_mem (N : Superfunctor k A (SVec k)) (m : ℕ) (a : Option (Fin m)) :
    gridCapMatrixEntry J K hγ hα N m a ∈ parity (R := k) _ _ 0 := by
  cases a with
  | none =>
    change orderedGridMateComponent J K hγ N ≫
      ((SKM.homParityShiftDatum (k := k) p).iso ((restriction K).obj (induced K N))).inv ∈
        parity (R := k) _ _ 0
    simpa only [SKM.zmod2_add_self] using comp_mem
      (orderedGridMateComponent_mem J K hγ N)
      ((SKM.homParityShiftDatum (k := k) p).inv_mem ((restriction K).obj (induced K N)))
  | some r => exact shiftedCapDotRow_mem J hα N r.val

/-- The first unit field is the given mate after the canonical source coordinate. -/
theorem gridUnitMatrixEntry_none_total (N : Superfunctor k A (SVec k)) (m : ℕ) (w : A) :
    SVec.toLinearMap ((gridUnitMatrixEntry J K hγ hβ N m none).total w) =
      orderedGridMateLinear J K hγ N w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) p).iso
          (induced J ((restriction J).obj N))).hom.total w) := by
  rw [gridUnitMatrixEntry, Superfunctor.comp_total, SVec.toLinearMap_comp]
  rfl

/-- The first cap field is the same given mate before the canonical target coordinate. -/
theorem gridCapMatrixEntry_none_total (N : Superfunctor k A (SVec k)) (m : ℕ) (w : A) :
    SVec.toLinearMap ((gridCapMatrixEntry J K hγ hα N m none).total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) p).iso
        ((restriction K).obj (induced K N))).inv.total w) ∘ₗ
          orderedGridMateLinear J K hγ N w := by
  rw [gridCapMatrixEntry, Superfunctor.comp_total, SVec.toLinearMap_comp]
  rfl

/-- The dotted unit field evaluates to its actual canonical shifted column. -/
theorem gridUnitMatrixEntry_some_total (N : Superfunctor k A (SVec k)) (m : ℕ) (r : Fin m) (w : A) :
    SVec.toLinearMap ((gridUnitMatrixEntry J K hγ hβ N m (some r)).total w) =
      shiftedUnitDotLinear K hβ N r.val w := shiftedUnitDotColumn_total K hβ N r.val w

/-- The dotted cap field evaluates to its actual canonical shifted row. -/
theorem gridCapMatrixEntry_some_total (N : Superfunctor k A (SVec k)) (m : ℕ) (r : Fin m) (w : A) :
    SVec.toLinearMap ((gridCapMatrixEntry J K hγ hα N m (some r)).total w) =
      shiftedCapDotLinear J hα N r.val w := shiftedCapDotRow_total J hα N r.val w

/-- The actual shifted unit source, evaluated as a pointwise superspace. -/
def gridUnitMatrixSourceSpace (p : ZMod 2) (N : Superfunctor k A (SVec k)) (m : ℕ) (w : A) : SVec k :=
  OddMath.FiniteSuperspace.product fun a => (gridUnitMatrixFamily J p N m a).obj w

/-- The actual shifted cap target, evaluated as a pointwise superspace. -/
def gridCapMatrixTargetSpace (p : ZMod 2) (N : Superfunctor k A (SVec k)) (m : ℕ) (w : A) : SVec k :=
  OddMath.FiniteSuperspace.product fun a => (gridCapMatrixFamily K p N m a).obj w

/-- Literal finite assembly of the given unit columns. -/
def gridUnitMatrixComponent (N : Superfunctor k A (SVec k)) (m : ℕ) (w : A) :
    gridUnitMatrixSourceSpace J p N m w ⟶ ((restriction K).obj (induced K N)).obj w :=
  OddMath.FiniteSuperspace.assembleColumns _ _ fun a => (gridUnitMatrixEntry J K hγ hβ N m a).total w

/-- Literal finite assembly of the given cap rows. -/
def gridCapMatrixComponent (N : Superfunctor k A (SVec k)) (m : ℕ) (w : A) :
    (induced J ((restriction J).obj N)).obj w ⟶ gridCapMatrixTargetSpace K p N m w :=
  OddMath.FiniteSuperspace.assembleRows _ _ fun a => (gridCapMatrixEntry J K hγ hα N m a).total w

/-- The literal unit entries assemble as a morphism of actual modules. -/
def gridUnitMatrixModuleMap (N : Superfunctor k A (SVec k)) (m : ℕ) :
    OddMath.FiniteSupermodule.product (gridUnitMatrixFamily J p N m) ⟶
      (restriction K).obj (induced K N) :=
  OddMath.FiniteSupermodule.columnsHom (gridUnitMatrixEntry J K hγ hβ N m)
    (gridUnitMatrixEntry_mem J K hγ hβ N m)

/-- The literal cap entries assemble as a morphism of actual modules. -/
def gridCapMatrixModuleMap (N : Superfunctor k A (SVec k)) (m : ℕ) :
    induced J ((restriction J).obj N) ⟶
      OddMath.FiniteSupermodule.product (gridCapMatrixFamily K p N m) :=
  OddMath.FiniteSupermodule.rowsHom (gridCapMatrixEntry J K hγ hα N m)
    (gridCapMatrixEntry_mem J K hγ hα N m)

/-- The actual unit module map evaluates to the same prescribed finite component. -/
theorem gridUnitMatrixModuleMap_total (N : Superfunctor k A (SVec k)) (m : ℕ) (w : A) :
    (gridUnitMatrixModuleMap J K hγ hβ N m).total w =
      gridUnitMatrixComponent J K hγ hβ N m w := by
  apply LinearMap.ext
  intro b
  exact OddMath.FiniteSupermodule.columnsHom_total_apply _ _ w b

/-- The actual cap module map evaluates to the same prescribed finite component. -/
theorem gridCapMatrixModuleMap_total (N : Superfunctor k A (SVec k)) (m : ℕ) (w : A) :
    (gridCapMatrixModuleMap J K hγ hα N m).total w =
      gridCapMatrixComponent J K hγ hα N m w := by
  apply LinearMap.ext
  intro b
  funext a
  exact OddMath.FiniteSupermodule.rowsHom_total_apply _ _ w b a

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Local inverse entries of the prescribed induction-grid matrices

BE (1.13)–(1.14): the inverse of the specified even finite grid matrix
supplies the local inverse entries of its given mate and ordinary dotted
unit or cap fields, retaining the canonical parity coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.FiniteSupermodule
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
  (N : Superfunctor k A (SVec k)) (m : ℕ)
local instance gridLocalModulePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory

/-- The given unit matrix inverse supplies every local inverse field of its
specified mate and unit/dot columns. The matrix isomorphism is an intermediate input. -/
def gridLocalInverseFrom
    (e : product (gridUnitMatrixFamily J p N m) ≅ (restriction K).obj (induced K N))
    (he : e.hom = gridUnitMatrixModuleMap J K hγ hβ N m) :
    SKM.SuperSumInvFrom (k := k) (orderedGridMateComponent J K hγ N)
      (unitDotColumn K hβ N) p (fun n => n • p) m :=
  localInverseFromColumns p (fun n => n • p)
    ((SKM.homParityShiftDatum (k := k) p).iso (induced J ((restriction J).obj N)))
    (fun r => (SKM.homParityShiftDatum (k := k) (r.val • p)).iso N)
    ((SKM.homParityShiftDatum (k := k) p).hom_mem _)
    (fun r => (SKM.homParityShiftDatum (k := k) (r.val • p)).hom_mem N)
    (orderedGridMateComponent J K hγ N) (unitDotColumn K hβ N)
    (orderedGridMateComponent_mem J K hγ N) (unitDotColumn_mem K hβ N) e (by
      have hc : restoredColumn
          (optionRestoringIso
            ((SKM.homParityShiftDatum (k := k) p).iso (induced J ((restriction J).obj N)))
            (fun r => (SKM.homParityShiftDatum (k := k) (r.val • p)).iso N))
          (optionForwardColumns (orderedGridMateComponent J K hγ N) (unitDotColumn K hβ N)) =
          gridUnitMatrixEntry J K hγ hβ N m := by
        funext a
        cases a <;> rfl
      rw [he, restoredColumns, gridUnitMatrixModuleMap]
      simp only [hc])

/-- The given cap matrix inverse supplies every local inverse field of its
specified mate and dot/counit rows. The matrix isomorphism is an intermediate input. -/
def gridLocalInverseTo
    (e : induced J ((restriction J).obj N) ≅ product (gridCapMatrixFamily K p N m))
    (he : e.hom = gridCapMatrixModuleMap J K hγ hα N m) :
    SKM.SuperSumInvTo (k := k) (orderedGridMateComponent J K hγ N)
      (capDotRow J hα N) p (fun n => n • p) m :=
  localInverseToRows p (fun n => n • p)
    ((SKM.homParityShiftDatum (k := k) p).iso ((restriction K).obj (induced K N)))
    (fun r => (SKM.homParityShiftDatum (k := k) (r.val • p)).iso N)
    ((SKM.homParityShiftDatum (k := k) p).hom_mem _)
    (fun r => (SKM.homParityShiftDatum (k := k) (r.val • p)).hom_mem N)
    (orderedGridMateComponent J K hγ N) (capDotRow J hα N)
    (orderedGridMateComponent_mem J K hγ N) (capDotRow_mem J hα N) e (by
      have hc : restoredRow
          (optionRestoringIso
            ((SKM.homParityShiftDatum (k := k) p).iso ((restriction K).obj (induced K N)))
            (fun r => (SKM.homParityShiftDatum (k := k) (r.val • p)).iso N))
          (optionForwardRows (orderedGridMateComponent J K hγ N) (capDotRow J hα N)) =
          gridCapMatrixEntry J K hγ hα N m := by
        funext a
        cases a <;> rfl
      rw [he, restoredRows, gridCapMatrixModuleMap]
      simp only [hc])

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Input-module supernaturality of the signed grid mate

DeformedMatrixComparison (4), (5) needs the prescribed same-colour grid
mate on all input module maps. Its crossing has the extra minus, whereas
the rectangular mate of Brundan--Ellis (1.12) uses the positive crossing.
The negative crossing is retained while composing the homogeneous family laws.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
private theorem gridFamily_neg
    {k : Type u} {C A : Type*} [CommRing k] [Category C] [Category A]
    [Preadditive C] [Linear k C] [Supercategory k C]
    [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : C ⥤ A} {p : ZMod 2} {α : ∀ N, F.obj N ⟶ G.obj N}
    (hα : IsSupernatural k p α) : IsSupernatural k p (fun N => -α N) where
  mem N := (parity (R := k) _ _ p).neg_mem (hα.mem N)
  naturality hf := by
    simpa only [Preadditive.comp_neg, Preadditive.neg_comp, smul_neg] using
      congrArg Neg.neg (hα.naturality hf)

variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hα : IsSupernatural k p α)

/-- The given chosen flatten-crossing-unflatten family is supernatural
in every input-module map. -/
theorem gridDoubleCrossComponent_supernatural :
    IsSupernatural k p (F := induction J ⋙ induction K) (G := induction J ⋙ induction K)
      (gridDoubleCrossComponent J K hα) := by
  have h₁ := isSupernatural_of_natTrans (inductionComp (k := k) J K).hom
    (fun N => inductionComp_hom_mem J K N)
  have h₂ := transformComponent_supernatural hα
  have h₃ := isSupernatural_of_natTrans (inductionComp (k := k) J K).inv
    (fun N => inductionComp_inv_mem J K N)
  change IsSupernatural k p (F := induction J ⋙ induction K) (G := induction J ⋙ induction K)
    (fun N => (inductionComp J K).hom.app N ≫ transformComponent hα N ≫
      (inductionComp J K).inv.app N)
  simpa only [zero_add, add_zero, Category.assoc] using h₁.comp (h₂.comp h₃)

/-- The prescribed signed mate is supernatural in arbitrary input-module
maps; no map is restricted to even parity. The extra crossing minus remains
inside the actual component. -/
theorem orderedGridMateComponent_supernatural :
    IsSupernatural k p (F := restriction (k := k) J ⋙ induction (k := k) J)
      (G := induction (k := k) K ⋙ restriction (k := k) K)
      (orderedGridMateComponent J K hα) := by
  have hU₀ := isSupernatural_of_natTrans (R := k) (adjunctionUnit (k := k) K)
    (fun N => adjunctionUnit_mem (k := k) K N)
  have hU := hU₀.whiskerLeft (restriction (k := k) J ⋙ induction (k := k) J)
  have hX₀ := gridFamily_neg (gridDoubleCrossComponent_supernatural J K hα)
  have hX := (hX₀.whiskerLeft (restriction (k := k) J)).whiskerRight (restriction (k := k) K)
  have hC₀ := isSupernatural_of_natTrans (R := k) (adjunctionCounit (k := k) J)
    (fun N => adjunctionCounit_mem (k := k) J N)
  have hC := (hC₀.whiskerRight (induction (k := k) K)).whiskerRight (restriction (k := k) K)
  change IsSupernatural k p (F := restriction (k := k) J ⋙ induction (k := k) J)
    (G := induction (k := k) K ⋙ restriction (k := k) K)
    (fun N => (adjunctionUnit K).app (induced J ((restriction J).obj N)) ≫
      (restriction K).map (-gridDoubleCrossComponent J K hα ((restriction J).obj N)) ≫
      (restriction K).map ((induction K).map ((adjunctionCounit J).app N)))
  have h := hU.comp (hX.comp hC)
  set_option backward.dsimp.instances true in
    dsimp only [induction] at h ⊢
  simpa only [Functor.comp_id, Functor.id_comp, Functor.comp_obj, zero_add, add_zero,
    Category.assoc] using h
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Input-module naturality of the prescribed changing-content matrix entries

DeformedMatrixComparison (4), (5): the given signed mate, unit/dot columns
and normalized dot/counit rows are supernatural on all input-module maps.
The canonical source or target parity coordinates turn these exact entries
into even natural transformations, including on odd and inhomogeneous maps.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
section Dots
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)

/-- The given ordered dot powers form a homogeneous input-module family. -/
theorem gridDotEnd_power_supernatural (n : ℕ) :
    IsSupernatural k (n • p) (F := induction J) (G := induction J)
      (fun M => dotEnd J hα M ^ n) := by
  have hd := transformComponent_supernatural hα
  induction n with
  | zero => simpa only [zero_nsmul, pow_zero, End.one_def] using
      (isSupernatural_id (R := k) (F := induction J))
  | succ n ih =>
    simpa only [pow_succ, End.mul_def, succ_nsmul, add_comm, dotEnd] using hd.comp ih

/-- The ordinary unscaled unit/dot column is supernatural in input maps. -/
theorem gridUnitDotColumn_supernatural (n : ℕ) :
    IsSupernatural k (n • p) (F := 𝟭 (Superfunctor k C (SVec k)))
      (G := induction J ⋙ restriction J) (fun M => unitDotColumn J hα M n) := by
  have hu := isSupernatural_of_natTrans (R := k) (adjunctionUnit J) (adjunctionUnit_mem J)
  simpa only [zero_add, unitDotColumn, adjunction] using hu.comp
    ((gridDotEnd_power_supernatural J hα n).whiskerRight (restriction J))

/-- The given dot/counit row is supernatural in arbitrary input maps. -/
theorem gridCapDotRow_supernatural (n : ℕ) :
    IsSupernatural k (n • p) (F := restriction J ⋙ induction J)
      (G := 𝟭 (Superfunctor k A (SVec k))) (fun M => capDotRow J hα M n) := by
  have hc := isSupernatural_of_natTrans (R := k) (adjunctionCounit J) (adjunctionCounit_mem J)
  simpa only [add_zero, capDotRow, adjunction] using
    ((gridDotEnd_power_supernatural J hα n).whiskerLeft (restriction J)).comp hc
end Dots

section Families
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
local instance gridMatrixInputModulePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory

/-- Each literal unit source summand as a functor of the input module. -/
def gridUnitMatrixSummandFunctor (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    Superfunctor k A (SVec k) ⥤ Superfunctor k A (SVec k) :=
  match a with
  | none => (restriction J ⋙ induction J) ⋙ SKM.homParityShift (k := k) p
  | some r => SKM.homParityShift (k := k) (r.val • p)

/-- Each literal cap target summand as a functor of the input module. -/
def gridCapMatrixSummandFunctor (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    Superfunctor k A (SVec k) ⥤ Superfunctor k A (SVec k) :=
  match a with
  | none => (induction K ⋙ restriction K) ⋙ SKM.homParityShift (k := k) p
  | some r => SKM.homParityShift (k := k) (r.val • p)

instance gridUnitMatrixSummandFunctor_additive (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    (gridUnitMatrixSummandFunctor (k := k) J p m a).Additive := by
  cases a <;> dsimp [gridUnitMatrixSummandFunctor] <;> infer_instance
instance gridUnitMatrixSummandFunctor_linear (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    (gridUnitMatrixSummandFunctor (k := k) J p m a).Linear k := by
  cases a <;> dsimp [gridUnitMatrixSummandFunctor] <;> infer_instance
instance gridUnitMatrixSummandFunctor_super (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    IsSuperfunctor k (gridUnitMatrixSummandFunctor (k := k) J p m a) := by
  cases a <;> dsimp [gridUnitMatrixSummandFunctor] <;> infer_instance
instance gridCapMatrixSummandFunctor_additive (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    (gridCapMatrixSummandFunctor (k := k) K p m a).Additive := by
  cases a <;> dsimp [gridCapMatrixSummandFunctor] <;> infer_instance
instance gridCapMatrixSummandFunctor_linear (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    (gridCapMatrixSummandFunctor (k := k) K p m a).Linear k := by
  cases a <;> dsimp [gridCapMatrixSummandFunctor] <;> infer_instance
instance gridCapMatrixSummandFunctor_super (p : ZMod 2) (m : ℕ) (a : Option (Fin m)) :
    IsSuperfunctor k (gridCapMatrixSummandFunctor (k := k) K p m a) := by
  cases a <;> dsimp [gridCapMatrixSummandFunctor] <;> infer_instance

variable {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)

end Families
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Input-natural local inverses of induction-grid matrices

Brundan–Ellis (1.13)–(1.14): the prescribed even matrix isomorphisms
supply inverse entries on all input modules. Their signed naturality
follows from that of the given forward mate and dotted columns or rows.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {γ : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hγ : IsSupernatural k p γ)
  {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)

/-- The prescribed negative-crossing mate on every input module. -/
def gridMateTransformation :
    (⟨restriction J ⋙ induction J⟩ :
      Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k A (SVec k))) ⟶
    ⟨induction K ⋙ restriction K⟩ :=
  (orderedGridMateComponent_supernatural J K hγ).toSuperNatTrans

/-- The ordinary unit/dot column on every input module. -/
def gridUnitColumnTransformation (n : ℕ) :
    Superfunctor.id k (Superfunctor k A (SVec k)) ⟶
    (⟨induction K ⋙ restriction K⟩ :
      Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k A (SVec k))) :=
  (gridUnitDotColumn_supernatural K hβ n).toSuperNatTrans

/-- The ordinary dot/counit row on every input module. -/
def gridCapRowTransformation (n : ℕ) :
    (⟨restriction J ⋙ induction J⟩ :
      Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k A (SVec k))) ⟶
    Superfunctor.id k (Superfunctor k A (SVec k)) :=
  (gridCapDotRow_supernatural J hα n).toSuperNatTrans

/-- Evaluation retains the ordinary unit column, with no coordinate shift. -/
theorem gridUnitColumnTransformation_total (n : ℕ) (N : Superfunctor k A (SVec k)) :
    (gridUnitColumnTransformation K hβ n).total N = unitDotColumn K hβ N n :=
  OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := Superfunctor.id k (Superfunctor k A (SVec k)))
    (G := ⟨induction K ⋙ restriction K⟩) (gridUnitDotColumn_supernatural K hβ n) N

/-- Evaluation retains the prescribed ordinary cap row. -/
theorem gridCapRowTransformation_total (n : ℕ) (N : Superfunctor k A (SVec k)) :
    (gridCapRowTransformation J hα n).total N = capDotRow J hα N n :=
  OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := ⟨restriction J ⋙ induction J⟩)
    (G := Superfunctor.id k (Superfunctor k A (SVec k)))
    (gridCapDotRow_supernatural J hα n) N

/-- The chosen unit inverses bundle without a separate inverse-naturality
assumption. Entries outside the finite window are zero. -/
def gridLocalInverseFromFamily (m : ℕ)
    (e : ∀ N, OddMath.FiniteSupermodule.product (gridUnitMatrixFamily J p N m) ≅
      (restriction K).obj (induced K N))
    (he : ∀ N, (e N).hom = gridUnitMatrixModuleMap J K hγ hβ N m) :
    SKM.SuperSumInvFrom (k := k) (gridMateTransformation J K hγ)
      (gridUnitColumnTransformation K hβ) p (fun n => n • p) m :=
  SKM.SuperSumInvFrom.ofSupernaturalComponents
    (fun N => gridLocalInverseFrom J K hγ hβ N m (e N) (he N))
    (orderedGridMateComponent_supernatural J K hγ)
    (gridUnitDotColumn_supernatural K hβ)

/-- The chosen cap inverses bundle with all odd input signs retained. -/
def gridLocalInverseToFamily (m : ℕ)
    (e : ∀ N, induced J ((restriction J).obj N) ≅
      OddMath.FiniteSupermodule.product (gridCapMatrixFamily K p N m))
    (he : ∀ N, (e N).hom = gridCapMatrixModuleMap J K hγ hα N m) :
    SKM.SuperSumInvTo (k := k) (gridMateTransformation J K hγ)
      (gridCapRowTransformation J hα) p (fun n => n • p) m :=
  SKM.SuperSumInvTo.ofSupernaturalComponents
    (fun N => gridLocalInverseTo J K hγ hα N m (e N) (he N))
    (orderedGridMateComponent_supernatural J K hγ)
    (gridCapDotRow_supernatural J hα)

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end
