import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMateParity
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeShiftedUnitComparison

/-! # Prescribed finite matrix families on a changing-category induction grid

Brundan--Ellis (1.13)--(1.14) and DeformedMatrixComparison (4), (5) use
canonical parity families and the specified crossing mate, unit/dot columns,
and dot/counit rows. Here the two inductions may change categories. The
entries assemble as actual even module morphisms and literal finite value
components, independently of any inverse or comparison assumption.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
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

end OddMath.QuiverHecke.ELVOld.BalancedInduction
