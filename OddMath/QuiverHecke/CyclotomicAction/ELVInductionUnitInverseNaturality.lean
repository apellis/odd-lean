import OddMath.QuiverHecke.CyclotomicAction.ELVInductionUnitInverseRows
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMatrixNaturality
import OddMath.Algebra.FiniteSupermoduleFamily

/-! # Input naturality of the finite dotted-unit inverse rows

Brundan–Ellis (1.13): the specified shifted unit columns form an even
natural matrix. Its constructed component inverses are therefore natural;
projecting and removing the original shift gives the signed row family.
No inverse-naturality condition is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
local instance unitInverseInputPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- The actual finite shifted source family on all input modules. -/
def unitColumnInputFunctor (p : ZMod 2) (m : ℕ) :
    Superfunctor k C (SVec k) ⥤ Superfunctor k C (SVec k) :=
  OddMath.FiniteSupermodule.familyFunctor
    (fun r : Fin m => SKM.homParityShift (k := k) (r.val • p))

private theorem product_projection
    {ι : Type} [Fintype ι] {V W : ι → Superfunctor k C (SVec k)}
    (f : ∀ a, V a ⟶ W a) (a : ι) :
    OddMath.FiniteSupermodule.productMap f ≫ OddMath.FiniteSupermodule.projectionHom W a =
      OddMath.FiniteSupermodule.projectionHom V a ≫ f a := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  rw [Superfunctor.comp_total, Superfunctor.comp_total]
  apply SVec.hom_ext
  intro x
  rw [SVec.comp_apply, SVec.comp_apply, OddMath.FiniteSupermodule.projectionHom_total_apply,
    OddMath.FiniteSupermodule.projectionHom_total_apply]
  exact OddMath.FiniteSupermodule.productMap_total_apply f w x a

private def unitInputProjection (p : ZMod 2) (m : ℕ) (r : Fin m) :
    unitColumnInputFunctor (k := k) (C := C) p m ⟶ SKM.homParityShift (k := k) (r.val • p) where
  app M := OddMath.FiniteSupermodule.projectionHom (unitColumnModuleFamily p M m) r
  naturality _ _ f := product_projection
    (fun a : Fin m => (SKM.homParityShift (k := k) (a.val • p)).map f) r

variable {A : Type u} [Category.{u} A]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)

private theorem shiftedUnitColumn_input_supernatural (n : ℕ) :
    IsSupernatural k 0 (F := SKM.homParityShift (k := k) (n • p))
      (G := induction (k := k) J ⋙ restriction (k := k) J) (fun M => shiftedUnitDotColumn J hα M n) := by
  simpa only [shiftedUnitDotColumn, SKM.zmod2_add_self] using
    ((SKM.homParityShiftDatum (k := k) (n • p)).supernatural).comp
      (gridUnitDotColumn_supernatural J hα n)

/-- The prescribed even matrix on all input module maps, including odd ones. -/
def unitColumnInputNatTrans (m : ℕ) :
    unitColumnInputFunctor (k := k) (C := C) p m ⟶ induction (k := k) J ⋙ restriction (k := k) J where
  app M := unitColumnModuleMap J hα M m
  naturality M N f :=
    OddMath.FiniteSupermodule.productMap_columnsHom
      (fun r : Fin m => (SKM.homParityShift (k := k) (r.val • p)).map f)
      (fun r => shiftedUnitDotColumn J hα N r.val)
      (fun r => shiftedUnitDotColumn J hα M r.val)
      ((induction (k := k) J ⋙ restriction (k := k) J).map f)
      (fun r => shiftedUnitDotColumn_mem J hα N r.val)
      (fun r => shiftedUnitDotColumn_mem J hα M r.val)
      (fun r => (shiftedUnitColumn_input_supernatural J hα r.val).naturality_zero f)

variable (m : ℕ)
  (e : ∀ M, OddMath.FiniteSupermodule.product (unitColumnModuleFamily p M m) ≅
    (restriction (k := k) J).obj ((induction (k := k) J).obj M))
  (he : ∀ M, (e M).hom = unitColumnModuleMap J hα M m)

/-- The constructed component inverses of the specified matrix form a natural isomorphism. -/
def unitColumnInputNatIso : unitColumnInputFunctor (k := k) (C := C) p m ≅
    induction (k := k) J ⋙ restriction (k := k) J :=
  NatIso.ofComponents e (by
    intro M N f
    simpa only [he, unitColumnInputNatTrans] using (unitColumnInputNatTrans J hα m).naturality f)

private def inverseShiftRowNatTrans (r : Fin m) :
    induction (k := k) J ⋙ restriction (k := k) J ⟶ SKM.homParityShift (k := k) (r.val • p) :=
  (unitColumnInputNatIso J hα m e he).inv ≫ unitInputProjection (k := k) p m r

private theorem inverseShiftRowNatTrans_mem (r : Fin m) (M : Superfunctor k C (SVec k)) :
    (inverseShiftRowNatTrans J hα m e he r).app M ∈ parity (R := k) _ _ 0 := by
  have h0 : (e M).hom ∈ parity (R := k) _ _ 0 := by
    rw [he]
    exact unitColumnModuleMap_mem J hα M m
  change (e M).inv ≫ OddMath.FiniteSupermodule.projectionHom (unitColumnModuleFamily p M m) r ∈
    parity (R := k) _ _ 0
  simpa only [zero_add] using comp_mem (inv_mem (e M) h0)
      (OddMath.FiniteSupermodule.projectionHom_mem (unitColumnModuleFamily p M m) r)

include he in
/-- Input supernaturality of the given inverse rows follows from the forward
unit matrix alone, retaining each original source-unshift sign. -/
theorem unitColumnInverseRow_supernatural (r : Fin m) :
    IsSupernatural k (r.val • p) (F := induction (k := k) J ⋙ restriction (k := k) J)
      (G := 𝟭 (Superfunctor k C (SVec k))) (fun M => unitColumnInverseRow J M m (e M) r) := by
  have hi := isSupernatural_of_natTrans (R := k) (inverseShiftRowNatTrans J hα m e he r)
    (inverseShiftRowNatTrans_mem J hα m e he r)
  have hrow (M : Superfunctor k C (SVec k)) :
      (inverseShiftRowNatTrans J hα m e he r).app M ≫
        ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom =
          unitColumnInverseRow J M m (e M) r := Category.assoc _ _ _
  have hfun :
      (fun M : Superfunctor k C (SVec k) =>
        (inverseShiftRowNatTrans J hα m e he r).app M ≫
          ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom) =
      (fun M : Superfunctor k C (SVec k) => unitColumnInverseRow J M m (e M) r) := funext hrow
  have h := hi.comp (SKM.homParityShiftDatum (k := k) (r.val • p)).supernatural
  have hs : IsSupernatural k (r.val • p)
      (F := induction (k := k) J ⋙ restriction (k := k) J)
      (G := 𝟭 (Superfunctor k C (SVec k)))
      (fun M => (inverseShiftRowNatTrans J hα m e he r).app M ≫
        ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom) := by
    simpa only [zero_add] using h
  exact hfun ▸ hs

/-- The inverse row as a homogeneous cell on all input modules. -/
def unitColumnInverseTransformation (r : Fin m) :
    (⟨induction (k := k) J ⋙ restriction (k := k) J⟩ :
      Superfunctor k (Superfunctor k C (SVec k)) (Superfunctor k C (SVec k))) ⟶
    Superfunctor.id k (Superfunctor k C (SVec k)) :=
  (unitColumnInverseRow_supernatural J hα m e he r).toSuperNatTrans

theorem unitColumnInverseTransformation_total (r : Fin m) (M : Superfunctor k C (SVec k)) :
    (unitColumnInverseTransformation J hα m e he r).total M = unitColumnInverseRow J M m (e M) r :=
  OddMath.HomogeneousSuperfunctorIso.homogeneous_total
    (F := ⟨induction (k := k) J ⋙ restriction (k := k) J⟩) (G := Superfunctor.id k (Superfunctor k C (SVec k)))
    (unitColumnInverseRow_supernatural J hα m e he r) M

end OddMath.QuiverHecke.ELVOld.BalancedInduction
