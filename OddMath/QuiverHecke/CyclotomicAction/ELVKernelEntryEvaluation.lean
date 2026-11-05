import OddMath.QuiverHecke.CyclotomicAction.ELVActualKernelMatrices

/-! # Kernel entries on arbitrary supermodules

The kernel transfer of DeformedMatrixComparison §4 must recover the prescribed
module transformations. These evaluation identities keep the ordinary-right
coefficient action and all inhomogeneous input vectors.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  {C D : Type u} [Category.{u} C] [Category.{u} D]
  [Preadditive D] [Linear k D]
  (J : C ⥤ D) (M : C ⥤ SVec k)

/-- Insert a fixed module vector into a Hom-kernel coefficient. -/
def coefficientEvaluation (v : C) (w : D) (m : M.obj v) :
    (J.obj v ⟶ w) →ₗ[k] Obj J M w :=
  inclusion J M w v ∘ₗ (TensorProduct.mk k _ _).flip m

@[simp] theorem coefficientEvaluation_apply (v : C) (w : D)
    (m : M.obj v) (h : J.obj v ⟶ w) :
    coefficientEvaluation J M v w m h = tensor J M v h m := rfl

private theorem evaluation_pow {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (q : V →ₗ[k] W)
    (S : Module.End k V) (T : Module.End k W)
    (h : q.comp S = T.comp q) (n : ℕ) (x : V) :
    q ((S ^ n) x) = (T ^ n) (q x) := by
  have hc : Function.Semiconj q S T := fun x => LinearMap.congr_fun h x
  simpa only [Module.End.pow_apply] using hc.iterate_right n x

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (i : I) (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
  (v t : OldCategory D Sc cutoff) (m : M.obj v)

/-- On the double tensor generators, kernel evaluation is the actual mate. -/
theorem mateKernel_evaluate_tensor (s : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t)
    (b : v ⟶ (append D Sc cutoff i).obj s) :
    BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v
      (mateKernelComponent D Sc cutoff i v t
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b)) m =
      (matrixMateComponent D Sc cutoff i M).total t
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj M).toFunctor
          s g (M.map b m)) := by
  rw [mateKernelComponent_tensor]
  have hp : D.parity i * D.parity i = D.parity i := by
    rcases parity_eq_zero_or_one (D.parity i) with h | h <;> simp [h]
  have hh := oldModuleMate_total_tensor D Sc cutoff i M s t g (M.map b m)
  rw [hp] at hh
  change _ = ((oldModuleMate D Sc cutoff i).app (D.parity i) M).total t _
  rw [hh]
  have hn : BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v
      (-((append D Sc cutoff i).map b ≫ equalCrossComponent D Sc cutoff i s ≫
        twist k (D.parity i) ((append D Sc cutoff i).map g))) m =
      -BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v
        ((append D Sc cutoff i).map b ≫ equalCrossComponent D Sc cutoff i s ≫
          twist k (D.parity i) ((append D Sc cutoff i).map g)) m := by
    simp only [BalancedInduction.tensor, neg_tmul, map_neg]
  exact hn.trans (congrArg Neg.neg (BalancedInduction.balance (append D Sc cutoff i)
    M.toFunctor b (equalCrossComponent D Sc cutoff i s ≫
      twist k (D.parity i) ((append D Sc cutoff i).map g)) m))

/-- Evaluation with the literal induced-restriction module endpoint. -/
def moduleSourceEvaluation :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k]
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t :=
  IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m

/-- Evaluation intertwines the actual kernel dot with the actual module dot. -/
theorem dotKernel_evaluate :
    (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m).comp
        (dotKernelComponent D Sc cutoff i v t) =
      (inductionDot D Sc cutoff i
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t).comp
        (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m) := by
  apply BalancedInduction.hom_ext
  intro s g b
  change v ⟶ (append D Sc cutoff i).obj s at b
  change IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m
    (dotKernelComponent D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b)) =
    inductionDot D Sc cutoff i
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t
      (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b))
  rw [dotKernelComponent_tensor, IndResKernel.evaluate_tensor,
    IndResKernel.evaluate_tensor]
  exact (inductionDot_tensor D Sc cutoff i
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) s t g (M.map b m)).symm

/-- The kernel counit evaluates by the ordinary module counit. -/
theorem counitKernel_evaluate :
    ((M.toFunctor.mapLinearMap (R := k)).flip m).comp
        (counitKernelComponent D Sc cutoff i v t) =
      (BalancedInduction.counit (append D Sc cutoff i) M.toFunctor t).comp
        (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m) := by
  apply BalancedInduction.hom_ext
  intro s g b
  change v ⟶ (append D Sc cutoff i).obj s at b
  change M.map (counitKernelComponent D Sc cutoff i v t
    (BalancedInduction.tensor (append D Sc cutoff i)
      ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b)) m =
    BalancedInduction.counit (append D Sc cutoff i) M.toFunctor t
      (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m
        (BalancedInduction.tensor (append D Sc cutoff i)
          ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b))
  rw [counitKernelComponent_tensor, IndResKernel.evaluate_tensor,
    BalancedInduction.counit_tensor]
  exact congrArg (fun f : M.obj v ⟶ M.obj t => f m) (M.toFunctor.map_comp b g)

/-- Every kernel dot power has the prescribed action on arbitrary module vectors. -/
theorem dotKernel_power_evaluate (n : ℕ)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m
        ((dotKernelComponent D Sc cutoff i v t ^ n) z) =
      (inductionDot D Sc cutoff i
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t ^ n)
        (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m z) :=
  BalancedInduction.evaluation_pow _ _ _ (dotKernel_evaluate D Sc cutoff i M v t m) n z

/-- Ordinary counit-dot powers retain the full module coefficient. -/
theorem capKernel_evaluate (n : ℕ)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    M.map (capKernelComponent D Sc cutoff i n v t z) m =
      BalancedInduction.counit (append D Sc cutoff i) M.toFunctor t
        ((inductionDot D Sc cutoff i
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t ^ n)
          (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m z)) := by
  change M.map (counitKernelComponent D Sc cutoff i v t
    ((dotKernelComponent D Sc cutoff i v t ^ n) z)) m = _
  have hc := LinearMap.congr_fun (counitKernel_evaluate D Sc cutoff i M v t m)
    ((dotKernelComponent D Sc cutoff i v t ^ n) z)
  change M.map (counitKernelComponent D Sc cutoff i v t
    ((dotKernelComponent D Sc cutoff i v t ^ n) z)) m =
    BalancedInduction.counit (append D Sc cutoff i) M.toFunctor t
      (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m
        ((dotKernelComponent D Sc cutoff i v t ^ n) z)) at hc
  exact hc.trans (congrArg (BalancedInduction.counit (append D Sc cutoff i) M.toFunctor t)
    (dotKernel_power_evaluate D Sc cutoff i M v t m n z))

/-- The total of the chosen even counit is the raw balanced evaluation. -/
theorem adjunctionCounit_total_apply
    (z : BalancedInduction.Obj (append D Sc cutoff i)
      ((append D Sc cutoff i) ⋙ M.toFunctor) t) :
    ((BalancedInduction.adjunction (append D Sc cutoff i)).counit.app M).total t z =
      BalancedInduction.counit (append D Sc cutoff i) M.toFunctor t z := by
  simp only [BalancedInduction.adjunction, BalancedInduction.adjunctionCounit,
    Superfunctor.homMk, SuperNatTrans.total, BalancedInduction.counitTransform_app,
    ↓reduceIte, one_ne_zero, add_zero]
  rfl

/-- The kernel cap row evaluates to the literal ordinary categorical cap row. -/
theorem capKernel_evaluate_moduleCapRow (n : ℕ)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    M.map (capKernelComponent D Sc cutoff i n v t z) m =
      (moduleCapRow D Sc cutoff i M n).total t
        (IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m z) := by
  let q := IndResKernel.evaluate (append D Sc cutoff i) M.toFunctor v t m z
  let T := inductionDot D Sc cutoff i
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t
  have hm := LinearMap.congr_fun (moduleCapRow_total D Sc cutoff i M t n) q
  change (moduleCapRow D Sc cutoff i M n).total t q =
    ((BalancedInduction.adjunction (append D Sc cutoff i)).counit.app M).total t ((T ^ n) q) at hm
  have hc := adjunctionCounit_total_apply D Sc cutoff i M t ((T ^ n) q)
  exact (capKernel_evaluate D Sc cutoff i M v t m n z).trans (hm.trans hc).symm

/-- The unscaled unit/dot kernel column evaluates to the ordinary module column. -/
theorem unitKernel_evaluate (n : ℕ) (b : v ⟶ t) :
    BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v
      (unitKernelComponent D Sc cutoff i n v t b) m =
      (moduleUnitColumn D Sc cutoff i M n).total t (M.map b m) := by
  let P : (append D Sc cutoff i).obj t ⟶ (append D Sc cutoff i).obj t :=
    (ideal D Sc cutoff _ _).mkQ (appendMovingPower D Sc cutoff i t.word n)
  have hp := inductionDot_iterate_unit D Sc cutoff i M t n (M.map b m)
  change (inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t))^[n]
      (BalancedInduction.unit (append D Sc cutoff i) M.toFunctor t (M.map b m)) =
    inductionUnitDotSign (k := k) (D.parity i) n •
      BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor t P (M.map b m) at hp
  have hc := LinearMap.congr_fun (moduleUnitColumn_total D Sc cutoff i M t n) (M.map b m)
  change (moduleUnitColumn D Sc cutoff i M n).total t (M.map b m) =
    (inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t) ^ n)
      (((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app M).total t (M.map b m)) at hc
  have hu := adjunctionUnit_total_apply D Sc cutoff i M t (M.map b m)
  change ((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app M).total t
    (M.map b m) = BalancedInduction.unit (append D Sc cutoff i) M.toFunctor t (M.map b m) at hu
  have hc' := hc.trans (congrArg
    (inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t) ^ n) hu)
  simp only [Module.End.pow_apply] at hc'
  refine (show _ = inductionUnitDotSign (k := k) (D.parity i) n •
      BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor t P (M.map b m) from ?_).trans
    (hc'.trans hp).symm
  change BalancedInduction.coefficientEvaluation (append D Sc cutoff i) M.toFunctor
    v ((append D Sc cutoff i).obj t) m
      (inductionUnitDotColumn D Sc cutoff i v.word t.word n b) = _
  rw [inductionUnitDotColumn_comp, map_smul, BalancedInduction.coefficientEvaluation_apply]
  exact congrArg (fun x => inductionUnitDotSign (k := k) (D.parity i) n • x)
    (BalancedInduction.balance (append D Sc cutoff i) M.toFunctor b P m)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
