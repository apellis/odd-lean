import OddMath.QuiverHecke.CyclotomicAction.ELVMateKernelNaturality
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenCoefficientModule
import OddMath.QuiverHecke.CyclotomicAction.ELVMatrixEntryTotals

/-! # Ordinary-right covariance of the actual counit-dot rows

The source action is ordinary coefficient precomposition for all arrows.
The actual induction dot changes only the first tensor factor, and the
ordinary counit composes the untwisted coefficient with that factor.
Consequently every actual ordinary counit/dot-power row is right natural.
-/
noncomputable section
open CategoryTheory Opposite StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private def transportEnd {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (e : V ≃ₗ[k] W) (T : Module.End k W) : Module.End k V :=
  e.symm.toLinearMap.comp (T.comp e.toLinearMap)

private theorem transportEnd_apply {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (e : V ≃ₗ[k] W) (T : Module.End k W) (x : V) :
    transportEnd e T x = e.symm (T (e x)) := rfl

private theorem transportEnd_pow_apply {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (e : V ≃ₗ[k] W) (T : Module.End k W) (n : ℕ) (x : V) :
    e ((transportEnd e T ^ n) x) = (T ^ n) (e x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, transportEnd_apply,
      e.apply_symm_apply, pow_succ, Module.End.mul_apply]

private theorem pow_intertwining {V W : Type u} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (q : V →ₗ[k] W) (S : Module.End k V) (T : Module.End k W)
    (h : T.comp q = q.comp S) (n : ℕ) : (T ^ n).comp q = q.comp (S ^ n) := by
  have hs : Function.Semiconj q S T := fun x => (LinearMap.congr_fun h x).symm
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, Module.End.pow_apply]
  exact (hs.iterate_right n x).symm

@[simp] theorem oldSourceKernelEquiv_symm_tensor (i : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : v ⟶ (append D Sc cutoff i).obj s) :
    (oldSourceKernelEquiv D Sc cutoff i v t).symm
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff v)).toFunctor s g b) =
    BalancedInduction.tensor (append D Sc cutoff i)
      ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b := rfl

def dotKernelComponent (i : I) (v t : OldCategory D Sc cutoff) :
    Module.End k (IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :=
  transportEnd (oldSourceKernelEquiv D Sc cutoff i v t)
    (inductionDot D Sc cutoff i
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (oldRepresentable D Sc cutoff v)) t)

@[simp] theorem dotKernelComponent_tensor (i : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : v ⟶ (append D Sc cutoff i).obj s) :
    dotKernelComponent D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) =
    BalancedInduction.tensor (append D Sc cutoff i)
      ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s
      (oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g) b := by
  rw [dotKernelComponent, transportEnd_apply, oldSourceKernelEquiv_tensor]
  have h := inductionDot_tensor D Sc cutoff i
    ((BalancedInduction.restriction (append D Sc cutoff i)).obj
      (oldRepresentable D Sc cutoff v)) s t g b
  exact (congrArg (oldSourceKernelEquiv D Sc cutoff i v t).symm h).trans
    (oldSourceKernelEquiv_symm_tensor D Sc cutoff i v s t
      (oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g) b)

theorem dotKernelComponent_precompose (i : I)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (dotKernelComponent D Sc cutoff i v t).comp
      (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t) =
    (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t).comp
      (dotKernelComponent D Sc cutoff i w t) := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, IndResKernel.precompose_tensor, dotKernelComponent_tensor]

def counitKernelComponent (i : I) (v t : OldCategory D Sc cutoff) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k] (v ⟶ t) :=
  (unshiftedCounitComponent D Sc cutoff i v.word t.word).comp
    (oldSourceKernelEquiv D Sc cutoff i v t).toLinearMap

theorem counitKernelComponent_apply (i : I) (v t : OldCategory D Sc cutoff)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    counitKernelComponent D Sc cutoff i v t z =
      unshiftedCounitComponent D Sc cutoff i v.word t.word
        (oldSourceKernelEquiv D Sc cutoff i v t z) := rfl

@[simp] theorem counitKernelComponent_tensor (i : I) (v s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : v ⟶ (append D Sc cutoff i).obj s) :
    counitKernelComponent D Sc cutoff i v t
      (BalancedInduction.tensor (append D Sc cutoff i)
        ((append D Sc cutoff i) ⋙ IndResKernel.homModule (k := k) v) s g b) = b ≫ g := by
  rw [counitKernelComponent_apply, oldSourceKernelEquiv_tensor]
  cases v with
  | mk v =>
    cases s with
    | mk s =>
      cases t with
      | mk t => exact unshiftedCounitComponent_tensor D Sc cutoff i v s t g b

theorem counitKernelComponent_precompose (i : I)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (counitKernelComponent D Sc cutoff i v t).comp
      (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t) =
    (Linear.leftComp k t a).comp (counitKernelComponent D Sc cutoff i w t) := by
  apply BalancedInduction.hom_ext
  intro s g b
  simp only [LinearMap.comp_apply, IndResKernel.precompose_tensor,
    counitKernelComponent_tensor]
  exact Category.assoc a b g

/-- Underlying coefficient component of the actual ordinary counit/dot-power row. -/
def capKernelComponent (i : I) (n : ℕ) (v t : OldCategory D Sc cutoff) :
    IndResKernel.Component (k := k) (append D Sc cutoff i) v t →ₗ[k] (v ⟶ t) :=
  (counitKernelComponent D Sc cutoff i v t).comp
    (dotKernelComponent D Sc cutoff i v t ^ n)

theorem capKernelComponent_precompose (i : I) (n : ℕ)
    {v w : OldCategory D Sc cutoff} (a : v ⟶ w) (t : OldCategory D Sc cutoff) :
    (capKernelComponent D Sc cutoff i n v t).comp
      (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t) =
    (Linear.leftComp k t a).comp (capKernelComponent D Sc cutoff i n w t) := by
  have hd := pow_intertwining
    (IndResKernel.precompose (k := k) (append D Sc cutoff i) a t)
    (dotKernelComponent D Sc cutoff i w t) (dotKernelComponent D Sc cutoff i v t)
    (dotKernelComponent_precompose D Sc cutoff i a t) n
  rw [capKernelComponent, capKernelComponent, LinearMap.comp_assoc,
    hd, ← LinearMap.comp_assoc, counitKernelComponent_precompose, LinearMap.comp_assoc]

private theorem moduleCapRow_total_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (n : ℕ)
    (z : ((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj M)).obj t) :
    (moduleCapRow D Sc cutoff i M n).total t z =
      ((BalancedInduction.adjunction (append D Sc cutoff i)).counit.app M).total t
        ((inductionDot D Sc cutoff i
          ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t ^ n) z) := by
  have h := LinearMap.congr_fun (moduleCapRow_total D Sc cutoff i M t n) z
  change (moduleCapRow D Sc cutoff i M n).total t z =
    ((BalancedInduction.adjunction (append D Sc cutoff i)).counit.app M).total t
      ((inductionDot D Sc cutoff i
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj M) t ^ n) z) at h
  exact h

/-- The kernel row is the fixed actual moduleCapRow, not an assumed substitute. -/
theorem capKernelComponent_moduleCapRow (i : I) (n : ℕ) (v t : OldCategory D Sc cutoff)
    (z : IndResKernel.Component (k := k) (append D Sc cutoff i) v t) :
    capKernelComponent D Sc cutoff i n v t z =
      (moduleCapRow D Sc cutoff i (oldRepresentable D Sc cutoff v) n).total t
        (oldSourceKernelEquiv D Sc cutoff i v t z) := by
  rw [capKernelComponent, LinearMap.comp_apply, counitKernelComponent_apply]
  have he := transportEnd_pow_apply (oldSourceKernelEquiv D Sc cutoff i v t)
    (inductionDot D Sc cutoff i
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (oldRepresentable D Sc cutoff v)) t) n z
  have hc := congrArg (unshiftedCounitComponent D Sc cutoff i v.word t.word) he
  exact hc.trans (moduleCapRow_total_apply D Sc cutoff i
    (oldRepresentable D Sc cutoff v) t n (oldSourceKernelEquiv D Sc cutoff i v t z)).symm

/-- Every fixed ordinary counit/dot-power row is an ordinary-right kernel map. -/
def capKernel (i : I) (n : ℕ) (t : OldCategory D Sc cutoff) :
    IndResKernel.kernel (k := k) (append D Sc cutoff i) t ⟶
      BalancedKernelTensor.inductionKernel (k := k) (𝟭 (OldCategory D Sc cutoff)) t where
  app v := ModuleCat.ofHom (capKernelComponent D Sc cutoff i n v.unop t)
  naturality _ _ a := by
    apply ModuleCat.hom_ext
    exact capKernelComponent_precompose D Sc cutoff i n a.unop t

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
