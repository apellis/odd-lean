import OddMath.QuiverHecke.CyclotomicAction.ELVKernelMatrixInteger
import OddMath.QuiverHecke.CyclotomicAction.ELVModuleInverseKernelCoordinates

/-! # Integer degree of represented unit-inverse-cap closures

The source-coefficient calculation needed by ReservoirClosureDegree applies
ordinary unit/dot columns, the prescribed principal finite inverse, then
ordinary dot/cap rows. Both height orientations have degree
`2 dᵢ (r+s+1)`. The evaluation equations retain the actual OLD module maps
and all their canonical parity coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Ordinary unit/dot, positive principal inverse, then ordinary dot/cap. -/
def positiveKernelClosure (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) (r s : ℕ) :
    (v ⟶ t) →ₗ[k] (v ⟶ t) :=
  capKernelComponent D Sc cutoff i s v t ∘ₗ
    positiveKernelPrincipalInverse D Sc cutoff i v t hh ∘ₗ
      unitKernelComponent D Sc cutoff i r v t

/-- The same literal closure using the negative principal inverse. -/
def negativeKernelClosure (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) (r s : ℕ) :
    (v ⟶ t) →ₗ[k] (v ⟶ t) :=
  capKernelComponent D Sc cutoff i s v t ∘ₗ
    negativeKernelPrincipalInverse D Sc cutoff i v t hh ∘ₗ
      unitKernelComponent D Sc cutoff i r v t

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

/-- The positive represented closure has its prescribed integer degree. -/
theorem positiveKernelClosure_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I)) (r s : ℕ)
    {n : ℤ} {b : v ⟶ t} (hb : b ∈ oldDegree D sy Sc hc cutoff v.word t.word n) :
    positiveKernelClosure D Sc cutoff i v t hh r s b ∈
      oldDegree D sy Sc hc cutoff v.word t.word (n + 2 * sy.d i * (r + s + 1 : ℕ)) := by
  have h := capKernelComponent_degree D Sc cutoff sy hc i v t s
    (positiveKernelPrincipalInverse_degree D Sc cutoff sy hc i v t hh
      (unitKernelComponent_degree D Sc cutoff sy hc i v t r hb))
  have he : n + 2 * sy.d i * r + 2 * sy.d i + 2 * sy.d i * s =
      n + 2 * sy.d i * (r + s + 1 : ℕ) := by push_cast; ring
  simpa only [positiveKernelClosure, LinearMap.comp_apply, he] using h

/-- The negative represented closure has the same prescribed degree. -/
theorem negativeKernelClosure_degree (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0) (r s : ℕ)
    {n : ℤ} {b : v ⟶ t} (hb : b ∈ oldDegree D sy Sc hc cutoff v.word t.word n) :
    negativeKernelClosure D Sc cutoff i v t hh r s b ∈
      oldDegree D sy Sc hc cutoff v.word t.word (n + 2 * sy.d i * (r + s + 1 : ℕ)) := by
  have h := capKernelComponent_degree D Sc cutoff sy hc i v t s
    (negativeKernelPrincipalInverse_degree D Sc cutoff sy hc i v t hh
      (unitKernelComponent_degree D Sc cutoff sy hc i v t r hb))
  have he : n + 2 * sy.d i * r + 2 * sy.d i + 2 * sy.d i * s =
      n + 2 * sy.d i * (r + s + 1 : ℕ) := by push_cast; ring
  simpa only [negativeKernelClosure, LinearMap.comp_apply, he] using h

omit sy hc in
/-- On every OLD module, the positive closure acts by the prescribed unit,
canonical principal inverse, and cap; the module vector is unrestricted. -/
theorem positiveKernelClosure_evaluate
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (i : I) (v t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r s : ℕ) (b : v ⟶ t) (m : M.obj v) :
    M.map (positiveKernelClosure D Sc cutoff i v t hh r s b) m =
      (moduleCapRow D Sc cutoff i M s).total t
        (moduleIsoLinearEquiv (unitMatrixFirstSourceIso D Sc cutoff i M
          (contentUnitCount D cutoff i (t.word : Multiset I))) t
          (((moduleUnitMatrixIso D Sc cutoff M i t hh).inv
            ((moduleUnitColumn D Sc cutoff i M r).total t (M.map b m))) none)) := by
  rw [positiveKernelClosure, LinearMap.comp_apply, LinearMap.comp_apply,
    capKernel_evaluate_moduleCapRow,
    ← moduleUnitMatrixIso_principal_inv_tensor,
    unitKernel_evaluate]

omit sy hc in
/-- Inserting the upper-Hom coefficient before realization is exactly the
principal target insertion with its prescribed canonical parity coordinate. -/
theorem negativeKernelCoordinates_single_tensor
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (i : I) (m : ℕ) (v t : OldCategory D Sc cutoff)
    (y : (append D Sc cutoff i).obj v ⟶ (append D Sc cutoff i).obj t) (b : M.obj v) :
    TensorMatrixCoordinates.negativeKernelCoordinates D Sc cutoff M i m t
      (BalancedKernelTensor.tensor _ M.toFunctor v (Pi.single none y) b) =
    Pi.single none ((moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t).symm
      (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor v y b)) := by
  classical
  funext a
  rw [negativeKernelCoordinates_apply, BalancedKernelTensor.map_tensor]
  change negativeSlotCoordinates D Sc cutoff M i m t a
    (BalancedKernelTensor.tensor _ M.toFunctor v
      ((Pi.single none y : ∀ c, (negativeKernelFamily D Sc cutoff i m t c).obj (Opposite.op v)) a) b) = _
  cases a with
  | none =>
    simp only [Pi.single_eq_same]
    apply (moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M m) t).injective
    rw [negativeSlotCoordinates_none, LinearEquiv.apply_symm_apply]
    exact resIndKernelCoordinates_tensor D Sc cutoff M i v t y b
  | some r =>
    simp only [Pi.single_eq_of_ne (by simp : some r ≠ none),
      BalancedKernelTensor.tensor_zero_left, map_zero]

omit sy hc in
/-- The negative closure likewise acts by the ordinary unit, the actual cap
matrix inverse at its canonically shifted principal input, and ordinary cap. -/
theorem negativeKernelClosure_evaluate
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (i : I) (v t : OldCategory D Sc cutoff)
    (hh : contentCrossingHeight D cutoff i (t.word : Multiset I) ≤ 0)
    (r s : ℕ) (b : v ⟶ t) (m : M.obj v) :
    M.map (negativeKernelClosure D Sc cutoff i v t hh r s b) m =
      (moduleCapRow D Sc cutoff i M s).total t
        ((moduleCapMatrixIso D Sc cutoff M i t hh).inv
          (Pi.single none
            ((moduleIsoLinearEquiv (capMatrixFirstTargetIso D Sc cutoff i M
              (contentCapCount D cutoff i (t.word : Multiset I))) t).symm
              ((moduleUnitColumn D Sc cutoff i M r).total t (M.map b m))))) := by
  rw [negativeKernelClosure, LinearMap.comp_apply, LinearMap.comp_apply,
    capKernel_evaluate_moduleCapRow,
    ← moduleCapMatrixIso_principal_inv_tensor,
    negativeKernelCoordinates_single_tensor, unitKernel_evaluate]

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
