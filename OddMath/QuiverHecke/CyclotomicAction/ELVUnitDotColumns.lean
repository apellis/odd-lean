import OddMath.QuiverHecke.CyclotomicAction.ELVOldInductionRepresentable
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendOutputDot
import OddMath.QuiverHecke.CyclotomicAction.ELVCokernel

/-! # Ordinary unit and dot columns of the positive matrix

The positive columns in DeformedMatrixComparison (4) are the ordinary
adjunction unit followed by induction-dot powers. Under the canonical
upper-Hom equivalence they are the literal output-polynomial columns,
with the prescribed odd dot-power scalar retained. Both moving parities
and complete old Hom coefficients are included.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The scalar introduced by iterating the ordinary induction dot. -/
def inductionUnitDotSign (p : ZMod 2) (n : ℕ) : k := sign k (n.choose 2 • p)

theorem inductionUnitDotSign_succ (p : ZMod 2) (n : ℕ) :
    inductionUnitDotSign (k := k) p (n + 1) =
      sign k (n • p) * inductionUnitDotSign (k := k) p n := by
  have he : (n + 1).choose 2 = n + n.choose 2 := by
    simpa only [Nat.choose_one_right] using Nat.choose_succ_succ n 1
  simp only [inductionUnitDotSign, he, add_nsmul, sign_add]

private def oldAppendPower (i : I) (t : OldCategory D Sc cutoff) (n : ℕ) :
    (append D Sc cutoff i).obj t ⟶ (append D Sc cutoff i).obj t :=
  (ideal D Sc cutoff _ _).mkQ (appendMovingPower D Sc cutoff i t.word n)

private theorem oldAppendPower_mem (i : I) (t : OldCategory D Sc cutoff) (n : ℕ) :
    oldAppendPower D Sc cutoff i t n ∈ parity (R := k) _ _ (n • D.parity i) := by
  apply Submodule.mem_map_of_mem
  rw [appendMovingPower_whisker]
  exact appendComponent_mem D Sc cutoff (firstDot_pow_parity D Sc i [] n) t.word

private theorem oldAppendPower_zero (i : I) (t : OldCategory D Sc cutoff) :
    oldAppendPower D Sc cutoff i t 0 = 𝟙 _ := by
  simp only [oldAppendPower, appendMovingPower, pow_zero, End.one_def, affineUnit_id]
  rfl

private theorem oldAppendPower_succ (i : I) (t : OldCategory D Sc cutoff) (n : ℕ) :
    oldAppendDotComponent D Sc cutoff i t ≫ oldAppendPower D Sc cutoff i t n =
      oldAppendPower D Sc cutoff i t (n + 1) := by
  rw [oldAppendDotComponent_eq]
  change (ideal D Sc cutoff _ _).mkQ
    (appendMovingPower D Sc cutoff i t.word 1 ≫ appendMovingPower D Sc cutoff i t.word n) = _
  congr 1
  unfold appendMovingPower
  rw [← affineUnit_comp]
  change affineUnit D Sc cutoff _ _
    ((dotE D Sc (t.word ++ [i]) t.word.length) ^ n *
      (dotE D Sc (t.word ++ [i]) t.word.length) ^ 1) = _
  rw [pow_one, ← pow_succ]

private theorem tensor_smul_first (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (s t : OldCategory D Sc cutoff) (c : k)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : M.obj s) :
    BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s (c • g) b =
      c • BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s g b := by
  simp only [BalancedInduction.tensor, ← TensorProduct.smul_tmul', map_smul]

/-- Powers on the actual unit tensor, including the odd power scalar. -/
theorem inductionDot_iterate_unit (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (n : ℕ) (b : M.obj t) :
    (inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t))^[n]
      (BalancedInduction.unit (append D Sc cutoff i) M.toFunctor t b) =
      inductionUnitDotSign (k := k) (D.parity i) n •
        BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor t
          (oldAppendPower D Sc cutoff i t n) b := by
  induction n with
  | zero =>
    simp only [Function.iterate_zero, id_eq, inductionUnitDotSign, Nat.choose_zero_succ,
      zero_nsmul, sign_zero, one_smul, oldAppendPower_zero, BalancedInduction.unit_apply]
  | succ n ih =>
    have hp : D.parity i * (n • D.parity i) = n • D.parity i := by
      rcases parity_eq_zero_or_one (D.parity i) with h | h <;> rw [h] <;> simp
    rw [Function.iterate_succ_apply', ih, map_smul, inductionDot_tensor,
      twist_of_mem (D.parity i) (oldAppendPower_mem D Sc cutoff i t n), hp,
      Linear.comp_smul, tensor_smul_first, smul_smul,
      oldAppendPower_succ, inductionUnitDotSign_succ, mul_comm]

/-- The packaged adjunction unit is the existing raw unit on every coefficient. -/
theorem adjunctionUnit_total_apply (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) (b : M.obj t) :
    ((BalancedInduction.adjunctionUnit (append D Sc cutoff i)).app M).total t b =
      BalancedInduction.unit (append D Sc cutoff i) M.toFunctor t b := by
  simp only [BalancedInduction.adjunctionUnit, Superfunctor.homMk, SuperNatTrans.total,
    BalancedInduction.unitTransform_app, ↓reduceIte, one_ne_zero, add_zero]
  rfl

/-- The ordinary categorical unit/dot column, in its canonical upper-Hom coordinates. -/
def inductionUnitDotColumn (i : I) (v t : List I) (n : ℕ) :
    Old D Sc cutoff v t →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  (OldInductionRepresentable.upperHomEquiv D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)).toLinearMap.comp
      (((inductionDot D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))
        ((append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff))) ^ n).comp
        (BalancedInduction.unit (append D Sc cutoff i)
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).toFunctor
          (⟨t⟩ : OldCategory D Sc cutoff)))

/-- No coefficient projection occurs: the actual categorical column equals
its prescribed scalar times the literal polynomial column on full Old(v,t). -/
theorem inductionUnitDotColumn_apply (i : I) (v t : List I) (n : ℕ)
    (b : Old D Sc cutoff v t) :
    inductionUnitDotColumn D Sc cutoff i v t n b =
      inductionUnitDotSign (k := k) (D.parity i) n •
        canonicalAppendTarget D Sc cutoff i v (t ++ [i])
          (appendOutputEmbedding D Sc cutoff i v t (Finsupp.single n b)) := by
  change OldInductionRepresentable.upperHomEquiv D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
    (((inductionDot D Sc cutoff i
      (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff))
      ((append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff))) ^ n)
      (BalancedInduction.unit (append D Sc cutoff i)
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)).toFunctor
        (⟨t⟩ : OldCategory D Sc cutoff) b)) = _
  rw [Module.End.pow_apply, inductionDot_iterate_unit, map_smul]
  congr 1
  have hforward := OldInductionRepresentable.upperHomEquiv_tensor D Sc cutoff i
    (⟨v⟩ : OldCategory D Sc cutoff) (⟨t⟩ : OldCategory D Sc cutoff)
    (⟨t⟩ : OldCategory D Sc cutoff) (oldAppendPower D Sc cutoff i ⟨t⟩ n)
    (show (⟨v⟩ : OldCategory D Sc cutoff) ⟶ (⟨t⟩ : OldCategory D Sc cutoff) from b)
  refine hforward.trans ?_
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
  rw [appendOutputEmbedding_single, canonicalAppendTarget_projection]
  rfl

/-- Finite polynomial assembly of the prescribed scalar-normalized ordinary columns. -/
def unitDotPolynomialMap (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  Finsupp.lsum k fun n => inductionUnitDotSign (k := k) (D.parity i) n •
    inductionUnitDotColumn D Sc cutoff i v t n

@[simp] theorem unitDotPolynomialMap_single (i : I) (v t : List I) (n : ℕ)
    (b : Old D Sc cutoff v t) :
    unitDotPolynomialMap D Sc cutoff i v t (Finsupp.single n b) =
      canonicalAppendTarget D Sc cutoff i v (t ++ [i])
        (appendOutputEmbedding D Sc cutoff i v t (Finsupp.single n b)) := by
  rw [unitDotPolynomialMap, Finsupp.lsum_single, LinearMap.smul_apply,
    inductionUnitDotColumn_apply, smul_smul]
  simp only [inductionUnitDotSign, Supercategory.sign_mul_self, one_smul]

/-- The whole polynomial column map equals the actual ordinary unit/dot assembly. -/
theorem unitDotPolynomialMap_eq (i : I) (v t : List I) :
    unitDotPolynomialMap D Sc cutoff i v t =
      (canonicalAppendTarget D Sc cutoff i v (t ++ [i])).comp
        (appendOutputEmbedding D Sc cutoff i v t) := by
  apply LinearMap.ext
  intro f
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single n b => exact unitDotPolynomialMap_single D Sc cutoff i v t n b

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
