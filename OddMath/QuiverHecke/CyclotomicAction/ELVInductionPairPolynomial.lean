import OddMath.QuiverHecke.CyclotomicAction.ELVContentOperatorPolynomial
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightQuadratic

/-! # Ordered original-parameter polynomials in arbitrary induction dots

DeformedActionAssembly §6 (9): the generic balanced induction dot powers
realize the signed source evaluation with original coefficients. Arbitrary
source and target categories and all coefficient parities are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]

/-- Evaluation of a source endomorphism against a fixed balanced generator. -/
def inductionEndTensorEval (N : Superfunctor k C (SVec k)) (w : E) (s : C)
    (g : F.obj s ⟶ w) (n : N.obj s) : End (F.obj s) →ₗ[k] Obj F N.toFunctor w where
  toFun a := tensor F N.toFunctor s (a ≫ g) n
  map_add' a b := by
    change F.obj s ⟶ F.obj s at a b
    change tensor F N.toFunctor s ((a + b) ≫ g) n =
      tensor F N.toFunctor s (a ≫ g) n + tensor F N.toFunctor s (b ≫ g) n
    simp only [Preadditive.add_comp, tensor, TensorProduct.add_tmul, map_add]
  map_smul' c a := by
    change F.obj s ⟶ F.obj s at a
    change tensor F N.toFunctor s ((c • a) ≫ g) n =
      c • tensor F N.toFunctor s (a ≫ g) n
    simp only [Linear.smul_comp, tensor, ← TensorProduct.smul_tmul', map_smul]

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b : ∀ s, End (F.obj s)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)

/-- Supported powers retain only the quadratic sign of the original source evaluation. -/
theorem transformLinear_supported_power (N : Superfunctor k C (SVec k)) (w : E)
    (r : ℕ) (hr : (r : ZMod 2) * D.parity i = 0) (c : k)
    (s : C) (g : F.obj s ⟶ w) (n : N.obj s) :
    (c • (transformLinear ha N w ^ r)) (tensor F N.toFunctor s g n) =
      inductionEndTensorEval F N w s g n
        ((SKM.zsign k (D.parity i * (r / 2 : ℕ)) * c) • (a s ^ r)) := by
  rw [LinearMap.smul_apply, transformLinear_pow_tensor, hr, twist_zero]
  change c • (sign k (D.parity i * (r / 2 : ℕ)) • tensor F N.toFunctor s ((a s ^ r) ≫ g) n) = _
  rw [map_smul, smul_smul, sign_eq_zsign, mul_comm c]
  rfl

/-- The ordered interior term uses support from the parameter axioms, not a new premise. -/
theorem transformLinear_pair_monomial (N : Superfunctor k C (SVec k)) (w : E)
    (r t : ℕ) (s : C) (g : F.obj s ⟶ w) (n : N.obj s) :
    (Sc.s i j r t • ((transformLinear hb N w ^ t) * (transformLinear ha N w ^ r)))
      (tensor F N.toFunctor s g n) =
      inductionEndTensorEval F N w s g n
        ((SKM.zsign k (D.parity i * (r / 2 : ℕ) + D.parity j * (t / 2 : ℕ)) * Sc.s i j r t) •
          (a s ^ r * b s ^ t)) := by
  by_cases hc : Sc.s i j r t = 0
  · simp [hc]
  · obtain ⟨hr, ht⟩ := elvParameter_support D Sc hc
    rw [LinearMap.smul_apply, Module.End.mul_apply, transformLinear_pow_tensor,
      map_smul, transformLinear_pow_tensor, hr, ht, twist_zero, twist_zero]
    change Sc.s i j r t • (sign k (D.parity i * (r / 2 : ℕ)) •
      (sign k (D.parity j * (t / 2 : ℕ)) •
        tensor F N.toFunctor s ((b s ^ t) ≫ (a s ^ r) ≫ g) n)) = _
    rw [map_smul]
    change _ = _ • tensor F N.toFunctor s (((a s ^ r * b s ^ t) : End (F.obj s)) ≫ g) n
    simp only [smul_smul, sign_eq_zsign, End.mul_def, Category.assoc]
    rw [mul_comm (Sc.s i j r t), ← SKM.zsign_add]

/-- The actual ordered dot polynomial evaluates the original signed source polynomial. -/
theorem transformLinear_pairPolynomial_tensor (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) (w : E) (s : C) (g : F.obj s ⟶ w) (n : N.obj s) :
    orderedPairOperatorPolynomial D Sc i j (transformLinear ha N w) (transformLinear hb N w)
      (tensor F N.toFunctor s g n) =
      inductionEndTensorEval F N w s g n (elvSignedPairQuadEval D Sc i j (a s) (b s)) := by
  unfold orderedPairOperatorPolynomial elvSignedPairQuadEval
  split_ifs with hd
  · simp [inductionEndTensorEval, End.one_def]
  · simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro t _
      exact transformLinear_pair_monomial F D Sc i j ha hb N w r t s g n
    · congr 1
      · exact transformLinear_supported_power F D i ha N w _
          (CyclotomicAction.dn_cast_mul_parity D hij) _ s g n
      · exact transformLinear_supported_power F D j hb N w _
          (CyclotomicAction.dn_cast_mul_parity D hij.symm) _ s g n
/-- Whole linear operators realize the signed polynomial, once its even naturality is proved. -/
theorem transformLinear_pairPolynomial (hij : i ≠ j)
    (hQ : IsSupernatural k 0 (fun s => elvSignedPairQuadEval D Sc (R := End (F.obj s)) i j (a s) (b s)))
    (N : Superfunctor k C (SVec k)) (w : E) :
    transformLinear hQ N w =
      orderedPairOperatorPolynomial D Sc i j (transformLinear ha N w) (transformLinear hb N w) := by
  apply hom_ext
  intro s g n
  rw [transformLinear_tensor, twist_zero,
    transformLinear_pairPolynomial_tensor F D Sc i j ha hb hij N w s g n]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction
