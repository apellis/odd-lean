import OddMath.CoveringQuantum.UDot.NativeCyclic.LengthLowering

/-!
# Unit leading term for native matched normal words

Corrections lie in the span of actual quotient word tensors strictly shorter in
both formal word lengths. No word independence or action faithfulness is used.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma.NativeLeading
open PreF Coefficients TensorProduct MixedGram
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ Μ : X)

local instance : AddCommGroup
    (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  TensorProduct.addCommGroup

/-- The original native lowering branch, retaining its parity and toral factors. -/
def correction (s : Bool) (i : I) (a b : List I) :=
  tensorFTwist D hD Λ s i (project D hD Λ (monomial Coefficients.Ring a)) ⊗ₜ[Coefficients.Ring]
    lowestF D hD Μ i (project D hD Μ (monomial Coefficients.Ring b))

/-- One negative letter: creation plus the actual lowest-lowering branch. -/
theorem F_word (s : Bool) (i : I) (a b : List I) :
    tensorF D hD Λ Μ s i
      (project D hD Λ (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
        project D hD Μ (monomial Coefficients.Ring b)) =
      tensorToralScalar D false i (Μ - halfWeight D true (wordWeight b)) •
        (project D hD Λ (monomial Coefficients.Ring (i :: a)) ⊗ₜ[Coefficients.Ring]
          project D hD Μ (monomial Coefficients.Ring b)) + correction D hD Λ Μ s i a b := by
  rw [tensorF_tmul, ← project_create, tensorK, ← project_weight, freeWeight_word]
  simp only [← monomial_cons, correction, project, map_smul, tmul_smul]

/-- The omitted creation lowers first length; lowestF strictly lowers second length. -/
theorem correction_mem (s : Bool) (i : I) (a b : List I) (m n : ℕ)
    (ha : a.length < m) (hb : b.length ≤ n) :
    correction D hD Λ Μ s i a b ∈ lowerBidegree D hD Λ Μ m n := by
  rw [correction, ← project_ftwist, ← project_lowestF]
  simp only [freeFTwist, freeLowestF, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
    parityTwist, diagTwist_monomial, project, map_smul, smul_tmul, tmul_smul]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  exact tmul_lower_mem D hD Λ Μ a b i m n ha hb

/-- Native negative action preserves the lower-bidegree error estimate. -/
theorem F_lowerBidegree (s : Bool) (i : I) (m n : ℕ)
    {z : IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ}
    (hz : z ∈ lowerBidegree D hD Λ Μ m n) :
    tensorF D hD Λ Μ s i z ∈ lowerBidegree D hD Λ Μ (m + 1) n := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, b, ha, hb, rfl⟩ := hz
    rw [F_word]
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ _ (wordTensor_mem D hD Λ Μ (i :: a) b (m + 1) n
        (by simpa using Nat.succ_lt_succ ha) hb)
    · exact correction_mem D hD Λ Μ s i a b (m + 1) n
        (ha.trans_le (Nat.le_succ _)) (Nat.le_of_lt hb)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul c x hx ih => simpa only [map_smul] using Submodule.smul_mem _ c ih

/-- All negative creation branches have the same second formal word degree. -/
theorem negative_leading (s : Bool) (a b : List I) :
    ∃ r ∈ lowerBidegree D hD Λ Μ a.length b.length,
      halfOperators D hD Λ Μ s false a
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring]
          project D hD Μ (monomial Coefficients.Ring b)) =
        TensorPositive.amplitude D false (Μ - halfWeight D true (wordWeight b)) a •
          (project D hD Λ (monomial Coefficients.Ring a) ⊗ₜ[Coefficients.Ring]
            project D hD Μ (monomial Coefficients.Ring b)) + r := by
  induction a with
  | nil =>
    refine ⟨0, Submodule.zero_mem _, ?_⟩
    simp [halfOperators, TensorPositive.amplitude, project, monomial]
  | cons i a ih =>
    obtain ⟨r, hr, he⟩ := ih
    let c := TensorPositive.amplitude D false (Μ - halfWeight D true (wordWeight b)) a
    refine ⟨c • correction D hD Λ Μ s i a b + tensorF D hD Λ Μ s i r,
      Submodule.add_mem _ (Submodule.smul_mem _ c
        (correction_mem D hD Λ Μ s i a b (a.length + 1) b.length
          (Nat.lt_succ_self _) le_rfl)) (F_lowerBidegree D hD Λ Μ s i _ _ hr), ?_⟩
    change tensorF D hD Λ Μ s i (halfOperators D hD Λ Μ s false a _) = _
    rw [he, map_add, map_smul, F_word, smul_add, smul_smul]
    simp only [TensorPositive.amplitude, List.map_cons, List.prod_cons, c]
    rw [mul_comm (List.prod _), add_assoc]

/-- Unit leading-term formula for the actual matched normal words and both native coproducts.
Each error tensor has first length less than a.length AND second length less than b.length. -/
theorem normalWord_leading (s : Bool) (a b : List I) :
    IsUnit (leadingScalar D Λ Μ s a b) ∧
    ∃ r ∈ lowerBidegree D hD Λ Μ a.length b.length,
      tensorRepresentation D hD Λ Μ s (normalWord D Coefficients.q pi a b (Λ - Μ))
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1) =
        leadingScalar D Λ Μ s a b •
          (toIntegrable D hD Λ
            (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a)) ⊗ₜ[Coefficients.Ring]
            toIntegrable D hD Μ
              (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b))) + r := by
  refine ⟨leadingScalar_isUnit D Λ Μ s a b, ?_⟩
  obtain ⟨r, hr, he⟩ := negative_leading D hD Λ Μ s a b
  refine ⟨TensorPositive.amplitude D s Λ b • r, Submodule.smul_mem _ _ hr, ?_⟩
  rw [normalWord_action]
  have hp : halfOperators D hD Λ Μ s true b
      (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1) =
      TensorPositive.amplitude D s Λ b •
        (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring]
          project D hD Μ (monomial Coefficients.Ring b)) := by
    simpa only [halfOperators, TensorPositive.pos, wordAction, List.map_map,
      Function.comp_def, PolarizationTransport.vac] using
      TensorPositive.wordAction_pos D hD Λ Μ s b
  rw [hp, map_smul, he, smul_add, smul_smul]
  rfl

/-- Empty positive half: the lower-bidegree submodule is zero, hence exact recovery. -/
theorem normalWord_nil_right (s : Bool) (a : List I) :
    tensorRepresentation D hD Λ Μ s (normalWord D Coefficients.q pi a [] (Λ - Μ))
      (toIntegrable D hD Λ 1 ⊗ₜ[Coefficients.Ring] toIntegrable D hD Μ 1) =
      leadingScalar D Λ Μ s a [] •
        (toIntegrable D hD Λ
            (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring a)) ⊗ₜ[Coefficients.Ring]
          toIntegrable D hD Μ 1) := by
  obtain ⟨_, r, hr, he⟩ := normalWord_leading D hD Λ Μ s a []
  have hz : r = 0 := by simpa only [List.length_nil, lowerBidegree_zero_right,
    Submodule.mem_bot] using hr
  simpa only [hz, add_zero, monomial_nil, map_one] using he

end OddMath.CoveringQuantum.UDot.GenericVerma.NativeLeading
