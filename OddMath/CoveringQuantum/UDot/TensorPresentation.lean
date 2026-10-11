import OddMath.CoveringQuantum.UDot.IntegrableWeightOperators

/-!
# The first Serre relations for the actual mixed tensor operators

The operators use Clark's Delta1/Delta2, with v=q^-1, on the tensor of the
source-generated highest quotient and the actual omega-twisted lowest quotient.
The weight and Koszul operators act on arbitrary quotient vectors. The theorem
below verifies disconnected positive Serre relations on the entire tensor.
It is a presentation-descent component, not yet a full tensor representation.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients TensorProduct
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ Μ : X)

/-- Source tilde K, optionally multiplied by tilde J, in v=q^-1 convention. -/
def tensorToralScalar (withJ : Bool) (i : I) (μ : X) : Coefficients.Ring :=
  (if withJ then D.pii pi i ^ (D.h i μ).natAbs else 1) *
    qp Coefficients.q (-(D.d i * D.h i μ))

/-- The toral times Koszul operator in the second summand of Delta1/Delta2(E). -/
def tensorTwist (withJ : Bool) (i : I) :
    Module.End Coefficients.Ring (IntegrableQuotient D hD Λ) :=
  integrableWeight D hD Λ (tensorToralScalar D withJ i) * integrableParity D hD Λ i

/-- Actual mixed-tensor E: withJ=true is Delta1, false is Delta2.
The second factor's E is F in the accepted highest quotient, by Clark omega. -/
def tensorE (withJ : Bool) (i : I) : Module.End Coefficients.Ring
    (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  TensorProduct.map (integrableChevalley D hD Λ true i) LinearMap.id +
    TensorProduct.map (tensorTwist D hD Λ withJ i) (integrableChevalley D hD Μ false i)

@[simp] theorem tensorE_tmul (withJ : Bool) (i : I)
    (x : IntegrableQuotient D hD Λ) (y : IntegrableQuotient D hD Μ) :
    tensorE D hD Λ Μ withJ i (x ⊗ₜ[Coefficients.Ring] y) =
      integrableChevalley D hD Λ true i x ⊗ₜ[Coefficients.Ring] y +
        tensorTwist D hD Λ withJ i x ⊗ₜ[Coefficients.Ring]
          integrableChevalley D hD Μ false i y := rfl

/-- The first-degree Serre relation on the original global quotient operators. -/
theorem integrableChevalley_disconnected (positive : Bool) {i j : I}
    (hij : i ≠ j) (ha : D.a i j = 0) :
    integrableChevalley D hD Λ positive i * integrableChevalley D hD Λ positive j =
      pi ^ (D.parity i * D.parity j).val •
        (integrableChevalley D hD Λ positive j * integrableChevalley D hD Λ positive i) := by
  have hs := integrableChevalley_serre D hD Λ positive hij
  have hN : D.serreDeg i j = 1 := by simp [SuperCartanDatum.serreDeg, ha]
  simp only [hN, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Nat.sub_zero, pow_one, pow_zero, mul_one, Nat.sub_self, one_mul] at hs
  have h0 : D.serreCoeff Coefficients.q pi i j 0 = 1 := by
    simp [SuperCartanDatum.serreCoeff, hN]
  have h1 : D.serreCoeff Coefficients.q pi i j 1 = -pi ^ (D.parity i * D.parity j).val := by
    have hp : ∀ p r : ZMod 2, p.val * r.val = (p * r).val := by decide
    simp [SuperCartanDatum.serreCoeff, hN, SuperCartanDatum.pii, ← pow_mul, hp]
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun f ↦ f x) hs
  simp only [h0, h1, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.zero_apply,
    one_smul, neg_smul] at hx
  simp only [LinearMap.smul_apply]
  exact eq_of_sub_eq_zero (by simpa only [sub_eq_add_neg] using hx)

omit [DecidableEq I] [DecidableEq X] [Finite I] in
/-- Toral scaling has the correct (here trivial) disconnected covariance. -/
theorem tensorToralScalar_shift (withJ : Bool) {i j : I} (ha : D.a i j = 0)
    (positive : Bool) (μ : X) :
    tensorToralScalar D withJ i (μ + halfRoot D positive j) =
      tensorToralScalar D withJ i μ := by
  cases positive <;> simp [tensorToralScalar, halfRoot, RootDatum.h, D.coroot_root, ha]

/-- Genuine Koszul covariance of the full toral/Koszul factor. -/
theorem tensorTwist_chevalley (withJ : Bool) {i j : I} (ha : D.a i j = 0)
    (positive : Bool) (x : IntegrableQuotient D hD Λ) :
    tensorTwist D hD Λ withJ i (integrableChevalley D hD Λ positive j x) =
      pi ^ (D.parity i * D.parity j).val •
        integrableChevalley D hD Λ positive j (tensorTwist D hD Λ withJ i x) := by
  simp only [tensorTwist, Module.End.mul_apply, integrableParity_chevalley, map_smul,
    integrableWeight_chevalley, tensorToralScalar_shift D withJ ha]

/-- The toral/Koszul operators commute on every vector, not just homogeneous ones. -/
theorem tensorTwist_comm (withJ : Bool) (i j : I) :
    tensorTwist D hD Λ withJ i * tensorTwist D hD Λ withJ j =
      tensorTwist D hD Λ withJ j * tensorTwist D hD Λ withJ i := by
  apply LinearMap.ext
  intro x
  induction x using integrable_induction D hD Λ with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul c x hx => simpa only [map_smul] using congrArg (c • ·) hx
  | word w =>
    simp only [tensorTwist, Module.End.mul_apply, integrableParity, integrableSign_word,
      map_smul, integrableWeight_word, smul_smul]
    congr 1
    ring

/-- Disconnected positive Serre relations for the actual two-summand Delta1/Delta2
operators on the entire mixed tensor. Both pi components, including odd-by-odd,
are retained. No tensor-action compatibility is hypothesized. -/
theorem tensorE_disconnected (withJ : Bool) {i j : I}
    (hij : i ≠ j) (ha : D.a i j = 0) :
    tensorE D hD Λ Μ withJ i * tensorE D hD Λ Μ withJ j =
      pi ^ (D.parity i * D.parity j).val •
        (tensorE D hD Λ Μ withJ j * tensorE D hD Λ Μ withJ i) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, Module.End.mul_apply,
    LinearMap.smul_apply, tensorE_tmul, map_add]
  have he := congrArg (fun f ↦ f x) (integrableChevalley_disconnected D hD Λ true hij ha)
  have hf := congrArg (fun f ↦ f y) (integrableChevalley_disconnected D hD Μ false hij ha)
  have ht := congrArg (fun f ↦ f x) (tensorTwist_comm D hD Λ withJ i j)
  simp only [Module.End.mul_apply, LinearMap.smul_apply] at he hf ht
  rw [he, hf, tensorTwist_chevalley D hD Λ withJ ha true, ht]
  have hb : D.a j i = 0 := (D.isGCM.zero_comm i j).mp ha
  have hc := tensorTwist_chevalley D hD Λ withJ hb true x
  rw [mul_comm (D.parity j) (D.parity i)] at hc
  have hp : pi ^ (D.parity i * D.parity j).val * pi ^ (D.parity i * D.parity j).val = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm _ 2, pow_mul, pi_sq, one_pow]
  have hc' : integrableChevalley D hD Λ true i (tensorTwist D hD Λ withJ j x) =
      pi ^ (D.parity i * D.parity j).val • tensorTwist D hD Λ withJ j
        (integrableChevalley D hD Λ true i x) := by
    rw [hc, smul_smul, hp, one_smul]
  rw [hc']
  simp only [smul_tmul, tmul_smul, smul_add]
  abel

/-- Toral/Koszul scaling preserves each actual weight space. -/
theorem tensorTwist_project (withJ : Bool) (i : I) (μ : X)
    (x : IntegrableQuotient D hD Λ) :
    integrableRepresentation D hD Λ (one D Coefficients.q pi μ)
      (tensorTwist D hD Λ withJ i x) =
      tensorTwist D hD Λ withJ i
        (integrableRepresentation D hD Λ (one D Coefficients.q pi μ) x) := by
  induction x using integrable_induction D hD Λ with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | smul c x hx => simp only [map_smul, hx]
  | word w =>
    have ht : tensorTwist D hD Λ withJ i
        (toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w))) =
        ((w.map (fun j ↦ pi ^ (D.parity i * D.parity j).val)).prod *
          tensorToralScalar D withJ i (Λ - halfWeight D true (wordWeight w))) •
          toIntegrable D hD Λ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring w)) := by
      simp only [tensorTwist, Module.End.mul_apply, integrableParity, integrableSign_word,
        map_smul, integrableWeight_word, smul_smul]
    rw [ht]
    simp only [map_smul, integrableRepresentation_toIntegrable, representation_one,
      weightProject_mk, weightProjectFree_monomial]
    split_ifs <;> simp [ht]

private def tensorProjectBilinear (η : X) :
    IntegrableQuotient D hD Λ →ₗ[Coefficients.Ring]
      IntegrableQuotient D hD Μ →ₗ[Coefficients.Ring]
        (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  (Finsupp.lsum Coefficients.Ring fun a ↦
    (TensorProduct.mk Coefficients.Ring _ _).compl₂
      (integrableRepresentation D hD Μ (one D Coefficients.q pi (Λ - a - η)))).comp
        (integrableGrading D hD Λ)

/-- Total-weight projection on the actual highest/lowest tensor. This is a finite
sum from the descended grading, not a sum over assumed finite weight fibers. -/
def tensorProject (η : X) : Module.End Coefficients.Ring
    (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  TensorProduct.lift (tensorProjectBilinear D hD Λ Μ η)

/-- Arbitrary first quotient vectors and a homogeneous second word suffice to
compute the genuine mixed-weight projector. -/
theorem tensorProject_tmul_word (η : X) (x : IntegrableQuotient D hD Λ) (b : List I) :
    tensorProject D hD Λ Μ η
      (x ⊗ₜ[Coefficients.Ring]
        toIntegrable D hD Μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b))) =
      integrableRepresentation D hD Λ
        (one D Coefficients.q pi (η + Μ - halfWeight D true (wordWeight b))) x ⊗ₜ[Coefficients.Ring]
        toIntegrable D hD Μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b)) := by
  induction x using integrable_induction D hD Λ with
  | zero => simp
  | add x y hx hy => simp only [map_add, add_tmul, hx, hy]
  | smul c x hx => simp only [map_smul, smul_tmul, tmul_smul, hx]
  | word a =>
    simp only [tensorProject, TensorProduct.lift.tmul, tensorProjectBilinear,
      LinearMap.comp_apply, integrableGrading_word, Finsupp.lsum_single,
      LinearMap.compl₂_apply, TensorProduct.mk_apply,
      integrableRepresentation_toIntegrable, representation_one,
      weightProject_mk, weightProjectFree_monomial]
    have he : halfWeight D true (wordWeight b) = Μ - (Λ - halfWeight D true (wordWeight a) - η) ↔
        halfWeight D true (wordWeight a) = Λ - (η + Μ - halfWeight D true (wordWeight b)) := by
      constructor <;> intro h
      · rw [h]; abel
      · rw [h]; abel
    simp only [he]
    split_ifs <;> simp

/-- Orthogonal idempotence of the actual mixed tensor projectors. -/
theorem tensorProject_mul (η ν : X) :
    tensorProject D hD Λ Μ η * tensorProject D hD Λ Μ ν =
      if η = ν then tensorProject D hD Λ Μ η else 0 := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply]
  induction y using integrable_induction D hD Μ with
  | zero => simp
  | add y z hy hz =>
    simp only [tmul_add, map_add] at *
    split_ifs at * <;> simp_all
  | smul c y hy =>
    simp only [tmul_smul, map_smul] at *
    split_ifs at * <;> simp_all
  | word b =>
    simp only [Module.End.mul_apply, tensorProject_tmul_word]
    rw [← Module.End.mul_apply, ← map_mul, one_mul_one]
    by_cases h : η = ν
    · subst ν; simp [tensorProject_tmul_word]
    · have hn : η + Μ - halfWeight D true (wordWeight b) ≠
          ν + Μ - halfWeight D true (wordWeight b) := by simpa using h
      simp [h, hn]

/-- The concrete Delta1/Delta2 positive operator has the actual total-weight shift. -/
theorem tensorProject_E (withJ : Bool) (i : I) (η : X) :
    tensorProject D hD Λ Μ η * tensorE D hD Λ Μ withJ i =
      tensorE D hD Λ Μ withJ i * tensorProject D hD Λ Μ (η - D.α i) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, Module.End.mul_apply]
  induction y using integrable_induction D hD Μ with
  | zero => simp
  | add y z hy hz => simp only [tmul_add, map_add, hy, hz]
  | smul c y hy => simp only [tmul_smul, map_smul, hy]
  | word b =>
    have hf : integrableChevalley D hD Μ false i
        (toIntegrable D hD Μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring b))) =
        toIntegrable D hD Μ (D.toSerreF Coefficients.q pi (monomial Coefficients.Ring (i :: b))) := by
      rw [integrableChevalley_mk, chevalley_false_apply, monomial_cons,
        map_mul (D.toSerreF Coefficients.q pi)]
    simp only [tensorE_tmul, hf, map_add, tensorProject_tmul_word,
      integrableProject_chevalley, halfRoot, ite_true, tensorTwist_project,
      wordWeight_cons, halfWeight_add, halfWeight_single]
    have h1 : η + Μ - halfWeight D true (wordWeight b) - D.α i =
        η - D.α i + Μ - halfWeight D true (wordWeight b) := by abel
    have h2 : η + Μ - (D.α i + halfWeight D true (wordWeight b)) =
        η - D.α i + Μ - halfWeight D true (wordWeight b) := by abel
    rw [h1, h2]

/-- Weight-labelled positive generator for either genuine coproduct convention. -/
def tensorEBlock (withJ : Bool) (i : I) (η : X) : Module.End Coefficients.Ring
    (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  tensorE D hD Λ Μ withJ i * tensorProject D hD Λ Μ η

/-- Right-corner presentation relation on every quotient tensor. -/
theorem tensorEBlock_project (withJ : Bool) (i : I) (η : X) :
    tensorEBlock D hD Λ Μ withJ i η * tensorProject D hD Λ Μ η =
      tensorEBlock D hD Λ Μ withJ i η := by
  simp only [tensorEBlock, mul_assoc, tensorProject_mul, ite_true]

/-- Left-corner presentation relation, with the genuine shifted weight. -/
theorem tensorProject_EBlock (withJ : Bool) (i : I) (η : X) :
    tensorProject D hD Λ Μ (η + D.α i) * tensorEBlock D hD Λ Μ withJ i η =
      tensorEBlock D hD Λ Μ withJ i η := by
  rw [tensorEBlock, ← mul_assoc, tensorProject_E, add_sub_cancel_right, mul_assoc]
  simp only [tensorProject_mul, ite_true]

end OddMath.CoveringQuantum.UDot.GenericVerma
