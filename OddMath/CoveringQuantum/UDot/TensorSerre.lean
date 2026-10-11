import OddMath.CoveringQuantum.UDot.TensorPresentation
import OddMath.CoveringQuantum.SerreAdd

/-!
# Connected Serre and the actual mixed tensor positive half

For the existing Delta1/Delta2 operators on the original highest/omega-lowest
quotients, toral/Koszul covariance supplies precisely the hypotheses of the
covering Serre addition formula. This proves all positive Serre relations,
including connected odd cases and arbitrary Cartan entries, as endomorphism
identities over the generic covering ring. No tensor compatibility is assumed.

The resulting positive-half algebra action descends to weight-labelled linear
maps using the existing finite projectors. Their corners, shifted multiplication,
and full projected Serre relations are proved. This is not a full CoveringUDot
tensor representation: negative/mixed relations and tensor polarization remain
separate obligations. The conventions are the accepted rho/tau1-prime with v=q^-1,
not a transport to the printed Delta3/Delta4 form.
-/

noncomputable section
namespace OddMath.CoveringQuantum.UDot.GenericVerma
open PreF Coefficients TensorProduct
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (D : RootDatum I X) (hD : D.toSuperCartanDatum.BarConsistent) (Λ Μ : X)

local instance : AddCommGroup
    (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  TensorProduct.addCommGroup

omit [DecidableEq I] [DecidableEq X] [Finite I] in
private theorem pii_shift (i j : I) (n : ℤ) :
    D.pii pi i ^ (n + D.a i j).natAbs = D.pii pi i ^ n.natAbs := by
  have h := pii_pow_sub_word D pi pi_sq i (n + D.a i j) [j]
  simp only [wordWeight_cons, wordWeight_nil, add_zero, halfWeight_single,
    halfRoot, ite_true, D.h_α, add_sub_cancel_right] at h
  exact h.symm

omit [DecidableEq I] [DecidableEq X] [Finite I] in
/-- The tilde J factor is unchanged by roots; tilde K has its exact quantum shift. -/
theorem tensorToralScalar_add_root (withJ : Bool) (i j : I) (μ : X) :
    tensorToralScalar D withJ i (μ + D.α j) =
      qp Coefficients.q (-D.dot i j) * tensorToralScalar D withJ i μ := by
  simp only [tensorToralScalar, map_add, D.h_α, pii_shift]
  rw [show -(D.d i * (D.h i μ + D.a i j)) =
    -D.dot i j + -(D.d i * D.h i μ) by simp [SuperCartanDatum.dot]; ring]
  simp only [qp, zpow_add, Units.val_mul]
  ring

/-- Exact covariance of the actual toral/Koszul operator, for arbitrary Cartan entries. -/
theorem tensorTwist_E (withJ : Bool) (i j : I)
    (x : IntegrableQuotient D hD Λ) :
    tensorTwist D hD Λ withJ i (integrableChevalley D hD Λ true j x) =
      D.chi Coefficients.q pi i j •
        integrableChevalley D hD Λ true j (tensorTwist D hD Λ withJ i x) := by
  simp only [tensorTwist, Module.End.mul_apply, integrableParity_chevalley, map_smul,
    integrableWeight_chevalley, halfRoot, ite_true, tensorToralScalar_add_root]
  have hw (f : X → Coefficients.Ring) (c : Coefficients.Ring)
      (x : IntegrableQuotient D hD Λ) :
      integrableWeight D hD Λ (fun μ ↦ c * f μ) x = c • integrableWeight D hD Λ f x := by
    induction x using integrable_induction D hD Λ with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy, smul_add]
    | smul a x hx => simp only [map_smul, hx, smul_comm a]
    | word w => simp only [integrableWeight_word, smul_smul]
  rw [hw, map_smul, smul_smul]
  simp only [SuperCartanDatum.chi_apply, qp]
  rw [mul_comm]

omit [DecidableEq I] [DecidableEq X] [Finite I] in
private theorem coveringSerre_coeff {B : Type*} [Ring B] [Algebra Coefficients.Ring B]
    (i j : I) (a b : B) :
    coveringSerre (D.qi Coefficients.q i) (D.pii pi i)
      (D.pii pi i ^ (D.parity j).val) (D.serreDeg i j) a b =
      ∑ r ∈ Finset.range (D.serreDeg i j + 1),
        D.serreCoeff Coefficients.q pi i j r • (a ^ (D.serreDeg i j - r) * b * a ^ r) := by
  unfold coveringSerre SuperCartanDatum.serreCoeff
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  rw [pow_add, ← pow_mul, mul_comm (D.parity j).val r]
  ring

private abbrev leftE (i : I) :=
  TensorProduct.map (integrableChevalley D hD Λ true i)
    (LinearMap.id : Module.End Coefficients.Ring (IntegrableQuotient D hD Μ))

private abbrev rightE (withJ : Bool) (i : I) :=
  TensorProduct.map (tensorTwist D hD Λ withJ i) (integrableChevalley D hD Μ false i)

private theorem rightE_leftE (withJ : Bool) (i j : I) :
    rightE D hD Λ Μ withJ i * leftE D hD Λ Μ j =
      D.chi Coefficients.q pi i j • (leftE D hD Λ Μ j * rightE D hD Λ Μ withJ i) := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply, Module.End.mul_apply,
    LinearMap.smul_apply, rightE, leftE, map_tmul, LinearMap.id_apply, tensorTwist_E,
    smul_tmul, tmul_smul]

omit [DecidableEq I] [DecidableEq X] [Finite I] in
private theorem chi_inv_mul (i j : I) :
    D.chi Coefficients.q⁻¹ pi i j * D.chi Coefficients.q pi j i = 1 := by
  rw [(D.chi Coefficients.q pi).comm j i]
  simp only [SuperCartanDatum.chi_apply, inv_zpow, ← zpow_neg, neg_neg]
  have hp : pi ^ (D.parity i * D.parity j).val * pi ^ (D.parity i * D.parity j).val = 1 := by
    rw [← pow_two, ← pow_mul, mul_comm _ 2, pow_mul, pi_sq, one_pow]
  calc
    _ = ((Coefficients.q ^ D.dot i j : Coefficients.Ringˣ) : Coefficients.Ring) *
        ((Coefficients.q ^ (-D.dot i j) : Coefficients.Ringˣ) : Coefficients.Ring) *
        (pi ^ (D.parity i * D.parity j).val * pi ^ (D.parity i * D.parity j).val) := by ring
    _ = 1 := by rw [hp, ← Units.val_mul, ← zpow_add]; simp

private theorem leftE_rightE (withJ : Bool) (i j : I) :
    leftE D hD Λ Μ i * rightE D hD Λ Μ withJ j =
      D.chi Coefficients.q⁻¹ pi i j • (rightE D hD Λ Μ withJ j * leftE D hD Λ Μ i) := by
  rw [rightE_leftE, smul_smul, chi_inv_mul, one_smul]

private theorem serre_leftE {i j : I} (hij : i ≠ j) :
    coveringSerre (D.qi Coefficients.q i) (D.pii pi i)
      (D.pii pi i ^ (D.parity j).val) (D.serreDeg i j)
        (leftE D hD Λ Μ i) (leftE D hD Λ Μ j) = 0 := by
  rw [coveringSerre_coeff]
  have hs := congrArg (fun f : Module.End Coefficients.Ring (IntegrableQuotient D hD Λ) ↦
    (TensorProduct.mapBilinear (RingHom.id Coefficients.Ring) _ _ _ _).flip
      (LinearMap.id : Module.End Coefficients.Ring (IntegrableQuotient D hD Μ)) f)
      (integrableChevalley_serre D hD Λ true hij)
  simpa only [leftE, TensorProduct.map_pow, ← TensorProduct.map_mul,
    show (LinearMap.id : Module.End Coefficients.Ring (IntegrableQuotient D hD Μ)) = 1 from rfl,
    one_pow, one_mul, map_sum, map_smul, map_zero, LinearMap.flip_apply,
    TensorProduct.mapBilinear_apply] using hs

private theorem serre_rightE (withJ : Bool) {i j : I} (hij : i ≠ j) :
    coveringSerre (D.qi Coefficients.q i) (D.pii pi i)
      (D.pii pi i ^ (D.parity j).val) (D.serreDeg i j)
        (rightE D hD Λ Μ withJ i) (rightE D hD Λ Μ withJ j) = 0 := by
  rw [coveringSerre_coeff]
  have ht : Commute (tensorTwist D hD Λ withJ i) (tensorTwist D hD Λ withJ j) :=
    tensorTwist_comm D hD Λ withJ i j
  simp only [rightE, TensorProduct.map_pow, ← TensorProduct.map_mul]
  have hp (r : ℕ) (hr : r ≤ D.serreDeg i j) :
      tensorTwist D hD Λ withJ i ^ (D.serreDeg i j - r) *
          tensorTwist D hD Λ withJ j * tensorTwist D hD Λ withJ i ^ r =
        tensorTwist D hD Λ withJ i ^ D.serreDeg i j * tensorTwist D hD Λ withJ j := by
    rw [mul_assoc, ← (ht.pow_left r).eq, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hr]
  simp_rw [Finset.sum_congr rfl (fun r hr ↦ congrArg
    (fun f ↦ D.serreCoeff Coefficients.q pi i j r • TensorProduct.map f
      (integrableChevalley D hD Μ false i ^ (D.serreDeg i j - r) *
        integrableChevalley D hD Μ false j * integrableChevalley D hD Μ false i ^ r))
          (hp r (Nat.le_of_lt_succ (Finset.mem_range.mp hr))))]
  have hs := congrArg (TensorProduct.mapBilinear (RingHom.id Coefficients.Ring) _ _ _ _
    (tensorTwist D hD Λ withJ i ^ D.serreDeg i j * tensorTwist D hD Λ withJ j))
      (integrableChevalley_serre D hD Μ false hij)
  simpa only [map_sum, map_smul, map_zero, TensorProduct.mapBilinear_apply] using hs

/-- The complete positive Serre relation on arbitrary actual mixed tensor vectors.
Both Delta1 and Delta2, arbitrary Cartan entries, and both pi components are retained. -/
theorem tensorE_serre (withJ : Bool) {i j : I} (hij : i ≠ j) :
    ∑ r ∈ Finset.range (D.serreDeg i j + 1),
      D.serreCoeff Coefficients.q pi i j r •
        (tensorE D hD Λ Μ withJ i ^ (D.serreDeg i j - r) *
          tensorE D hD Λ Μ withJ j * tensorE D hD Λ Μ withJ i ^ r) = 0 := by
  rw [← coveringSerre_coeff D i j (tensorE D hD Λ Μ withJ i)
    (tensorE D hD Λ Μ withJ j)]
  have hN : D.serreDeg i j - 1 + 1 = D.serreDeg i j := by
    have := D.serreDeg_eq hij
    have := D.isGCM.offDiag_nonpos i j hij
    omega
  have hs := coveringSerre_add (D.qi Coefficients.q i) (D.pii_sq pi pi_sq i)
    (c := D.pii pi i ^ (D.parity j).val)
    (u := leftE D hD Λ Μ i) (w := rightE D hD Λ Μ withJ i)
    (b := leftE D hD Λ Μ j) (b' := rightE D hD Λ Μ withJ j)
    (D.serreDeg i j - 1) (by rw [hN]; exact D.odd_serreDeg_or pi hij)
    (by simpa only [D.chi_self, mul_comm] using rightE_leftE D hD Λ Μ withJ i i)
    (by simpa only [D.chi_of_ne Coefficients.q pi hij, mul_comm]
      using rightE_leftE D hD Λ Μ withJ i j)
    (by simpa only [D.chi_of_ne Coefficients.q⁻¹ pi hij, SuperCartanDatum.qi, inv_pow,
      mul_comm] using leftE_rightE D hD Λ Μ withJ i j)
  rw [hN, serre_leftE D hD Λ Μ hij, serre_rightE D hD Λ Μ withJ hij, add_zero] at hs
  exact hs

/-- Evaluation of free positive words in the existing mixed tensor E operators. -/
def tensorPositiveFree (withJ : Bool) : PreF Coefficients.Ring I →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring
      (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  FreeAlgebra.lift Coefficients.Ring (tensorE D hD Λ Μ withJ)

@[simp] theorem tensorPositiveFree_θ (withJ : Bool) (i : I) :
    tensorPositiveFree D hD Λ Μ withJ (θ Coefficients.Ring i) =
      tensorE D hD Λ Μ withJ i := by simp [tensorPositiveFree, θ]

/-- The actual positive-half action, with Serre proved rather than assumed. -/
def tensorPositiveAction (withJ : Bool) : D.serreF Coefficients.q pi →ₐ[Coefficients.Ring]
    Module.End Coefficients.Ring
      (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  RingQuot.liftAlgHom Coefficients.Ring
    ⟨tensorPositiveFree D hD Λ Μ withJ, fun _ _ h ↦ by
      cases h with
      | serre i j hij =>
        simpa only [SuperCartanDatum.serreElt, map_sum, map_smul, map_mul, map_pow,
          tensorPositiveFree_θ, map_zero] using tensorE_serre D hD Λ Μ withJ hij⟩

@[simp] theorem tensorPositiveAction_mk (withJ : Bool) (x : PreF Coefficients.Ring I) :
    tensorPositiveAction D hD Λ Μ withJ (D.toSerreF Coefficients.q pi x) =
      tensorPositiveFree D hD Λ Μ withJ x :=
  RingQuot.liftAlgHom_mkAlgHom_apply _ _ _ x

@[simp] theorem tensorPositiveAction_θ (withJ : Bool) (i : I) :
    tensorPositiveAction D hD Λ Μ withJ (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
      tensorE D hD Λ Μ withJ i := by simp

private theorem tensorProject_word (withJ : Bool) (η : X) (w : List I) :
    tensorProject D hD Λ Μ η * tensorPositiveFree D hD Λ Μ withJ (monomial Coefficients.Ring w) =
      tensorPositiveFree D hD Λ Μ withJ (monomial Coefficients.Ring w) *
        tensorProject D hD Λ Μ (η - halfWeight D true (wordWeight w)) := by
  induction w generalizing η with
  | nil => simp
  | cons i w ih =>
    simp only [monomial_cons, map_mul, tensorPositiveFree_θ, wordWeight_cons, halfWeight_add,
      halfWeight_single, halfRoot, ite_true]
    rw [← mul_assoc, tensorProject_E, mul_assoc, ih, ← mul_assoc]
    congr 2
    abel

/-- Weight covariance of the descended half action on any homogeneous half element. -/
theorem tensorProject_positiveAction (withJ : Bool) (η : X) {ν : I →₀ ℕ}
    {x : D.serreF Coefficients.q pi} (hx : x ∈ halfWeightSpace D Coefficients.q pi ν) :
    tensorProject D hD Λ Μ η * tensorPositiveAction D hD Λ Μ withJ x =
      tensorPositiveAction D hD Λ Μ withJ x *
        tensorProject D hD Λ Μ (η - halfWeight D true ν) := by
  obtain ⟨x, hx, rfl⟩ := hx
  simp only [AlgHom.toLinearMap_apply, tensorPositiveAction_mk]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, rfl⟩ := hx
    change wordWeight w = ν at hw
    rw [← hw]
    exact tensorProject_word D hD Λ Μ withJ η w
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, mul_add, add_mul, ihx, ihy]
  | smul c x hx ih => simp only [map_smul, mul_smul_comm, smul_mul_assoc, ih]

/-- Weight-labelled positive-half map: its unit is the existing finite projector,
not the unit of the endomorphism algebra. -/
def tensorPositiveBlock (withJ : Bool) (η : X) : D.serreF Coefficients.q pi →ₗ[Coefficients.Ring]
    Module.End Coefficients.Ring
      (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) where
  toFun x := tensorPositiveAction D hD Λ Μ withJ x * tensorProject D hD Λ Μ η
  map_add' x y := by rw [map_add, add_mul]
  map_smul' c x := by rw [map_smul, smul_mul_assoc]; rfl

@[simp] theorem tensorPositiveBlock_one (withJ : Bool) (η : X) :
    tensorPositiveBlock D hD Λ Μ withJ η 1 = tensorProject D hD Λ Μ η := by
  change tensorPositiveAction D hD Λ Μ withJ 1 * _ = _
  rw [map_one, one_mul]

@[simp] theorem tensorPositiveBlock_θ (withJ : Bool) (η : X) (i : I) :
    tensorPositiveBlock D hD Λ Μ withJ η
      (D.toSerreF Coefficients.q pi (θ Coefficients.Ring i)) =
        tensorEBlock D hD Λ Μ withJ i η := by
  change tensorPositiveAction D hD Λ Μ withJ _ * _ = _
  rw [tensorPositiveAction_θ]; rfl

/-- Right corner of every, possibly inhomogeneous, descended half element. -/
theorem tensorPositiveBlock_project (withJ : Bool) (η : X) (x : D.serreF Coefficients.q pi) :
    tensorPositiveBlock D hD Λ Μ withJ η x * tensorProject D hD Λ Μ η =
      tensorPositiveBlock D hD Λ Μ withJ η x := by
  change (tensorPositiveAction D hD Λ Μ withJ x * tensorProject D hD Λ Μ η) *
    tensorProject D hD Λ Μ η = _
  rw [mul_assoc, tensorProject_mul]
  simp only [ite_true]
  rfl

/-- Left corner with the actual weight shift of a homogeneous half element. -/
theorem tensorProject_positiveBlock (withJ : Bool) (η : X) {ν : I →₀ ℕ}
    {x : D.serreF Coefficients.q pi} (hx : x ∈ halfWeightSpace D Coefficients.q pi ν) :
    tensorProject D hD Λ Μ (η + halfWeight D true ν) *
        tensorPositiveBlock D hD Λ Μ withJ η x = tensorPositiveBlock D hD Λ Μ withJ η x := by
  change tensorProject D hD Λ Μ (η + halfWeight D true ν) *
    (tensorPositiveAction D hD Λ Μ withJ x * tensorProject D hD Λ Μ η) = _
  rw [← mul_assoc, tensorProject_positiveAction D hD Λ Μ withJ _ hx,
    add_sub_cancel_right, mul_assoc, tensorProject_mul]
  simp only [ite_true]
  rfl

/-- Shifted multiplication law for the weight-labelled descent. Only the right
factor needs a degree; both operators act on arbitrary original quotient tensors. -/
theorem tensorPositiveBlock_mul (withJ : Bool) (η : X) {ν : I →₀ ℕ}
    (x : D.serreF Coefficients.q pi) {y : D.serreF Coefficients.q pi}
    (hy : y ∈ halfWeightSpace D Coefficients.q pi ν) :
    tensorPositiveBlock D hD Λ Μ withJ η (x * y) =
      tensorPositiveBlock D hD Λ Μ withJ (η + halfWeight D true ν) x *
        tensorPositiveBlock D hD Λ Μ withJ η y := by
  change tensorPositiveAction D hD Λ Μ withJ (x * y) * _ = (_ * _) * (_ * _)
  rw [map_mul]
  simp only [mul_assoc]
  exact congrArg (fun z ↦ tensorPositiveAction D hD Λ Μ withJ x * z)
    (tensorProject_positiveBlock D hD Λ Μ withJ η hy).symm

/-- Positive divided-free power with the actual finite right projector. -/
def tensorEPowBlock (withJ : Bool) (i : I) (n : ℕ) (η : X) : Module.End Coefficients.Ring
    (IntegrableQuotient D hD Λ ⊗[Coefficients.Ring] IntegrableQuotient D hD Μ) :=
  tensorE D hD Λ Μ withJ i ^ n * tensorProject D hD Λ Μ η

private theorem tensorProject_E_pow (withJ : Bool) (i : I) (n : ℕ) (η : X) :
    tensorProject D hD Λ Μ η * tensorE D hD Λ Μ withJ i ^ n =
      tensorE D hD Λ Μ withJ i ^ n * tensorProject D hD Λ Μ (η - n • D.α i) := by
  induction n generalizing η with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← mul_assoc, tensorProject_E, mul_assoc, ih, ← mul_assoc]
    congr 2
    rw [add_nsmul, one_nsmul]
    abel

@[simp] theorem tensorEPowBlock_zero (withJ : Bool) (i : I) (η : X) :
    tensorEPowBlock D hD Λ Μ withJ i 0 η = tensorProject D hD Λ Μ η := by
  simp [tensorEPowBlock]

/-- Recursion in the actual weight-labelled generators, not merely unprojected powers. -/
theorem tensorEPowBlock_succ (withJ : Bool) (i : I) (n : ℕ) (η : X) :
    tensorEPowBlock D hD Λ Μ withJ i (n + 1) η =
      tensorEBlock D hD Λ Μ withJ i (η + n • D.α i) *
        tensorEPowBlock D hD Λ Μ withJ i n η := by
  simp only [tensorEPowBlock, tensorEBlock]
  rw [mul_assoc, ← mul_assoc (tensorProject D hD Λ Μ _), tensorProject_E_pow,
    add_sub_cancel_right, mul_assoc, tensorProject_mul]
  simp only [ite_true, ← mul_assoc, pow_succ']

private theorem tensorSerreWord_block (withJ : Bool) (i j : I) (n m : ℕ) (η : X) :
    tensorEPowBlock D hD Λ Μ withJ i n (η + m • D.α i + D.α j) *
        tensorEBlock D hD Λ Μ withJ j (η + m • D.α i) *
        tensorEPowBlock D hD Λ Μ withJ i m η =
      (tensorE D hD Λ Μ withJ i ^ n * tensorE D hD Λ Μ withJ j *
        tensorE D hD Λ Μ withJ i ^ m) * tensorProject D hD Λ Μ η := by
  simp only [tensorEPowBlock, tensorEBlock]
  simp only [mul_assoc]
  rw [← mul_assoc (tensorProject D hD Λ Μ _), tensorProject_E,
    add_sub_cancel_right, mul_assoc, ← mul_assoc (tensorProject D hD Λ Μ _),
    tensorProject_mul]
  simp only [ite_true]
  rw [← mul_assoc (tensorProject D hD Λ Μ _), tensorProject_E_pow,
    add_sub_cancel_right, mul_assoc, tensorProject_mul]
  simp only [ite_true]

/-- The full weight-labelled positive Serre relation, with all prescribed intermediate
weights. It holds as an endomorphism of the original mixed tensor, in either convention. -/
theorem tensorEBlock_serre (withJ : Bool) {i j : I} (hij : i ≠ j) (η : X) :
    ∑ r ∈ Finset.range (D.serreDeg i j + 1), D.serreCoeff Coefficients.q pi i j r •
      (tensorEPowBlock D hD Λ Μ withJ i (D.serreDeg i j - r) (η + r • D.α i + D.α j) *
        tensorEBlock D hD Λ Μ withJ j (η + r • D.α i) *
        tensorEPowBlock D hD Λ Μ withJ i r η) = 0 := by
  have hs := congrArg (fun f ↦ f * tensorProject D hD Λ Μ η)
    (tensorE_serre D hD Λ Μ withJ hij)
  simpa only [tensorSerreWord_block, Finset.sum_mul, smul_mul_assoc, zero_mul] using hs

end OddMath.CoveringQuantum.UDot.GenericVerma
