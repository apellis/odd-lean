import OddMath.Frontier.EKOverKStructure

/-!
# EK Proposition 2.17 over an arbitrary commutative ring: the Hopf superalgebra `Λ_k`

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.1 p. 5 (`q`-Hopf algebras), Cor. 2.4 (p. 8),
Prop. 2.17 (p. 20).  `k` is an arbitrary commutative ring, `q = -1`.

`lambdaKHopf : EKComplete.QHopfAlgebra k (-1) Λ_k` bundles, over `k`:
* the grading `Λ_k = ⊕_d Λ_{k,d}` (`uniqueDecompositionK`), with graded unit and product;
* the twisted product `(x₁ ⊗ x₂)(y₁ ⊗ y₂) = (-1)^{deg x₂ deg y₁} x₁y₁ ⊗ x₂y₂` on homogeneous
  tensors (`tensorMulK_homogeneous`);
* the graded coassociative counital coproduct of Cor. 2.4, multiplicative for the twisted
  product; the counit, an algebra map vanishing in positive degree;
* the graded antipode `S = ψ₁ψ₂ψ₃` with both antipode identities.

`proposition_2_17_K` states the bundle together with `S = ψ₁ψ₂ψ₃`, associativity and
unitality of the twisted product, super anti-multiplicativity of `S`, and `S(1) = 1`.
(`S² ≠ 1` needs `2 ≠ 0` in `k`; see `EKOverKChar2`.)
-/

noncomputable section
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct BigOperators

namespace OddMath.Frontier.EKOverK
open EKGeneralQ

variable {k : Type*} [CommRing k]

/-! ## The grading -/

theorem one_mem_degreePieceK : (1 : LamK k) ∈ degreePieceK k 0 := by
  rw [← map_one (psiRing (k := k))]
  exact psi_degreePiece EKIntegralBases.unit_mem_degree_zero

theorem mul_mem_degreePieceK {a b : ℕ} {x y : LamK k} (hx : x ∈ degreePieceK k a)
    (hy : y ∈ degreePieceK k b) : x * y ∈ degreePieceK k (a + b) := by
  refine degreePieceK_induction (P := fun x => x * y ∈ degreePieceK k (a + b)) ?_ ?_ ?_ hx
  · simp
  · intro x x' hx hx'; rw [add_mul]; exact add_mem hx hx'
  · intro c z hz
    refine degreePieceK_induction (P := fun y => c • psiRing z * y ∈ degreePieceK k (a + b))
      ?_ ?_ ?_ hy
    · simp
    · intro y y' hy hy'; rw [mul_add]; exact add_mem hy hy'
    · intro c' z' hz'
      rw [smul_mul_smul_comm, ← map_mul]
      exact Submodule.smul_mem _ _ (psi_degreePiece (EKIntegralBases.degreePiece_mul hz hz'))

theorem hBasisK_mem (μ : YoungDiagram) : hBasisK (k := k) μ ∈ degreePieceK k μ.card := by
  rw [degreePieceK_eq_span]
  exact Submodule.subset_span ⟨⟨μ, rfl⟩, rfl⟩

/-- The homogeneous decomposition of `Λ_k`, by collecting `h`-basis coordinates by degree. -/
def decomposeK : LamK k →ₗ[k] (ℕ →₀ LamK k) :=
  (hBasisK (k := k)).constr k (fun μ => Finsupp.single μ.card (hBasisK μ))

@[simp] theorem decomposeK_hBasisK (μ : YoungDiagram) :
    decomposeK (hBasisK (k := k) μ) = Finsupp.single μ.card (hBasisK μ) :=
  (hBasisK (k := k)).constr_basis k _ μ

theorem decomposeK_piece {d : ℕ} {x : LamK k} (hx : x ∈ degreePieceK k d) :
    decomposeK x = Finsupp.single d x := by
  rw [degreePieceK_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, rfl⟩ := hx
    change decomposeK (hBasisK μ.val) = Finsupp.single d (hBasisK μ.val)
    rw [decomposeK_hBasisK, μ.property]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, Finsupp.single_add]
  | smul r x _ hx => simp only [map_smul, hx, Finsupp.smul_single]

theorem decomposeK_mem (x : LamK k) (d : ℕ) : decomposeK x d ∈ degreePieceK k d := by
  classical
  induction x using basis_induction k (hBasisK (k := k)) with
  | hz => simp
  | ha x y hx hy => simpa using (degreePieceK k d).add_mem hx hy
  | hb μ r =>
    simp only [map_smul, decomposeK_hBasisK, Finsupp.smul_apply]
    apply Submodule.smul_mem
    by_cases hd : μ.card = d
    · subst d
      rw [Finsupp.single_eq_same]
      exact hBasisK_mem μ
    · rw [Finsupp.single_eq_of_ne hd]
      exact Submodule.zero_mem _

theorem sum_decomposeK (x : LamK k) : (decomposeK x).sum (fun _ y => y) = x := by
  have he : (Finsupp.lsum k (fun _ => LinearMap.id)).comp decomposeK =
      (LinearMap.id : LamK k →ₗ[k] LamK k) := by
    apply (hBasisK (k := k)).ext
    intro μ
    simp only [LinearMap.coe_comp, Function.comp_apply, decomposeK_hBasisK,
      Finsupp.lsum_single, LinearMap.id_apply]
  exact LinearMap.congr_fun he x

theorem decomposeK_sum (f : ℕ →₀ LamK k) (hf : ∀ d, f d ∈ degreePieceK k d) :
    decomposeK (f.sum (fun _ x => x)) = f := by
  classical
  simp only [Finsupp.sum, map_sum]
  calc
    ∑ d ∈ f.support, decomposeK (f d) = ∑ d ∈ f.support, Finsupp.single d (f d) := by
      apply Finset.sum_congr rfl
      intro d _
      exact decomposeK_piece (hf d)
    _ = f := Finsupp.sum_single f

/-- `Λ_k = ⊕_d Λ_{k,d}`: existence and uniqueness of the homogeneous decomposition. -/
theorem uniqueDecompositionK (x : LamK k) :
    ∃! f : ℕ →₀ LamK k, (∀ d, f d ∈ degreePieceK k d) ∧ f.sum (fun _ y => y) = x := by
  refine ⟨decomposeK x, ⟨decomposeK_mem x, sum_decomposeK x⟩, ?_⟩
  intro f hf
  rw [← hf.2, decomposeK_sum f hf.1]

/-! ## The twisted product on homogeneous tensors -/

theorem tensorMulK_psi {a b c d : ℕ} {x y z t : QZ}
    (hx : x ∈ EKIntegralBases.degreePiece a) (hy : y ∈ EKIntegralBases.degreePiece b)
    (hz : z ∈ EKIntegralBases.degreePiece c) (ht : t ∈ EKIntegralBases.degreePiece d) :
    quotientTensorMul (-1 : k) (psiRing x ⊗ₜ[k] psiRing y) (psiRing z ⊗ₜ[k] psiRing t) =
      ((-1 : k) ^ (b * c)) • ((psiRing x * psiRing z) ⊗ₜ[k] (psiRing y * psiRing t)) := by
  rw [← psiT_tmul, ← psiT_tmul, tensorMulK_psiT, EKAutomorphisms.tensorMul_homogeneous hx hy hz ht,
    map_zsmul, psiT_tmul, map_mul, map_mul, ← Int.cast_smul_eq_zsmul k]
  push_cast; rfl

/-- EK p. 5 on `Λ_k ⊗ Λ_k`: `(x ⊗ y)(z ⊗ t) = (-1)^{deg y deg z} xz ⊗ yt` for homogeneous
`x, y, z, t`. -/
theorem tensorMulK_homogeneous {a b c d : ℕ} {x y z t : LamK k}
    (hx : x ∈ degreePieceK k a) (hy : y ∈ degreePieceK k b)
    (hz : z ∈ degreePieceK k c) (ht : t ∈ degreePieceK k d) :
    quotientTensorMul (-1 : k) (x ⊗ₜ[k] y) (z ⊗ₜ[k] t) =
      ((-1 : k) ^ (b * c)) • ((x * z) ⊗ₜ[k] (y * t)) := by
  -- extend one variable at a time from images of `Λ_ℤ`
  have h1 : ∀ {x : LamK k}, x ∈ degreePieceK k a → ∀ {y' z' t' : QZ},
      y' ∈ EKIntegralBases.degreePiece b → z' ∈ EKIntegralBases.degreePiece c →
      t' ∈ EKIntegralBases.degreePiece d →
      quotientTensorMul (-1 : k) (x ⊗ₜ[k] psiRing y') (psiRing z' ⊗ₜ[k] psiRing t') =
        ((-1 : k) ^ (b * c)) • ((x * psiRing z') ⊗ₜ[k] (psiRing y' * psiRing t')) := by
    intro x hx y' z' t' hy' hz' ht'
    refine degreePieceK_induction (P := fun x =>
      quotientTensorMul (-1 : k) (x ⊗ₜ[k] psiRing y') (psiRing z' ⊗ₜ[k] psiRing t') =
        ((-1 : k) ^ (b * c)) • ((x * psiRing z') ⊗ₜ[k] (psiRing y' * psiRing t'))) ?_ ?_ ?_ hx
    · simp
    · intro u v hu hv
      rw [TensorProduct.add_tmul, map_add, LinearMap.add_apply, hu, hv, add_mul,
        TensorProduct.add_tmul, smul_add]
    · intro e w hw
      rw [← TensorProduct.smul_tmul', map_smul, LinearMap.smul_apply, tensorMulK_psi hw hy' hz' ht',
        smul_mul_assoc, ← TensorProduct.smul_tmul', smul_comm]
  have h2 : ∀ {x y : LamK k}, x ∈ degreePieceK k a → y ∈ degreePieceK k b → ∀ {z' t' : QZ},
      z' ∈ EKIntegralBases.degreePiece c → t' ∈ EKIntegralBases.degreePiece d →
      quotientTensorMul (-1 : k) (x ⊗ₜ[k] y) (psiRing z' ⊗ₜ[k] psiRing t') =
        ((-1 : k) ^ (b * c)) • ((x * psiRing z') ⊗ₜ[k] (y * psiRing t')) := by
    intro x y hx hy z' t' hz' ht'
    refine degreePieceK_induction (P := fun y =>
      quotientTensorMul (-1 : k) (x ⊗ₜ[k] y) (psiRing z' ⊗ₜ[k] psiRing t') =
        ((-1 : k) ^ (b * c)) • ((x * psiRing z') ⊗ₜ[k] (y * psiRing t'))) ?_ ?_ ?_ hy
    · simp
    · intro u v hu hv
      rw [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hu, hv, add_mul,
        TensorProduct.tmul_add, smul_add]
    · intro e w hw
      rw [TensorProduct.tmul_smul, map_smul, LinearMap.smul_apply, h1 hx hw hz' ht',
        smul_mul_assoc, TensorProduct.tmul_smul, smul_comm]
  have h3 : ∀ {x y z : LamK k}, x ∈ degreePieceK k a → y ∈ degreePieceK k b →
      z ∈ degreePieceK k c → ∀ {t' : QZ}, t' ∈ EKIntegralBases.degreePiece d →
      quotientTensorMul (-1 : k) (x ⊗ₜ[k] y) (z ⊗ₜ[k] psiRing t') =
        ((-1 : k) ^ (b * c)) • ((x * z) ⊗ₜ[k] (y * psiRing t')) := by
    intro x y z hx hy hz t' ht'
    refine degreePieceK_induction (P := fun z =>
      quotientTensorMul (-1 : k) (x ⊗ₜ[k] y) (z ⊗ₜ[k] psiRing t') =
        ((-1 : k) ^ (b * c)) • ((x * z) ⊗ₜ[k] (y * psiRing t'))) ?_ ?_ ?_ hz
    · simp
    · intro u v hu hv
      rw [TensorProduct.add_tmul, map_add, hu, hv, mul_add, TensorProduct.add_tmul, smul_add]
    · intro e w hw
      rw [← TensorProduct.smul_tmul', map_smul, h2 hx hy hw ht', mul_smul_comm,
        ← TensorProduct.smul_tmul', smul_comm]
  refine degreePieceK_induction (P := fun t =>
    quotientTensorMul (-1 : k) (x ⊗ₜ[k] y) (z ⊗ₜ[k] t) =
      ((-1 : k) ^ (b * c)) • ((x * z) ⊗ₜ[k] (y * t))) ?_ ?_ ?_ ht
  · simp
  · intro u v hu hv
    rw [TensorProduct.tmul_add, map_add, hu, hv, mul_add, TensorProduct.tmul_add, smul_add]
  · intro e w hw
    rw [TensorProduct.tmul_smul, map_smul, h3 hx hy hz hw, mul_smul_comm,
      TensorProduct.tmul_smul, smul_comm]

/-! ## Gradedness of the coproduct, the counit and the antipode -/

theorem psiT_tensorPiece {d : ℕ} {u : QZ ⊗[ℤ] QZ}
    (hu : u ∈ EKComplete.tensorPiece EKIntegralBases.degreePiece d) :
    psiT k u ∈ EKComplete.tensorPiece (degreePieceK k) d := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, b, y, z, hab, hy, hz, rfl⟩ := hu
    exact Submodule.subset_span ⟨a, b, _, _, hab, psi_degreePiece hy, psi_degreePiece hz, rfl⟩
  | zero => simp
  | add u v _ _ hu hv => rw [map_add]; exact add_mem hu hv
  | smul c u _ hu =>
    rw [map_zsmul]
    exact Submodule.smul_of_tower_mem _ c hu

theorem coproductK_mem {d : ℕ} {x : LamK k} (hx : x ∈ degreePieceK k d) :
    coproductK x ∈ EKComplete.tensorPiece (degreePieceK k) d := by
  refine degreePieceK_induction
    (P := fun x => coproductK x ∈ EKComplete.tensorPiece (degreePieceK k) d) ?_ ?_ ?_ hx
  · simp
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro c z hz
    rw [map_smul, coproductK_psiRing]
    exact Submodule.smul_mem _ c (psiT_tensorPiece (EKComplete.coproduct_mem_tensorPiece hz))

theorem counitK_mem {d : ℕ} {x : LamK k} (hd : 0 < d) (hx : x ∈ degreePieceK k d) :
    quotientCounit (-1 : k) x = 0 := by
  refine degreePieceK_induction (P := fun x => quotientCounit (-1 : k) x = 0) ?_ ?_ ?_ hx
  · simp
  · intro x y hx hy; rw [map_add, hx, hy, add_zero]
  · intro c z hz
    rw [map_smul, counitK_psiRing, EKAutomorphisms.counit_positive (Nat.pos_iff_ne_zero.mp hd) hz]
    simp

/-! ## The bundled Hopf superalgebra -/

variable (k) in
/-- **EK Cor. 2.4 and Prop. 2.17 over `k`**: `Λ_k` is a `(-1)`-Hopf algebra (a `ℤ`-graded
Hopf superalgebra), with antipode `S = ψ₁ψ₂ψ₃`. -/
def lambdaKHopf : EKComplete.QHopfAlgebra k (-1) (LamK k) where
  piece := degreePieceK k
  decomposition := uniqueDecompositionK
  one_mem := one_mem_degreePieceK
  mul_mem := mul_mem_degreePieceK
  tensorMul := quotientTensorMul (-1 : k)
  tensorMul_tmul := tensorMulK_homogeneous
  comul := coproductK
  counit := quotientCounit (-1 : k)
  comul_mem := coproductK_mem
  counit_mem := counitK_mem
  coassoc := sep_coassociativity separating_neg_one
  counit_left := sep_counit_left separating_neg_one
  counit_right := sep_counit_right separating_neg_one
  comul_one := sep_coproduct_one separating_neg_one
  comul_mul := sep_coproduct_mul separating_neg_one
  antipode := SK k
  antipode_mem := SK_degree
  antipode_left := SK_convolution_left
  antipode_right := SK_convolution_right

/-- **EK Prop. 2.17 over every commutative ring `k`, bundled.** `Λ_k` carries the
`(-1)`-Hopf algebra structure `lambdaKHopf k` whose coproduct and counit are those of
Cor. 2.4 over `k` and whose antipode is `S = ψ₁ψ₂ψ₃`; the twisted product on `Λ_k ⊗ Λ_k` is
associative and unital; `S` is a super anti-homomorphism with `S(1) = 1`; and the whole
structure is the base change of the integral one (`coproductK_psiRing`, `counitK_psiRing`,
`SK_psiRing`). -/
theorem proposition_2_17_K :
    (lambdaKHopf k).piece = degreePieceK k ∧
    (lambdaKHopf k).comul = coproductK ∧
    (lambdaKHopf k).counit = quotientCounit (-1 : k) ∧
    (∀ x, (lambdaKHopf k).antipode x = psi1K k (psi2K k (psi3K k x))) ∧
    (∀ u v w, (lambdaKHopf k).tensorMul ((lambdaKHopf k).tensorMul u v) w =
      (lambdaKHopf k).tensorMul u ((lambdaKHopf k).tensorMul v w)) ∧
    (∀ u, (lambdaKHopf k).tensorMul ((1 : LamK k) ⊗ₜ[k] (1 : LamK k)) u = u ∧
      (lambdaKHopf k).tensorMul u ((1 : LamK k) ⊗ₜ[k] (1 : LamK k)) = u) ∧
    (∀ {a b : ℕ} {x y : LamK k}, x ∈ degreePieceK k a → y ∈ degreePieceK k b →
      (lambdaKHopf k).antipode (x * y) =
        ((-1 : k) ^ (a * b)) • ((lambdaKHopf k).antipode y * (lambdaKHopf k).antipode x)) ∧
    (lambdaKHopf k).antipode 1 = 1 ∧
    (∀ z : QZ, (lambdaKHopf k).comul (psiRing z) = psiT k (EKCoideal.quotientCoproduct z)) ∧
    (∀ z : QZ, (lambdaKHopf k).antipode (psiRing z) = psiRing (EKAntipode.S z)) :=
  ⟨rfl, rfl, rfl, SK_apply, quotientTensorMul_assoc (-1 : k),
    fun u => ⟨quotientTensorMul_one_left (-1 : k) u, quotientTensorMul_one_right (-1 : k) u⟩,
    fun hx hy => SK_mul hx hy, SK_one, coproductK_psiRing, SK_psiRing⟩

end OddMath.Frontier.EKOverK
