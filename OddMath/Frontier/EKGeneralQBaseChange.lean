import OddMath.Frontier.EKGeneralQIdeal
import OddMath.Frontier.EKDualBases
import OddMath.Frontier.EKSignedQuotient
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# EK Corollary 2.12 over an arbitrary commutative ring: `Λ = Λ_ℤ ⊗ k`

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.2, p.15, Corollary 2.12: "`Λₙ` is a free
`k`-module, of which the families `{h_λ}_{λ⊢n}` and `{e_λ}_{λ⊢n}` are both bases. ... Now `Λ_ℤ`
is a free `ℤ`-module with the required bases, so `Λ = Λ_ℤ ⊗_ℤ k` is a free `k`-module with the
required bases."

Here `k` is an arbitrary commutative ring, `q = -1`, and `Λ_k = Lam (-1 : k)` is the quotient
of `Λ'_k` by the radical of (2.1) over `k` (`EKGeneralQIdeal`), while `Λ_ℤ` is the existing
`EKRadicalQuotient.Q` with its bases `EKIntegralBases.hBasis`, `eBasis`.

* `baseChangeEquiv : k ⊗[ℤ] Λ_ℤ ≃ₗ[k] Λ_k`, `c ⊗ x̄ ↦ c · x̄`; it is multiplicative
  (`baseChangeEquiv_mul`), so `Λ_k ≅ k ⊗ Λ_ℤ` as `k`-algebras.
* `hBasisK`, `eBasisK`: the families `h_λ = h_{λ₁}⋯h_{λ_r}` and `e_λ = e_{λ₁}⋯e_{λ_r}`
  (all partitions `λ`) are `k`-bases of `Λ_k`, with `e_n` the image of the integral `e_n`
  (defined by (2.5)).
* `degreeHBasisK`, `degree_finrank`: the degree-`n` part of `Λ_k` is free with basis `h_λ`,
  `λ ⊢ n`, of rank the number of partitions of `n`.
* `quotientForm_hBasisK`: the induced form on `Λ_k` is the base change of the integral one.
-/
noncomputable section
open scoped TensorProduct BigOperators
namespace OddMath.Frontier.EKGeneralQ
open EKFreeCoproduct (W degree partWord partWord_degree)

variable {k : Type*} [CommRing k]
attribute [local instance] Classical.propDecidable

/-! ## The comparison map `Λ'_ℤ → Λ'_k` -/

variable (k) in
/-- `Λ'_ℤ → Λ'_k`, `hₙ ↦ hₙ`. -/
def iota : L ℤ →ₐ[ℤ] L k := FreeAlgebra.lift ℤ (fun i => FreeAlgebra.ι k i)

@[simp] theorem iota_h (n : ℕ) : iota k (h ℤ n) = h k n := by
  cases n with
  | zero => simp [iota]
  | succ n => exact FreeAlgebra.lift_ι_apply _ n

theorem iota_wordBasis (w : W) : iota k (wordBasis ℤ w) = wordBasis k w := by
  induction w using FreeMonoid.recOn with
  | h0 => simp
  | ih i w ih => rw [wordBasis_mul, wordBasis_mul, map_mul, ih, wordBasis_of, wordBasis_of, iota_h]

theorem iota_hWord (β : List ℕ) : iota k (hWord ℤ β) = hWord k β := by
  simp [hWord, map_list_prod, List.map_map, Function.comp_def]

theorem form_iota_basis (v w : W) :
    form (-1 : k) (iota k (wordBasis ℤ v)) (iota k (wordBasis ℤ w)) =
      ((form (-1 : ℤ) (wordBasis ℤ v) (wordBasis ℤ w) : ℤ) : k) := by
  rw [iota_wordBasis, iota_wordBasis, form_basis_mat, form_basis_mat, matForm, matForm]
  push_cast
  rfl

theorem form_iota (x y : L ℤ) :
    form (-1 : k) (iota k x) (iota k y) = ((form (-1 : ℤ) x y : ℤ) : k) := by
  induction x using basis_induction ℤ (wordBasis ℤ) with
  | hz => simp
  | ha x z hx hz => simp only [map_add, LinearMap.add_apply, hx, hz, Int.cast_add]
  | hb v r =>
    induction y using basis_induction ℤ (wordBasis ℤ) with
    | hz => simp
    | ha y z hy hz => simp only [map_add, hy, hz, Int.cast_add]
    | hb w s =>
      rw [map_zsmul (iota k), map_zsmul (iota k), map_zsmul (form (-1 : k)), LinearMap.smul_apply,
        map_zsmul, map_zsmul (form (-1 : ℤ)), LinearMap.smul_apply, map_zsmul,
        form_iota_basis]
      simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_id]

theorem hWord_int (β : List ℕ) : hWord ℤ β = CompleteElementary.hWord β := by
  have : h ℤ = CompleteElementary.h := funext h_int
  rw [hWord, CompleteElementary.hWord, this]

/-- The integral radical maps into the radical over `k`. -/
theorem iota_radical {x : L ℤ} (hx : x ∈ EKRadicalQuotient.radical) :
    iota k x ∈ radical (-1 : k) := by
  intro y
  induction y using basis_induction k (wordBasis k) with
  | hz => simp
  | ha y z hy hz => simp only [map_add, hy, hz, add_zero]
  | hb w r =>
    rw [map_smul, ← iota_wordBasis, form_iota, form_neg_one, hx, Int.cast_zero, smul_zero]

/-- `Λ_ℤ → Λ_k`, a ring homomorphism. -/
def psiRing : EKRadicalQuotient.Q →+* Lam (-1 : k) :=
  Ideal.Quotient.lift EKRadicalQuotient.radical
    ((piQ (-1 : k)).toRingHom.comp (iota k).toRingHom)
    (fun _ hx => (piQ_eq_zero_iff _ _).mpr (iota_radical hx))

@[simp] theorem psiRing_pi (x : L ℤ) :
    psiRing (EKRadicalQuotient.pi x) = piQ (-1 : k) (iota k x) := rfl

/-- `Λ_ℤ → Λ_k` as a `ℤ`-linear map. -/
def psi : EKRadicalQuotient.Q →ₗ[ℤ] Lam (-1 : k) := (psiRing (k := k)).toIntAlgHom.toLinearMap

@[simp] theorem psi_apply (z : EKRadicalQuotient.Q) : psi (k := k) z = psiRing z := rfl

/-- The comparison map `k ⊗[ℤ] Λ_ℤ → Λ_k`, `c ⊗ x̄ ↦ c · x̄`. -/
def baseChangeMap : k ⊗[ℤ] EKRadicalQuotient.Q →ₗ[k] Lam (-1 : k) :=
  (psi (k := k)).liftBaseChange k

@[simp] theorem baseChangeMap_tmul (c : k) (z : EKRadicalQuotient.Q) :
    baseChangeMap (c ⊗ₜ[ℤ] z) = c • psiRing z := rfl

theorem hPartition_eq_pi (μ : YoungDiagram) :
    EKPartitionSpanning.hPartition μ =
      EKRadicalQuotient.pi (CompleteElementary.hWord μ.rowLens) :=
  (EKIntegralBases.pi_hWord _).symm

theorem psi_hPartition (μ : YoungDiagram) :
    psiRing (EKPartitionSpanning.hPartition μ) = piQ (-1 : k) (hWord k μ.rowLens) := by
  rw [hPartition_eq_pi, ← hWord_int, psiRing_pi, iota_hWord]

/-! ## Surjectivity -/

theorem baseChangeMap_surjective : Function.Surjective (baseChangeMap (k := k)) := by
  rw [← LinearMap.range_eq_top, baseChangeMap, LinearMap.range_liftBaseChange]
  rw [eq_top_iff]
  rintro z -
  obtain ⟨x, rfl⟩ := piQ_surjective (-1 : k) z
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x y hx hy => rw [map_add]; exact add_mem hx hy
  | hb w r =>
    rw [map_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨EKRadicalQuotient.pi (wordBasis ℤ w), ?_⟩
    simp [iota_wordBasis]

/-! ## Injectivity via dual coordinates -/

open DegreeShapes in
/-- A lift to `Λ'_ℤ` of the integral dual basis vector `m_μ` of `Λ_ℤ` (EK §3.1). -/
def mLift (μ : YoungDiagram) : L ℤ :=
  Classical.choose (EKRadicalQuotient.pi_surjective
    (EKDualBases.mBasis μ.card ⟨μ, rfl⟩ : EKRadicalQuotient.Q))

theorem pi_mLift (μ : YoungDiagram) :
    EKRadicalQuotient.pi (mLift μ) = (EKDualBases.mBasis μ.card ⟨μ, rfl⟩ : EKRadicalQuotient.Q) :=
  Classical.choose_spec (EKRadicalQuotient.pi_surjective _)

theorem pairing_hPartition_degreePiece (ν : YoungDiagram) {d : ℕ} (hd : ν.card ≠ d)
    {z : EKRadicalQuotient.Q} (hz : z ∈ EKIntegralBases.degreePiece d) :
    EKRadicalQuotient.quotientPairing (EKPartitionSpanning.hPartition ν) z = 0 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    rw [hPartition_eq_pi, EKRadicalQuotient.quotientPairing_pi,
      ← EKFreeCoproduct.partWord_value]
    apply EKSignedQuotient.pairing_degree_zero
    rw [partWord_degree, EKIntegralBases.rowLens_sum, w.2]
    exact hd
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [map_zsmul, hx, smul_zero]

theorem pairing_hPartition_mBasis (ν μ : YoungDiagram) :
    EKRadicalQuotient.quotientPairing (EKPartitionSpanning.hPartition ν)
      (EKDualBases.mBasis μ.card ⟨μ, rfl⟩ : EKRadicalQuotient.Q) = if ν = μ then 1 else 0 := by
  by_cases hd : ν.card = μ.card
  · have := EKDualBases.h_m μ.card ⟨ν, hd⟩ ⟨μ, rfl⟩
    rw [this]
    by_cases h : ν = μ
    · subst h; simp
    · rw [if_neg (fun e => h (congrArg Subtype.val e)), if_neg h]
  · rw [pairing_hPartition_degreePiece ν hd (EKDualBases.mBasis μ.card ⟨μ, rfl⟩).2, if_neg]
    rintro rfl
    exact hd rfl

variable (k) in
/-- The coordinate of `h_μ` on `Λ_k`: pairing with the image of `m_μ`. -/
def coordK (μ : YoungDiagram) : Lam (-1 : k) →ₗ[k] k :=
  (quotientForm (-1 : k)).flip (piQ (-1 : k) (iota k (mLift μ)))

theorem coordK_h (ν μ : YoungDiagram) :
    coordK k μ (piQ (-1 : k) (hWord k ν.rowLens)) = if ν = μ then 1 else 0 := by
  rw [coordK, LinearMap.flip_apply, quotientForm_pi, ← iota_hWord, form_iota, form_neg_one,
    hWord_int, ← EKRadicalQuotient.quotientPairing_pi, ← hPartition_eq_pi, pi_mLift,
    pairing_hPartition_mBasis]
  split_ifs <;> simp

theorem hFamilyK_linearIndependent :
    LinearIndependent k (fun μ : YoungDiagram => piQ (-1 : k) (hWord k μ.rowLens)) := by
  rw [linearIndependent_iff]
  intro l hl
  ext μ
  have h := congrArg (coordK k μ) hl
  rw [Finsupp.linearCombination_apply, map_finsuppSum, map_zero] at h
  simp only [map_smul, coordK_h, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
  rw [Finsupp.sum_ite_eq'] at h
  split_ifs at h with hμ
  · exact h
  · simpa using hμ

theorem baseChangeMap_basis (μ : YoungDiagram) :
    baseChangeMap ((EKIntegralBases.hBasis.baseChange k) μ) =
      piQ (-1 : k) (hWord k μ.rowLens) := by
  rw [Basis.baseChange_apply, baseChangeMap_tmul, one_smul, EKIntegralBases.hBasis_apply,
    psi_hPartition]

theorem baseChangeMap_injective : Function.Injective (baseChangeMap (k := k)) := by
  have he : baseChangeMap (k := k) =
      (Finsupp.linearCombination k (fun μ : YoungDiagram => piQ (-1 : k) (hWord k μ.rowLens))).comp
        (EKIntegralBases.hBasis.baseChange k).repr.toLinearMap := by
    apply (EKIntegralBases.hBasis.baseChange k).ext
    intro μ
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.repr_self,
      Finsupp.linearCombination_single, one_smul, baseChangeMap_basis]
  rw [he, LinearMap.coe_comp]
  exact Function.Injective.comp hFamilyK_linearIndependent
    (EKIntegralBases.hBasis.baseChange k).repr.injective

/-! ## Corollary 2.12 over `k` -/

/-- EK Corollary 2.12, last sentence: `Λ_k = Λ_ℤ ⊗_ℤ k` (any commutative ring `k`, `q = -1`). -/
def baseChangeEquiv : k ⊗[ℤ] EKRadicalQuotient.Q ≃ₗ[k] Lam (-1 : k) :=
  LinearEquiv.ofBijective baseChangeMap ⟨baseChangeMap_injective, baseChangeMap_surjective⟩

@[simp] theorem baseChangeEquiv_tmul (c : k) (x : L ℤ) :
    baseChangeEquiv (c ⊗ₜ[ℤ] EKRadicalQuotient.pi x) = c • piQ (-1 : k) (iota k x) := rfl

/-- The comparison is multiplicative, so `Λ_k ≅ k ⊗ Λ_ℤ` as `k`-algebras. -/
theorem baseChangeEquiv_mul (x y : k ⊗[ℤ] EKRadicalQuotient.Q) :
    baseChangeEquiv (x * y) = baseChangeEquiv x * baseChangeEquiv y := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, LinearEquiv.map_zero, zero_mul]
  | add a b ha hb => rw [add_mul, LinearEquiv.map_add, LinearEquiv.map_add, ha, hb, add_mul]
  | tmul a z =>
    induction y using TensorProduct.induction_on with
    | zero => rw [mul_zero, LinearEquiv.map_zero, mul_zero]
    | add c d hc hd => rw [mul_add, LinearEquiv.map_add, LinearEquiv.map_add, hc, hd, mul_add]
    | tmul b w =>
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      change baseChangeMap _ = baseChangeMap _ * baseChangeMap _
      simp only [baseChangeMap_tmul, map_mul, smul_mul_smul_comm]

theorem baseChangeEquiv_one : baseChangeEquiv (1 : k ⊗[ℤ] EKRadicalQuotient.Q) = 1 := by
  change baseChangeMap ((1 : k) ⊗ₜ[ℤ] (1 : EKRadicalQuotient.Q)) = 1
  simp

/-- EK Corollary 2.12 over `k`: `{h_λ}` is a `k`-basis of `Λ_k`. -/
def hBasisK : Basis YoungDiagram k (Lam (-1 : k)) :=
  (EKIntegralBases.hBasis.baseChange k).map baseChangeEquiv

@[simp] theorem hBasisK_apply (μ : YoungDiagram) :
    hBasisK μ = piQ (-1 : k) (hWord k μ.rowLens) := by
  rw [hBasisK, Basis.map_apply]
  exact baseChangeMap_basis μ

/-- The odd elementary function `e_n` over `k`: the image of the integral `e_n` of (2.5). -/
def eK (n : ℕ) : Lam (-1 : k) := piQ (-1 : k) (iota k (CompleteElementary.elementary n))

/-- EK Corollary 2.12 over `k`: `{e_λ}` is a `k`-basis of `Λ_k`. -/
def eBasisK : Basis YoungDiagram k (Lam (-1 : k)) :=
  (EKIntegralBases.eBasis.baseChange k).map baseChangeEquiv

@[simp] theorem eBasisK_apply (μ : YoungDiagram) :
    eBasisK μ = (μ.rowLens.map (eK (k := k))).prod := by
  rw [eBasisK, Basis.map_apply, Basis.baseChange_apply, EKIntegralBases.eBasis_apply]
  change baseChangeMap _ = _
  rw [baseChangeMap_tmul, one_smul, EKPartitionSpanning.ePartition, map_list_prod, List.map_map]
  rfl

/-- The induced form on `Λ_k` on the `h`-basis is the image of the integral one. -/
theorem quotientForm_hBasisK (μ ν : YoungDiagram) :
    quotientForm (-1 : k) (hBasisK μ) (hBasisK ν) =
      ((EKRadicalQuotient.quotientPairing (EKPartitionSpanning.hPartition μ)
        (EKPartitionSpanning.hPartition ν) : ℤ) : k) := by
  rw [hBasisK_apply, hBasisK_apply, quotientForm_pi, ← iota_hWord (k := k) μ.rowLens,
    ← iota_hWord (k := k) ν.rowLens, form_iota,
    form_neg_one, hWord_int, hWord_int, hPartition_eq_pi, hPartition_eq_pi]
  rfl

/-! ## Degree pieces -/

variable (k) in
/-- The degree-`n` part `Λ_{k,n}`: the span of the images of words of degree `n`. -/
def degreePieceK (n : ℕ) : Submodule k (Lam (-1 : k)) :=
  Submodule.span k (Set.range (fun w : {w : W // degree w = n} => piQ (-1 : k) (wordBasis k w.1)))

theorem psi_degreePiece {n : ℕ} {z : EKRadicalQuotient.Q} (hz : z ∈ EKIntegralBases.degreePiece n) :
    psiRing z ∈ degreePieceK k n := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    show psiRing (EKRadicalQuotient.pi (wordBasis ℤ w.1)) ∈ _
    rw [psiRing_pi, iota_wordBasis]
    exact Submodule.subset_span ⟨w, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [show psiRing (r • x) = r • psiRing x from (psi (k := k)).map_smul r x]
    exact Submodule.smul_of_tower_mem _ r hx

theorem degreePieceK_eq_span (n : ℕ) :
    degreePieceK k n = Submodule.span k
      (Set.range (fun μ : DegreeShapes.DegreeShape n => hBasisK (k := k) μ.val)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    have hw : EKRadicalQuotient.pi (wordBasis ℤ w.1) ∈ EKIntegralBases.partitionPiece false n := by
      rw [← EKIntegralBases.degreePiece_eq_hPartition_span]
      exact Submodule.subset_span ⟨w, rfl⟩
    have key : ∀ z ∈ EKIntegralBases.partitionPiece false n, psiRing z ∈ Submodule.span k
        (Set.range (fun μ : DegreeShapes.DegreeShape n => hBasisK (k := k) μ.val)) := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨μ, rfl⟩ := hx
        apply Submodule.subset_span
        refine ⟨μ, ?_⟩
        show hBasisK μ.val = psiRing (EKPartitionSpanning.hPartition μ.val)
        rw [hBasisK_apply, psi_hPartition]
      | zero => simp
      | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
      | smul r x _ hx =>
        rw [show psiRing (r • x) = r • psiRing x from (psi (k := k)).map_smul r x]
        exact Submodule.smul_of_tower_mem _ r hx
    have := key _ hw
    rwa [psiRing_pi, iota_wordBasis] at this
  · apply Submodule.span_le.mpr
    rintro _ ⟨μ, rfl⟩
    show hBasisK μ.val ∈ _
    rw [hBasisK_apply, ← psi_hPartition]
    apply psi_degreePiece
    rw [EKIntegralBases.degreePiece_eq_hPartition_span]
    exact Submodule.subset_span ⟨μ, rfl⟩

/-- EK Corollary 2.12 over `k`, degreewise: `Λ_{k,n}` is free with basis `h_λ`, `λ ⊢ n`. -/
def degreeHBasisK (n : ℕ) : Basis (DegreeShapes.DegreeShape n) k (degreePieceK k n) :=
  (Basis.span (hBasisK.linearIndependent.comp (fun μ : DegreeShapes.DegreeShape n => μ.val)
    Subtype.val_injective)).map (LinearEquiv.ofEq _ _ (degreePieceK_eq_span n).symm)

@[simp] theorem degreeHBasisK_apply (n : ℕ) (μ : DegreeShapes.DegreeShape n) :
    (degreeHBasisK (k := k) n μ : Lam (-1 : k)) = piQ (-1 : k) (hWord k μ.val.rowLens) := by
  simp only [degreeHBasisK, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
  exact hBasisK_apply _


theorem eBasisK_eq_psi (μ : YoungDiagram) :
    eBasisK (k := k) μ = psiRing (EKPartitionSpanning.ePartition μ) := by
  rw [eBasisK, Basis.map_apply, Basis.baseChange_apply, EKIntegralBases.eBasis_apply]
  change baseChangeMap _ = _
  rw [baseChangeMap_tmul, one_smul]

theorem psiRing_mem_span {S : Set EKRadicalQuotient.Q} {z : EKRadicalQuotient.Q}
    (hz : z ∈ Submodule.span ℤ S) : psiRing (k := k) z ∈ Submodule.span k (psiRing '' S) := by
  induction hz using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | smul r x _ hx =>
    rw [show psiRing (r • x) = r • psiRing x from (psi (k := k)).map_smul r x]
    exact Submodule.smul_of_tower_mem _ r hx

theorem degreePieceK_eq_espan (n : ℕ) :
    degreePieceK k n = Submodule.span k
      (Set.range (fun μ : DegreeShapes.DegreeShape n => eBasisK (k := k) μ.val)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    have hw : EKRadicalQuotient.pi (wordBasis ℤ w.1) ∈ EKIntegralBases.partitionPiece true n := by
      rw [← EKIntegralBases.degreePiece_eq_ePartition_span]
      exact Submodule.subset_span ⟨w, rfl⟩
    have := psiRing_mem_span (k := k) hw
    rw [psiRing_pi, iota_wordBasis] at this
    refine Submodule.span_le.mpr ?_ this
    rintro _ ⟨_, ⟨μ, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨μ, ?_⟩
    show eBasisK μ.val = _
    rw [eBasisK_eq_psi]
    rfl
  · apply Submodule.span_le.mpr
    rintro _ ⟨μ, rfl⟩
    show eBasisK μ.val ∈ _
    rw [eBasisK_eq_psi]
    apply psi_degreePiece
    rw [EKIntegralBases.degreePiece_eq_ePartition_span]
    exact Submodule.subset_span ⟨μ, rfl⟩

/-- EK Corollary 2.12 over `k`, degreewise: `Λ_{k,n}` is free with basis `e_λ`, `λ ⊢ n`. -/
def degreeEBasisK (n : ℕ) : Basis (DegreeShapes.DegreeShape n) k (degreePieceK k n) :=
  (Basis.span (eBasisK.linearIndependent.comp (fun μ : DegreeShapes.DegreeShape n => μ.val)
    Subtype.val_injective)).map (LinearEquiv.ofEq _ _ (degreePieceK_eq_espan n).symm)

@[simp] theorem degreeEBasisK_apply (n : ℕ) (μ : DegreeShapes.DegreeShape n) :
    (degreeEBasisK (k := k) n μ : Lam (-1 : k)) = (μ.val.rowLens.map (eK (k := k))).prod := by
  simp only [degreeEBasisK, Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
  exact eBasisK_apply _

attribute [local instance] DegreeShapes.degreeFintype in
/-- The rank of `Λ_{k,n}` is the number of partitions of `n` (as for `q = 1`). -/
theorem degree_finrank [Nontrivial k] (n : ℕ) :
    Module.finrank k (degreePieceK k n) = Fintype.card (DegreeShapes.DegreeShape n) :=
  Module.finrank_eq_card_basis (degreeHBasisK n)

end OddMath.Frontier.EKGeneralQ
