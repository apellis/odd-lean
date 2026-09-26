import OddMath.Frontier.EKFinalBaseChange
import OddMath.Frontier.EKCompleteHopf

/-!
# EK over an arbitrary commutative ring: transport from `Λ_ℤ` to `Λ_k`

Source: Ellis–Khovanov, arXiv:1107.5610v2.  From p. 5 on, `k` is an arbitrary commutative
ring; from §2.2 on, `q = -1`.  Corollary 2.12 (p. 15) gives `Λ_k = Λ_ℤ ⊗_ℤ k`
(`EKFinal.baseChangeAlgEquiv`).

Here `Λ_k = EKGeneralQ.Lam (-1 : k)` and `Λ_ℤ = EKRadicalQuotient.Q`; the comparison ring map is
`EKGeneralQ.psiRing : Λ_ℤ → Λ_k`, `h_n ↦ h_n`.

General transport lemmas:

* `psiRing_span`: the images of `Λ_ℤ` span `Λ_k` over `k`; hence `linearMap_ext`,
  `bilinear_ext`: `k`-(bi)linear maps out of `Λ_k` are determined on images of `Λ_ℤ`;
* `bcLin f`: the `k`-linear base change `id_k ⊗ f` of a `ℤ`-linear `f : Λ_ℤ → Λ_ℤ`, with
  `bcLin_psiRing`, `bcLin_comp`, `bcLin_id`, and transfer of multiplicativity
  (`bcLin_mul`) and of super anti-multiplicativity on homogeneous elements
  (`bcLin_superAnti`);
* `bcAlg f`, `bcEquiv f`: the `k`-algebra base change of a ring endomorphism (automorphism) of
  `Λ_ℤ`, and `bcHom : (Λ_ℤ ≃+* Λ_ℤ) →* (Λ_k ≃ₐ[k] Λ_k)`;
* `psiT : Λ_ℤ ⊗ Λ_ℤ → Λ_k ⊗ Λ_k` and the compatibility of the coproduct (Corollary 2.4)
  with base change, `coproductK_psiRing`; compatibility of the counit (`counitK_psiRing`) and
  of the twisted product on `Λ ⊗ Λ` (`tensorMulK_psiT`);
* `bcChar χ`: the base change `Λ_k → k` of a character `χ : Λ_ℤ → ℤ`.
-/

noncomputable section
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct BigOperators

namespace OddMath.Frontier.EKOverK
open EKGeneralQ

variable {k : Type*} [CommRing k]

/-- `Λ_ℤ`, the integral form of EK's `Λ` (`q = -1`). -/
abbrev QZ := EKRadicalQuotient.Q

/-- `Λ_k`, EK's `Λ` over `k` (`q = -1`). -/
abbrev LamK (k : Type*) [CommRing k] := Lam (-1 : k)

/-! ## Spanning by images of `Λ_ℤ` -/

theorem baseChangeEquiv_symm_psiRing (z : QZ) :
    (baseChangeEquiv (k := k)).symm (psiRing z) = (1 : k) ⊗ₜ[ℤ] z := by
  rw [LinearEquiv.symm_apply_eq]
  change psiRing z = baseChangeMap ((1 : k) ⊗ₜ[ℤ] z)
  rw [baseChangeMap_tmul, one_smul]

theorem baseChangeAlgEquiv_symm_psiRing (z : QZ) :
    (EKFinal.baseChangeAlgEquiv k).symm (psiRing z) = (1 : k) ⊗ₜ[ℤ] z :=
  baseChangeEquiv_symm_psiRing z

/-- Induction principle: a property of `Λ_k` closed under `0`, `+`, and holding on
`c • ψ(z)` holds everywhere. -/
theorem induction_psi {P : LamK k → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hsm : ∀ (c : k) (z : QZ), P (c • psiRing z)) (x : LamK k) : P x := by
  obtain ⟨t, rfl⟩ := (baseChangeEquiv (k := k)).surjective x
  induction t using TensorProduct.induction_on with
  | zero => rw [LinearEquiv.map_zero]; exact h0
  | tmul c z =>
    change P (baseChangeMap (c ⊗ₜ[ℤ] z))
    rw [baseChangeMap_tmul]; exact hsm c z
  | add a b ha hb => rw [LinearEquiv.map_add]; exact hadd _ _ ha hb

theorem psiRing_span : Submodule.span k (Set.range (psiRing (k := k))) = ⊤ := by
  rw [eq_top_iff]
  intro x hx
  clear hx
  induction x using induction_psi with
  | h0 => exact Submodule.zero_mem _
  | hadd x y hx hy => exact add_mem hx hy
  | hsm c z => exact Submodule.smul_mem _ c (Submodule.subset_span ⟨z, rfl⟩)

theorem linearMap_ext {M : Type*} [AddCommGroup M] [Module k M] {F G : LamK k →ₗ[k] M}
    (h : ∀ z : QZ, F (psiRing z) = G (psiRing z)) : F = G := by
  refine LinearMap.ext fun x => ?_
  induction x using induction_psi with
  | h0 => simp
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]
  | hsm c z => rw [map_smul, map_smul, h]

theorem bilinear_ext {M : Type*} [AddCommGroup M] [Module k M]
    {F G : LamK k →ₗ[k] LamK k →ₗ[k] M}
    (h : ∀ y z : QZ, F (psiRing y) (psiRing z) = G (psiRing y) (psiRing z)) : F = G := by
  apply linearMap_ext
  intro y
  apply linearMap_ext
  intro z
  exact h y z

theorem psiRing_zsmul (c : ℤ) (z : QZ) : psiRing (k := k) (c • z) = (c : k) • psiRing z := by
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul k]

/-! ## Degree pieces -/

/-- `Λ_{k,d}` is the `k`-span of the image of `Λ_{ℤ,d}`. -/
theorem degreePieceK_eq_span_psi (d : ℕ) :
    degreePieceK k d =
      Submodule.span k (psiRing '' (EKIntegralBases.degreePiece d : Set QZ)) := by
  apply le_antisymm
  · rw [degreePieceK_eq_span, Submodule.span_le]
    rintro _ ⟨μ, rfl⟩
    apply Submodule.subset_span
    refine ⟨EKPartitionSpanning.hPartition μ.val, ?_, ?_⟩
    · rw [EKIntegralBases.degreePiece_eq_hPartition_span]
      exact Submodule.subset_span ⟨μ, rfl⟩
    · show psiRing _ = hBasisK μ.val
      rw [hBasisK_apply, psi_hPartition]
  · rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact psi_degreePiece hz

theorem degreePieceK_induction {d : ℕ} {P : LamK k → Prop} (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hsm : ∀ (c : k) (z : QZ), z ∈ EKIntegralBases.degreePiece d → P (c • psiRing z))
    {x : LamK k} (hx : x ∈ degreePieceK k d) : P x := by
  rw [degreePieceK_eq_span_psi, Submodule.mem_span_set'] at hx
  obtain ⟨n, f, g, rfl⟩ := hx
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    rw [Fin.sum_univ_succ]
    apply hadd
    · obtain ⟨z, hz, hzg⟩ := (g 0).2
      rw [← hzg]
      exact hsm _ z hz
    · exact ih (fun i => f i.succ) (fun i => g i.succ)

/-! ## Base change of `ℤ`-linear endomorphisms -/

variable (k) in
/-- The base change `id_k ⊗ f : Λ_k → Λ_k` of a `ℤ`-linear map `f : Λ_ℤ → Λ_ℤ`. -/
def bcLin (f : QZ →ₗ[ℤ] QZ) : LamK k →ₗ[k] LamK k :=
  ((baseChangeEquiv (k := k)).toLinearMap ∘ₗ f.baseChange k) ∘ₗ
    (baseChangeEquiv (k := k)).symm.toLinearMap

@[simp] theorem bcLin_psiRing (f : QZ →ₗ[ℤ] QZ) (z : QZ) :
    bcLin k f (psiRing z) = psiRing (f z) := by
  simp only [bcLin, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    baseChangeEquiv_symm_psiRing, LinearMap.baseChange_tmul]
  change baseChangeMap _ = _
  rw [baseChangeMap_tmul, one_smul]

theorem bcLin_comp (f g : QZ →ₗ[ℤ] QZ) : bcLin k (f ∘ₗ g) = bcLin k f ∘ₗ bcLin k g :=
  linearMap_ext fun z => by simp

theorem bcLin_id : bcLin k (LinearMap.id : QZ →ₗ[ℤ] QZ) = LinearMap.id :=
  linearMap_ext fun z => by simp

theorem bcLin_apply_apply (f g : QZ →ₗ[ℤ] QZ) (x : LamK k) :
    bcLin k f (bcLin k g x) = bcLin k (f ∘ₗ g) x := by
  rw [bcLin_comp]; rfl

/-- If `f ∘ g = id` over `ℤ`, then the same holds over `k`. -/
theorem bcLin_leftInverse {f g : QZ →ₗ[ℤ] QZ} (h : ∀ z, f (g z) = z) (x : LamK k) :
    bcLin k f (bcLin k g x) = x := by
  rw [bcLin_apply_apply]
  have : f ∘ₗ g = LinearMap.id := LinearMap.ext h
  rw [this, bcLin_id]; rfl

/-- The multiplication of `Λ_k`, as a bilinear map. -/
abbrev mulK : LamK k →ₗ[k] LamK k →ₗ[k] LamK k := LinearMap.mul k (LamK k)

/-- Multiplicativity transfers along base change. -/
theorem bcLin_mul {f : QZ →ₗ[ℤ] QZ} (hf : ∀ x y, f (x * y) = f x * f y) (a b : LamK k) :
    bcLin k f (a * b) = bcLin k f a * bcLin k f b := by
  have h := bilinear_ext (M := LamK k)
    (F := (mulK (k := k)).compr₂ (bcLin k f))
    (G := (mulK (k := k)).compl₁₂ (bcLin k f) (bcLin k f)) (fun y z => by
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply',
        ← map_mul, bcLin_psiRing, hf])
  exact LinearMap.congr_fun₂ h a b

/-- Anti-multiplicativity transfers along base change. -/
theorem bcLin_anti {f : QZ →ₗ[ℤ] QZ} (hf : ∀ x y, f (x * y) = f y * f x) (a b : LamK k) :
    bcLin k f (a * b) = bcLin k f b * bcLin k f a := by
  have h := bilinear_ext (M := LamK k)
    (F := (mulK (k := k)).compr₂ (bcLin k f))
    (G := ((mulK (k := k)).flip).compl₁₂ (bcLin k f) (bcLin k f)) (fun y z => by
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.flip_apply,
        LinearMap.mul_apply', ← map_mul, bcLin_psiRing, hf])
  exact LinearMap.congr_fun₂ h a b

/-- Degree preservation transfers along base change. -/
theorem bcLin_degree {f : QZ →ₗ[ℤ] QZ}
    (hf : ∀ {d : ℕ} {z : QZ}, z ∈ EKIntegralBases.degreePiece d → f z ∈ EKIntegralBases.degreePiece d)
    {d : ℕ} {x : LamK k} (hx : x ∈ degreePieceK k d) : bcLin k f x ∈ degreePieceK k d := by
  refine degreePieceK_induction (P := fun x => bcLin k f x ∈ degreePieceK k d) ?_ ?_ ?_ hx
  · simp
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro c z hz
    rw [map_smul, bcLin_psiRing]
    exact Submodule.smul_mem _ c (psi_degreePiece (hf hz))

/-- Super anti-multiplicativity on homogeneous elements transfers along base change. -/
theorem bcLin_superAnti {f : QZ →ₗ[ℤ] QZ}
    (hf : ∀ {a b : ℕ} {x y : QZ}, x ∈ EKIntegralBases.degreePiece a →
      y ∈ EKIntegralBases.degreePiece b → f (x * y) = (-1 : ℤ) ^ (a * b) • (f y * f x))
    {a b : ℕ} {x y : LamK k} (hx : x ∈ degreePieceK k a) (hy : y ∈ degreePieceK k b) :
    bcLin k f (x * y) = ((-1 : k) ^ (a * b)) • (bcLin k f y * bcLin k f x) := by
  refine degreePieceK_induction (P := fun x => bcLin k f (x * y) =
    ((-1 : k) ^ (a * b)) • (bcLin k f y * bcLin k f x)) ?_ ?_ ?_ hx
  · simp
  · intro x x' hx hx'; rw [add_mul, map_add, hx, hx', map_add, mul_add, smul_add]
  · intro c z hz
    refine degreePieceK_induction (P := fun y => bcLin k f (c • psiRing z * y) =
      ((-1 : k) ^ (a * b)) • (bcLin k f y * bcLin k f (c • psiRing z))) ?_ ?_ ?_ hy
    · simp
    · intro y y' hy hy'; rw [mul_add, map_add, hy, hy', map_add, add_mul, smul_add]
    · intro c' z' hz'
      rw [smul_mul_smul_comm, map_smul, ← map_mul, bcLin_psiRing, hf hz hz', psiRing_zsmul,
        map_mul, map_smul, map_smul, bcLin_psiRing, bcLin_psiRing, smul_mul_smul_comm,
        smul_smul, smul_smul]
      congr 1
      push_cast
      ring

/-! ## Base change of ring endomorphisms and automorphisms -/

variable (k) in
/-- The `k`-algebra base change of a ring endomorphism of `Λ_ℤ`. -/
def bcAlg (f : QZ →+* QZ) : LamK k →ₐ[k] LamK k :=
  (EKFinal.baseChangeAlgEquiv k).toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id k k) f.toIntAlgHom).comp
      (EKFinal.baseChangeAlgEquiv k).symm.toAlgHom)

@[simp] theorem bcAlg_psiRing (f : QZ →+* QZ) (z : QZ) :
    bcAlg k f (psiRing z) = psiRing (f z) := by
  simp only [bcAlg, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
    baseChangeAlgEquiv_symm_psiRing, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    RingHom.toIntAlgHom_apply, EKFinal.baseChangeAlgEquiv_tmul, one_smul]

theorem algHom_ext {F G : LamK k →ₐ[k] LamK k} (h : ∀ z : QZ, F (psiRing z) = G (psiRing z)) :
    F = G := by
  have := linearMap_ext (F := F.toLinearMap) (G := G.toLinearMap) h
  exact AlgHom.ext fun x => LinearMap.congr_fun this x

theorem bcAlg_comp (f g : QZ →+* QZ) : bcAlg k (f.comp g) = (bcAlg k f).comp (bcAlg k g) :=
  algHom_ext fun z => by simp

theorem bcAlg_id : bcAlg k (RingHom.id QZ) = AlgHom.id k (LamK k) :=
  algHom_ext fun z => by simp

theorem bcAlg_toLinearMap (f : QZ →+* QZ) :
    (bcAlg k f).toLinearMap = bcLin k f.toIntAlgHom.toLinearMap :=
  linearMap_ext fun z => by simp

variable (k) in
/-- The `k`-algebra base change of a ring automorphism of `Λ_ℤ`. -/
def bcEquiv (f : QZ ≃+* QZ) : LamK k ≃ₐ[k] LamK k :=
  AlgEquiv.ofAlgHom (bcAlg k f.toRingHom) (bcAlg k f.symm.toRingHom)
    (algHom_ext fun z => by simp) (algHom_ext fun z => by simp)

@[simp] theorem bcEquiv_psiRing (f : QZ ≃+* QZ) (z : QZ) :
    bcEquiv k f (psiRing z) = psiRing (f z) := by
  simp [bcEquiv]

@[simp] theorem bcEquiv_symm_psiRing (f : QZ ≃+* QZ) (z : QZ) :
    (bcEquiv k f).symm (psiRing z) = psiRing (f.symm z) := by
  simp [bcEquiv]

theorem algEquiv_ext {F G : LamK k ≃ₐ[k] LamK k}
    (h : ∀ z : QZ, F (psiRing z) = G (psiRing z)) : F = G :=
  AlgEquiv.coe_algHom_injective (algHom_ext h)

variable (k) in
/-- Base change as a group homomorphism `Aut(Λ_ℤ) → Aut_k(Λ_k)`. -/
def bcHom : (QZ ≃+* QZ) →* (LamK k ≃ₐ[k] LamK k) where
  toFun := bcEquiv k
  map_one' := algEquiv_ext fun z => by simp; rfl
  map_mul' f g := algEquiv_ext fun z => by simp; rfl

@[simp] theorem bcHom_apply (f : QZ ≃+* QZ) : bcHom k f = bcEquiv k f := rfl

theorem bcEquiv_zpow (f : QZ ≃+* QZ) (i : ℤ) : bcEquiv k (f ^ i) = (bcEquiv k f) ^ i :=
  map_zpow (bcHom k) f i

theorem bcEquiv_pow (f : QZ ≃+* QZ) (n : ℕ) : bcEquiv k (f ^ n) = (bcEquiv k f) ^ n :=
  map_pow (bcHom k) f n

/-! ## Tensor squares: the coproduct, the counit and the twisted product -/

variable (k) in
/-- `Λ'_ℤ ⊗ Λ'_ℤ → Λ'_k ⊗ Λ'_k`, `x ⊗ y ↦ ι x ⊗ ι y`. -/
def iotaT : LL ℤ →ₗ[ℤ] LL k :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun x y => iota k x ⊗ₜ[k] iota k y)
    (fun x x' y => by dsimp only; rw [map_add, TensorProduct.add_tmul])
    (fun c x y => by
      dsimp only
      rw [map_zsmul]
      exact map_zsmul ((TensorProduct.mk k (L k) (L k)).flip (iota k y)) c (iota k x))
    (fun x y y' => by dsimp only; rw [map_add, TensorProduct.tmul_add])
    (fun c x y => by
      dsimp only
      rw [map_zsmul]
      exact map_zsmul ((TensorProduct.mk k (L k) (L k)) (iota k x)) c (iota k y)))

@[simp] theorem iotaT_tmul (x y : L ℤ) : iotaT k (x ⊗ₜ[ℤ] y) = iota k x ⊗ₜ[k] iota k y := rfl

theorem iotaT_basis (p : EKFreeCoproduct.W × EKFreeCoproduct.W) : iotaT k (tensorBasis ℤ p) = tensorBasis k p := by
  rw [tensorBasis_apply, tensorBasis_apply, iotaT_tmul, iota_wordBasis, iota_wordBasis]

theorem int_smul_eq {M : Type*} [AddCommGroup M] [Module k M] (c : ℤ) (m : M) :
    c • m = (c : k) • m := (Int.cast_smul_eq_zsmul k c m).symm

theorem iotaT_tensorMul (x y : LL ℤ) :
    iotaT k (tensorMul (-1 : ℤ) x y) = tensorMul (-1 : k) (iotaT k x) (iotaT k y) := by
  induction x using basis_induction ℤ (tensorBasis ℤ) with
  | hz => simp
  | ha x z hx hz => rw [tensorMul_add_left, map_add, hx, hz, map_add, tensorMul_add_left]
  | hb p r =>
    induction y using basis_induction ℤ (tensorBasis ℤ) with
    | hz => simp
    | ha y z hy hz => rw [tensorMul_add_right, map_add, hy, hz, map_add, tensorMul_add_right]
    | hb t s =>
      rw [tensorMul_smul_left, tensorMul_smul_right, tensorMul_basis]
      simp only [map_zsmul, iotaT_basis]
      simp only [← Int.cast_smul_eq_zsmul k, tensorMul_smul_left, tensorMul_smul_right,
        tensorMul_basis, Int.cast_pow, Int.cast_neg, Int.cast_one]
      rw [smul_comm]

theorem iotaT_coproduct (x : L ℤ) :
    iotaT k (coproduct (-1 : ℤ) x) = coproduct (-1 : k) (iota k x) := by
  induction x using basis_induction ℤ (wordBasis ℤ) with
  | hz => simp
  | ha x z hx hz => rw [map_add, map_add, hx, hz, map_add, map_add]
  | hb w r =>
    rw [map_zsmul, map_zsmul, map_zsmul, map_zsmul]
    congr 1
    induction w using FreeMonoid.recOn with
    | h0 =>
      rw [wordBasis_one, coproduct_one, map_one, coproduct_one, tensorOne, tensorOne,
        iotaT_tmul, map_one]
    | ih i w ih =>
      rw [wordBasis_mul, wordBasis_of, coproduct_mul, iotaT_tensorMul, ih, map_mul,
        iota_h, coproduct_mul, coproduct_h, coproduct_h, map_sum]
      simp only [iotaT_tmul, iota_h, iota_wordBasis]

variable (k) in
/-- `Λ_ℤ ⊗ Λ_ℤ → Λ_k ⊗ Λ_k`, `y ⊗ z ↦ ψ(y) ⊗ ψ(z)`. -/
def psiT : QZ ⊗[ℤ] QZ →ₗ[ℤ] LamK k ⊗[k] LamK k :=
  TensorProduct.lift (LinearMap.mk₂ ℤ (fun x y => psiRing (k := k) x ⊗ₜ[k] psiRing y)
    (fun x x' y => by dsimp only; rw [map_add, TensorProduct.add_tmul])
    (fun c x y => by
      dsimp only
      rw [map_zsmul]
      exact map_zsmul ((TensorProduct.mk k (LamK k) (LamK k)).flip (psiRing y)) c (psiRing x))
    (fun x y y' => by dsimp only; rw [map_add, TensorProduct.tmul_add])
    (fun c x y => by
      dsimp only
      rw [map_zsmul]
      exact map_zsmul ((TensorProduct.mk k (LamK k) (LamK k)) (psiRing x)) c (psiRing y)))

@[simp] theorem psiT_tmul (x y : QZ) : psiT k (x ⊗ₜ[ℤ] y) = psiRing x ⊗ₜ[k] psiRing y := rfl

theorem psiT_quotientTensorMap (t : EKFreeCoproduct.T) :
    psiT k (EKCoideal.quotientTensorMap t) = quotientTensorMap (-1 : k) (iotaT k t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rfl
  | add a b ha hb => simp only [map_add, ha, hb]

/-- The coproduct `Δ` of `Λ_k` (Corollary 2.4 over `k`). -/
abbrev coproductK : LamK k →ₗ[k] LamK k ⊗[k] LamK k := EKFinal.coproductK

/-- **Coproduct compatibility with base change:** `Δ_k ∘ ψ = (ψ ⊗ ψ) ∘ Δ_ℤ`. -/
theorem coproductK_psiRing (z : QZ) :
    coproductK (psiRing (k := k) z) = psiT k (EKCoideal.quotientCoproduct z) := by
  obtain ⟨x, rfl⟩ := EKRadicalQuotient.pi_surjective z
  rw [psiRing_pi, EKCoideal.quotientCoproduct_pi, psiT_quotientTensorMap,
    ← coproduct_neg_one, iotaT_coproduct]
  rfl

/-- **Counit compatibility with base change.** -/
theorem counitK_psiRing (z : QZ) :
    quotientCounit (-1 : k) (psiRing z) = ((EKRadicalQuotient.quotientCounit z : ℤ) : k) := by
  obtain ⟨x, rfl⟩ := EKRadicalQuotient.pi_surjective z
  rw [psiRing_pi, quotientCounit_pi]
  change counit k (iota k x) = ((EKRadicalQuotient.quotientCounit (Ideal.Quotient.mk _ x) : ℤ) : k)
  have h : (counitAlg k).toRingHom.comp (iota k).toRingHom =
      (Int.castRingHom k).comp (counitAlg ℤ).toRingHom := by
    apply RingHom.toIntAlgHom_injective
    apply FreeAlgebra.hom_ext
    funext i
    simp [counitAlg, iota]
  exact congrArg (fun F : L ℤ →+* k => F x) h

/-- The twisted product on `Λ_k ⊗ Λ_k` is compatible with base change. -/
theorem tensorMulK_psiT (u v : QZ ⊗[ℤ] QZ) :
    quotientTensorMul (-1 : k) (psiT k u) (psiT k v) =
      psiT k (EKSignedQuotient.quotientTensorMul u v) := by
  obtain ⟨u, rfl⟩ := EKSignedQuotient.quotientTensorMap_surjective u
  obtain ⟨v, rfl⟩ := EKSignedQuotient.quotientTensorMap_surjective v
  rw [psiT_quotientTensorMap, psiT_quotientTensorMap, quotientTensorMul_map,
    EKSignedQuotient.quotientTensorMul_map, psiT_quotientTensorMap, ← tensorMul_neg_one,
    iotaT_tensorMul]

/-- Tensor products of base-changed maps are base changes. -/
theorem map_bcLin_psiT (f g : QZ →ₗ[ℤ] QZ) (u : QZ ⊗[ℤ] QZ) :
    TensorProduct.map (bcLin k f) (bcLin k g) (psiT k u) = psiT k (TensorProduct.map f g u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- Multiplication is compatible with base change. -/
theorem mul_psiT (u : QZ ⊗[ℤ] QZ) :
    TensorProduct.lift (LinearMap.mul k (LamK k)) (psiT k u) =
      psiRing (TensorProduct.lift (LinearMap.mul ℤ QZ) u) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-! ## Characters -/

variable (k) in
/-- The base change `Λ_k → k` of a character `χ : Λ_ℤ → ℤ`. -/
def bcChar (χ : QZ →+* ℤ) : LamK k →ₐ[k] k :=
  (Algebra.TensorProduct.lift (Algebra.ofId k k) ((Algebra.ofId ℤ k).comp χ.toIntAlgHom)
    (fun _ _ => Commute.all _ _)).comp (EKFinal.baseChangeAlgEquiv k).symm.toAlgHom

@[simp] theorem bcChar_psiRing (χ : QZ →+* ℤ) (z : QZ) :
    bcChar k χ (psiRing z) = ((χ z : ℤ) : k) := by
  simp [bcChar, baseChangeAlgEquiv_symm_psiRing]

end OddMath.Frontier.EKOverK
