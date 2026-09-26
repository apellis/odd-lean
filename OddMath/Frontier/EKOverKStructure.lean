import OddMath.Frontier.EKOverKTransport
import OddMath.Frontier.EKTriangular

/-!
# EK §2.2–§2.3 over an arbitrary commutative ring

Source: Ellis–Khovanov, arXiv:1107.5610v2.  `k` is an arbitrary commutative ring (p. 5),
`q = -1` (§2.2 on), `Λ_k = Lam (-1 : k)`.  Everything here is obtained from the integral
statements by the base change `Λ_k = k ⊗_ℤ Λ_ℤ` (Corollary 2.12) of `EKOverKTransport`.

* Prop. 2.5 (p. 12), (2.6)–(2.7) over `k`: `Δ(h_n) = Σ h_i ⊗ h_{n-i}` and
  `Δ(e_n) = Σ e_i ⊗ e_{n-i}` (`coproductK_h`, `coproductK_e`).
* §2.3 (pp. 18–21) over `k`:
  - `psi1K` (ψ₁, `h_n ↦ e_n`, Cor. 2.13), an automorphism of `k`-bialgebras
    (`psi1K_h`, `psi1K_coproduct`, `psi1K_counit`);
  - `psi2K` (ψ₂, `h_n ↦ (-1)^{C(n+1,2)} h_n`), an involution (`psi2K_h`, `psi2K_involutive`);
  - `psi3K` (ψ₃), a `k`-linear super anti-automorphism fixing every `h_n`
    (`psi3K_h`, `psi3K_involutive`, `psi3K_mul`, `psi3K_hWord`: (2.24) with the exponent
    `Σ_{i<j} λ_i λ_j`);
  - (2.25) for `ψ₁ψ₂` (`psi12K_h`, `psi12K_e`, `psi12K_hWord`, `psi12K_eWord`);
  - Cor. 2.18 (`psi2K_psi1K_psi2K`, `psi1K_psi2K_psi1K`, `psi12K_involutive`);
  - Lemma 2.16 (`lemma_2_16_K`): ψ₃ is triangular in the lexicographic order on the
    `h_λ`, with diagonal entries `(-1)^{b(λᵀ)}`.
* Prop. 2.17 (p. 20) over `k`: the antipode `S = ψ₁ψ₂ψ₃` (`SK`), `S(h_n) = (-1)^{C(n+1,2)} e_n`,
  (2.25) for `S`, super anti-multiplicativity, both antipode identities
  (`SK_convolution_left/right`), and the bundled `(-1)`-Hopf algebra (Hopf superalgebra)
  `lambdaKHopf : EKComplete.QHopfAlgebra k (-1) Λ_k` (`proposition_2_17_K`).
-/

noncomputable section
set_option synthInstance.maxHeartbeats 400000
open scoped TensorProduct BigOperators

namespace OddMath.Frontier.EKOverK
open EKGeneralQ
open EKAutomorphisms (s)

variable {k : Type*} [CommRing k]

/-! ## Generators -/

variable (k) in
/-- `h_n ∈ Λ_k`. -/
def hK (n : ℕ) : LamK k := psiRing (EKElementaryQuotient.h n)

variable (k) in
/-- `e_n ∈ Λ_k` (defined by (2.5)). -/
def eK' (n : ℕ) : LamK k := psiRing (EKElementaryQuotient.e n)

theorem eK'_eq (n : ℕ) : eK' k n = EKGeneralQ.eK n := rfl

theorem hK_eq (n : ℕ) : hK k n = piQ (-1 : k) (h k n) := by
  rw [hK, EKElementaryQuotient.h, psiRing_pi, ← h_int, iota_h]

@[simp] theorem hK_zero : hK k 0 = 1 := by
  rw [hK_eq, h_zero, map_one]

@[simp] theorem eK'_zero : eK' k 0 = 1 := by
  rw [eK', EKElementaryQuotient.e, CompleteElementary.elementary_zero, map_one, map_one]

theorem hWordK (w : List ℕ) :
    (w.map (hK k)).prod = psiRing ((w.map EKElementaryQuotient.h).prod) := by
  rw [map_list_prod, List.map_map]; rfl

theorem eWordK (w : List ℕ) :
    (w.map (eK' k)).prod = psiRing ((w.map EKElementaryQuotient.e).prod) := by
  rw [map_list_prod, List.map_map]; rfl

/-! ## Prop. 2.5: the coproduct of `h_n` and `e_n` over `k` -/

/-- **EK (2.6) over `k`:** `Δ(h_n) = Σ_{i=0}^n h_i ⊗ h_{n-i}`. -/
theorem coproductK_h (n : ℕ) :
    coproductK (hK k n) = ∑ i : Fin (n + 1), hK k i ⊗ₜ[k] hK k (n - i) := by
  rw [hK, coproductK_psiRing, EKAutomorphisms.coproduct_h, map_sum]
  rfl

/-- **EK Proposition 2.5(1), (2.7), over `k`:** `Δ(e_n) = Σ_{i=0}^n e_i ⊗ e_{n-i}`. -/
theorem coproductK_e (n : ℕ) :
    coproductK (eK' k n) = ∑ i : Fin (n + 1), eK' k i ⊗ₜ[k] eK' k (n - i) := by
  rw [eK', coproductK_psiRing, EKElementaryQuotient.quotientCoproduct_e, map_sum]
  rfl

/-! ## The maps ψ₁, ψ₂, ψ₃ and S over `k` -/

variable (k) in
/-- ψ₁ on `Λ_k`: the `k`-algebra automorphism `h_n ↦ e_n` (Cor. 2.13 over `k`). -/
def psi1K : LamK k ≃ₐ[k] LamK k := bcEquiv k EKPresentation.psi1

variable (k) in
/-- ψ₂ on `Λ_k`: the `k`-algebra automorphism `h_n ↦ (-1)^{C(n+1,2)} h_n`. -/
def psi2K : LamK k ≃ₐ[k] LamK k := bcEquiv k EKAutomorphisms.psi2

variable (k) in
/-- ψ₁ψ₂ on `Λ_k`. -/
def psi12K : LamK k ≃ₐ[k] LamK k := bcEquiv k EKAutomorphisms.psi12

variable (k) in
/-- ψ₃ on `Λ_k`: the `k`-linear super anti-automorphism fixing every `h_n`. -/
def psi3K : LamK k →ₗ[k] LamK k := bcLin k EKAutomorphisms.psi3.toLinearMap

variable (k) in
/-- The antipode `S = ψ₁ψ₂ψ₃` of `Λ_k` (Prop. 2.17). -/
def SK : LamK k →ₗ[k] LamK k := bcLin k EKAntipode.S

@[simp] theorem psi1K_psiRing (z : QZ) : psi1K k (psiRing z) = psiRing (EKPresentation.psi1 z) :=
  bcEquiv_psiRing _ z
@[simp] theorem psi2K_psiRing (z : QZ) :
    psi2K k (psiRing z) = psiRing (EKAutomorphisms.psi2 z) := bcEquiv_psiRing _ z
@[simp] theorem psi12K_psiRing (z : QZ) :
    psi12K k (psiRing z) = psiRing (EKAutomorphisms.psi12 z) := bcEquiv_psiRing _ z
@[simp] theorem psi3K_psiRing (z : QZ) :
    psi3K k (psiRing z) = psiRing (EKAutomorphisms.psi3 z) := bcLin_psiRing _ z
@[simp] theorem SK_psiRing (z : QZ) : SK k (psiRing z) = psiRing (EKAntipode.S z) :=
  bcLin_psiRing _ z

theorem psi12K_apply (x : LamK k) : psi12K k x = psi1K k (psi2K k x) := by
  have h := linearMap_ext (F := (psi12K k).toLinearMap)
    (G := (psi1K k).toLinearMap ∘ₗ (psi2K k).toLinearMap) (fun z => by
      simp only [AlgEquiv.toLinearMap_apply, LinearMap.coe_comp, Function.comp_apply,
        psi12K_psiRing, psi2K_psiRing, psi1K_psiRing, EKAutomorphisms.psi12_apply])
  exact LinearMap.congr_fun h x

/-- `S = ψ₁ ψ₂ ψ₃` on `Λ_k`, in EK's composition order. -/
theorem SK_apply (x : LamK k) : SK k x = psi1K k (psi2K k (psi3K k x)) := by
  have h := linearMap_ext (F := SK k)
    (G := (psi1K k).toLinearMap ∘ₗ (psi2K k).toLinearMap ∘ₗ psi3K k) (fun z => by
      simp only [SK_psiRing, AlgEquiv.toLinearMap_apply, LinearMap.coe_comp,
        Function.comp_apply, psi3K_psiRing, psi2K_psiRing, psi1K_psiRing,
        EKAntipode.S_apply, EKAutomorphisms.psi12_apply])
  exact LinearMap.congr_fun h x

/-! ### Values on generators and words; (2.24), (2.25) -/

/-- **Cor. 2.13 over `k`:** `ψ₁(h_n) = e_n`. -/
@[simp] theorem psi1K_h (n : ℕ) : psi1K k (hK k n) = eK' k n := by
  rw [hK, psi1K_psiRing, EKPresentation.psi1_h]; rfl

@[simp] theorem psi2K_h (n : ℕ) : psi2K k (hK k n) = ((s n : ℤ) : k) • hK k n := by
  rw [hK, psi2K_psiRing, EKAutomorphisms.psi2_h, psiRing_zsmul]

/-- (2.25) over `k`, generators: `ψ₁ψ₂(h_n) = (-1)^{C(n+1,2)} e_n`. -/
@[simp] theorem psi12K_h (n : ℕ) : psi12K k (hK k n) = ((s n : ℤ) : k) • eK' k n := by
  rw [hK, psi12K_psiRing, EKAutomorphisms.psi12_h, psiRing_zsmul]; rfl

/-- (2.25) over `k`, generators: `ψ₁ψ₂(e_n) = (-1)^{C(n+1,2)} h_n`. -/
@[simp] theorem psi12K_e (n : ℕ) : psi12K k (eK' k n) = ((s n : ℤ) : k) • hK k n := by
  rw [eK', psi12K_psiRing, EKAutomorphisms.psi12_e, psiRing_zsmul]; rfl

@[simp] theorem psi3K_h (n : ℕ) : psi3K k (hK k n) = hK k n := by
  rw [hK, psi3K_psiRing]; exact congrArg psiRing (EKAutomorphisms.psi3_h n)

/-- **Prop. 2.17 over `k`:** `S(h_n) = (-1)^{C(n+1,2)} e_n`. -/
@[simp] theorem SK_h (n : ℕ) : SK k (hK k n) = ((s n : ℤ) : k) • eK' k n := by
  rw [hK, SK_psiRing, EKAntipode.S_h, psiRing_zsmul]; rfl

/-- ψ₁ on words: `ψ₁(h_{λ₁}⋯h_{λ_r}) = e_{λ₁}⋯e_{λ_r}`. -/
theorem psi1K_hWord (w : List ℕ) : psi1K k (w.map (hK k)).prod = (w.map (eK' k)).prod := by
  rw [hWordK, psi1K_psiRing, EKPresentation.psi1_word, eWordK]

/-- (2.25) over `k`, on words of `h`'s. -/
theorem psi12K_hWord (w : List ℕ) :
    psi12K k (w.map (hK k)).prod =
      ((-1 : k) ^ ((w.map (fun n => (n + 1).choose 2)).sum)) • (w.map (eK' k)).prod := by
  rw [hWordK, psi12K_psiRing, EKAutomorphisms.psi12_hWord_source, psiRing_zsmul, eWordK]
  push_cast; rfl

/-- (2.25) over `k`, on words of `e`'s. -/
theorem psi12K_eWord (w : List ℕ) :
    psi12K k (w.map (eK' k)).prod =
      ((-1 : k) ^ ((w.map (fun n => (n + 1).choose 2)).sum)) • (w.map (hK k)).prod := by
  rw [eWordK, psi12K_psiRing, EKAutomorphisms.psi12_eWord_source, psiRing_zsmul, hWordK]
  push_cast; rfl

/-- (2.24) over `k` (with the exponent `Σ_{i<j} λ_i λ_j`):
`ψ₃(h_{λ₁}⋯h_{λ_r}) = (-1)^{Σ_{i<j} λ_iλ_j} h_{λ_r}⋯h_{λ₁}`. -/
theorem psi3K_hWord (w : List ℕ) :
    psi3K k (w.map (hK k)).prod =
      ((-1 : k) ^ (∑ i : Fin w.length, ∑ j : Fin w.length,
        if i < j then w.get i * w.get j else 0)) • (w.reverse.map (hK k)).prod := by
  rw [hWordK, psi3K_psiRing]
  change psiRing (EKAutomorphisms.psi3 _) = _
  rw [EKAutomorphisms.psi3_hWord_source, psiRing_zsmul, hWordK]
  push_cast; rfl

/-- (2.25) over `k` for the antipode: `S(h_{λ₁}⋯h_{λ_r}) = (-1)^{C(|λ|+1,2)} e_{λ_r}⋯e_{λ₁}`. -/
theorem SK_hWord (w : List ℕ) :
    SK k (w.map (hK k)).prod =
      ((-1 : k) ^ ((w.sum + 1).choose 2)) • (w.reverse.map (eK' k)).prod := by
  rw [hWordK, SK_psiRing, EKAntipode.S_hWord, psiRing_zsmul, eWordK]
  push_cast; rfl

/-! ### Involutions and Cor. 2.18 -/

theorem psi2K_involutive (x : LamK k) : psi2K k (psi2K k x) = x := by
  have h := linearMap_ext (F := (psi2K k).toLinearMap ∘ₗ (psi2K k).toLinearMap)
    (G := LinearMap.id) (fun z => by simp)
  exact LinearMap.congr_fun h x

theorem psi12K_involutive (x : LamK k) : psi12K k (psi12K k x) = x := by
  have h := linearMap_ext (F := (psi12K k).toLinearMap ∘ₗ (psi12K k).toLinearMap)
    (G := LinearMap.id) (fun z => by
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
        psi12K_psiRing, LinearMap.id_apply]
      exact congrArg psiRing (EKAutomorphisms.psi12_involutive z))
  exact LinearMap.congr_fun h x

theorem psi3K_involutive (x : LamK k) : psi3K k (psi3K k x) = x :=
  bcLin_leftInverse (fun z => EKAutomorphisms.psi3_involutive z) x

/-- **Cor. 2.18 over `k`:** `ψ₂ψ₁ψ₂ = ψ₁⁻¹`. -/
theorem psi2K_psi1K_psi2K (x : LamK k) :
    psi2K k (psi1K k (psi2K k x)) = (psi1K k).symm x := by
  have h := linearMap_ext
    (F := (psi2K k).toLinearMap ∘ₗ (psi1K k).toLinearMap ∘ₗ (psi2K k).toLinearMap)
    (G := (psi1K k).symm.toLinearMap) (fun z => by
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
        psi2K_psiRing, psi1K_psiRing, EKAutomorphisms.psi2_psi1_psi2]
      exact (bcEquiv_symm_psiRing _ z).symm)
  exact LinearMap.congr_fun h x

/-- **Cor. 2.18 over `k`:** `ψ₁ψ₂ψ₁ = ψ₂`. -/
theorem psi1K_psi2K_psi1K (x : LamK k) : psi1K k (psi2K k (psi1K k x)) = psi2K k x := by
  have h := linearMap_ext
    (F := (psi1K k).toLinearMap ∘ₗ (psi2K k).toLinearMap ∘ₗ (psi1K k).toLinearMap)
    (G := (psi2K k).toLinearMap) (fun z => by
      simp [EKAutomorphisms.psi1_psi2_psi1])
  exact LinearMap.congr_fun h x

/-! ### ψ₁ is an automorphism of bialgebras -/

theorem psi1K_toLinearMap :
    (psi1K k).toLinearMap = bcLin k EKAutomorphisms.psi1L := by
  apply linearMap_ext
  intro z
  simp

/-- ψ₁ commutes with the coproduct of `Λ_k`. -/
theorem psi1K_coproduct (x : LamK k) :
    coproductK (psi1K k x) =
      TensorProduct.map (psi1K k).toLinearMap (psi1K k).toLinearMap (coproductK x) := by
  have h := linearMap_ext (F := coproductK ∘ₗ (psi1K k).toLinearMap)
    (G := TensorProduct.map (psi1K k).toLinearMap (psi1K k).toLinearMap ∘ₗ coproductK)
    (fun z => by
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply]
      rw [psi1K_psiRing, coproductK_psiRing, EKAutomorphisms.psi1_coproduct, coproductK_psiRing,
        psi1K_toLinearMap, map_bcLin_psiT]
      rfl)
  exact LinearMap.congr_fun h x

/-- ψ₁ commutes with the counit of `Λ_k`. -/
theorem psi1K_counit (x : LamK k) :
    quotientCounit (-1 : k) (psi1K k x) = quotientCounit (-1 : k) x := by
  have h := linearMap_ext (F := (quotientCounit (-1 : k)).toLinearMap ∘ₗ (psi1K k).toLinearMap)
    (G := (quotientCounit (-1 : k)).toLinearMap) (fun z => by
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgEquiv.toLinearMap_apply,
        AlgHom.toLinearMap_apply, psi1K_psiRing, counitK_psiRing,
        EKAutomorphisms.psi1_counit])
  exact LinearMap.congr_fun h x

/-! ### Super anti-multiplicativity of ψ₃ and S -/

theorem psi3K_mul {a b : ℕ} {x y : LamK k} (hx : x ∈ degreePieceK k a)
    (hy : y ∈ degreePieceK k b) :
    psi3K k (x * y) = ((-1 : k) ^ (a * b)) • (psi3K k y * psi3K k x) :=
  bcLin_superAnti (fun hx hy => EKAutomorphisms.psi3_mul hx hy) hx hy

theorem SK_mul {a b : ℕ} {x y : LamK k} (hx : x ∈ degreePieceK k a)
    (hy : y ∈ degreePieceK k b) :
    SK k (x * y) = ((-1 : k) ^ (a * b)) • (SK k y * SK k x) :=
  bcLin_superAnti (fun hx hy => EKAntipode.S_mul hx hy) hx hy

theorem SK_degree {d : ℕ} {x : LamK k} (hx : x ∈ degreePieceK k d) : SK k x ∈ degreePieceK k d :=
  bcLin_degree (fun hz => EKAntipode.S_degree hz) hx

theorem psi3K_degree {d : ℕ} {x : LamK k} (hx : x ∈ degreePieceK k d) :
    psi3K k x ∈ degreePieceK k d :=
  bcLin_degree (fun hz => EKAutomorphisms.psi3_degree hz) hx

@[simp] theorem SK_one : SK k 1 = 1 := by
  rw [← map_one (psiRing (k := k)), SK_psiRing, EKAntipode.S_one]

/-! ### The antipode identities (Prop. 2.17) -/

/-- **Prop. 2.17 over `k`, first antipode identity:** `m (S ⊗ id) Δ = η ε`. -/
theorem SK_convolution_left (x : LamK k) :
    TensorProduct.lift (LinearMap.mul k (LamK k))
      (TensorProduct.map (SK k) LinearMap.id (coproductK x)) =
      algebraMap k (LamK k) (quotientCounit (-1 : k) x) := by
  have h := linearMap_ext
    (F := TensorProduct.lift (LinearMap.mul k (LamK k)) ∘ₗ
      TensorProduct.map (SK k) LinearMap.id ∘ₗ coproductK)
    (G := (Algebra.linearMap k (LamK k)) ∘ₗ (quotientCounit (-1 : k)).toLinearMap)
    (fun z => by
      simp only [LinearMap.coe_comp, Function.comp_apply, coproductK_psiRing]
      rw [← bcLin_id (k := k), SK, map_bcLin_psiT, mul_psiT]
      have := EKAntipode.convolution_left z
      change psiRing (EKAntipode.multiplication _) = _
      rw [this, psiRing_zsmul, map_one, Algebra.linearMap_apply, AlgHom.toLinearMap_apply,
        counitK_psiRing, Algebra.algebraMap_eq_smul_one])
  exact LinearMap.congr_fun h x

/-- **Prop. 2.17 over `k`, second antipode identity:** `m (id ⊗ S) Δ = η ε`. -/
theorem SK_convolution_right (x : LamK k) :
    TensorProduct.lift (LinearMap.mul k (LamK k))
      (TensorProduct.map LinearMap.id (SK k) (coproductK x)) =
      algebraMap k (LamK k) (quotientCounit (-1 : k) x) := by
  have h := linearMap_ext
    (F := TensorProduct.lift (LinearMap.mul k (LamK k)) ∘ₗ
      TensorProduct.map LinearMap.id (SK k) ∘ₗ coproductK)
    (G := (Algebra.linearMap k (LamK k)) ∘ₗ (quotientCounit (-1 : k)).toLinearMap)
    (fun z => by
      simp only [LinearMap.coe_comp, Function.comp_apply, coproductK_psiRing]
      rw [← bcLin_id (k := k), SK, map_bcLin_psiT, mul_psiT]
      have := EKAntipode.convolution_right z
      change psiRing (EKAntipode.multiplication _) = _
      rw [this, psiRing_zsmul, map_one, Algebra.linearMap_apply, AlgHom.toLinearMap_apply,
        counitK_psiRing, Algebra.algebraMap_eq_smul_one])
  exact LinearMap.congr_fun h x

end OddMath.Frontier.EKOverK
