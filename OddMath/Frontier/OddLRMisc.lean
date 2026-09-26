import OddMath.Frontier.OddSymmetricLimit
import OddMath.Frontier.EKLSectionTwoG
import OddMath.Frontier.EKInfiniteSymmetry
import OddMath.Frontier.EKDualBasesControls
import OddMath.Frontier.EKKostkaValues
import OddMath.Frontier.EKClosureCompositionControls

/-! Ellis, "The odd Littlewood–Richardson rule", arXiv:1111.3932v1 ("E"): small items of §2.1
(p. 5), Proposition 2.3 (2.9) (p. 6) and Lemma 3.5 (3.6) (p. 9).

* Lemma 3.5 (3.6): `s^K_{(k)} = s^p_{(k)} = h_k`, in `OΛ` (`sK_row`), in every `OPol_N`
  (`sp_row`), and `= s^s_{(k)}` (`schur_row`).
* §2.1 lists `ψ₃(h_k) = h_k` as an "algebra anti-involution" and asserts that "both `ψ₁, ψ₂`
  commute with `ψ₃`" and that `S = ψ₁ψ₂ψ₃`. The antipode identity forces EK's *super*
  anti-involution `ψ₃` (`EKAntipode.S`). For it the `ψ₂` half holds (`psi2_psi3_comm`) and
  the `ψ₁` half fails (`psi1_psi3_not_commute`). Both halves hold for the ordinary
  anti-involution `R` (`reverse_psi1_comm`, `reverse_psi2_comm`).
* (2.9b) `ψ₃(s^K_λ) = ε_λ sign(T_λ) s^K_λ` fails for EK's `ψ₃`
  (`EKLSectionTwo.psi3_not_diagonal`) and holds for `R` (`reverse_sK_source`): the eigenvalue
  `η_λ` of `EKLSectionTwo.reverse_sK` equals `ε_λ sign(T_λ) = (-1)^{dN(λ)+N(λ)}` (`eta_eq`).
* The asides of §2.1: `ψ₁` is not an involution (`psi1_not_involutive`); `ψ₂` is not a
  coalgebra homomorphism (`psi2_not_coalgebra`). "`ψ₃` (not a coalgebra homomorphism)" is false
  for EK's `ψ₃` (`psi3_coproduct`: `Δψ₃ = (ψ₃ ⊗ ψ₃)Δ`) and true for `R`
  (`reverse_not_coalgebra`). -/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators TensorProduct

namespace OddMath.Frontier.OddLRMisc

open EKRadicalQuotient (Q)
open EKElementaryQuotient (h e)
open EKPresentation (psi1)
open EKAutomorphisms (psi2 psi3 reverseLinear s wordSign)
open EKCoideal (quotientCoproduct)
open OddLREKIdentification (sK piN)
open TableauExtremal (rowShape)
open TableauStripSigns (north directNorth)

/-! ### Lemma 3.5 (3.6) -/

theorem rowShape_fst {k : ℕ} {p : ℕ × ℕ} (hp : p ∈ (rowShape k).cells) : p.1 = 0 := by
  obtain ⟨i, j⟩ := p
  rw [YoungDiagram.mem_cells, TableauExtremal.mem_rowShape] at hp
  exact hp.1

theorem north_rowShape (k : ℕ) : north (rowShape k) = 0 := by
  unfold north
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _
  rw [rowShape_fst hp]
  exact Nat.not_lt_zero _

theorem directNorth_rowShape (k : ℕ) : directNorth (rowShape k) = 0 := by
  unfold directNorth
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro q _
  rw [rowShape_fst hp]
  exact fun h => Nat.not_lt_zero _ h.1

theorem card_rowShape (k : ℕ) : (rowShape k).card = k := by
  simp [YoungDiagram.card, TableauExtremal.rowShape]

theorem colLen_rowShape (k : ℕ) : (rowShape k).colLen 0 ≤ 1 := by
  by_contra hc
  have hm : (1, 0) ∈ rowShape k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  rw [TableauExtremal.mem_rowShape] at hm
  omega

/-- E Lemma 3.5 (3.6), p. 9, plactic half: `s^p_{(k)} = h_k` in `OPol_N`, every `N`. -/
theorem sp_row (N k : ℕ) : CompleteTableauExpansion.sp N (rowShape k) =
    FiniteCompleteElementary.completePoly N k := by
  rw [CompleteTableauExpansion.sp, directNorth_rowShape, north_rowShape,
    TableauExtremal.tableauPolynomial_row, pow_zero, one_smul]

theorem hq_zero : h 0 = 1 := by simp [EKElementaryQuotient.h]

theorem h_mem_degree (k : ℕ) : h k ∈ EKIntegralBases.degreePiece k := by
  simpa using EKAutomorphisms.hWord_degree [k]

/-- E Lemma 3.5 (3.6), p. 9: `s^K_{(k)} = h_k` in `OΛ`. -/
theorem sK_row (k : ℕ) : sK (rowShape k) = h k := by
  have h1 : sK (rowShape k) ∈ EKIntegralBases.degreePiece k := by
    have := EKLSectionTwo.sK_mem_degree (rowShape k)
    rwa [card_rowShape] at this
  have hinj := OddSymmetricLimit.degreeMap_injective k k (by omega)
    (a₁ := ⟨_, h1⟩) (a₂ := ⟨_, h_mem_degree k⟩) (Subtype.ext (by
      simp only [OddSymmetricLimit.degreeMap_coe]
      rw [OddLRThm38.sK_eq_sp, sp_row, OddLREKIdentification.piN_h]))
  exact congrArg Subtype.val hinj

/-- E Lemma 3.5 (3.6), p. 9, and the remark after it: `s^s_{(k)} = h_k` in `OPol_{n+2}`. -/
theorem schur_row (n k : ℕ) :
    OddSymmetrizer.schur n (OddLREKIdentification.toExponent n (rowShape k)) =
      FiniteCompleteElementary.completePoly (n+2) k := by
  rw [← OddLRThm38.sK_eq_schur n (rowShape k) (by have := colLen_rowShape k; omega), sK_row,
    OddLREKIdentification.piN_h]

/-! ### §2.1: `ψ₁`, `ψ₂`, `ψ₃` and `R` -/

/-- E §2.1, p. 5, "both `ψ₁, ψ₂` commute with `ψ₃`": false for `ψ₁` and EK's super
anti-involution `ψ₃`. Already on `h₂`: `ψ₃ψ₁(h₂) = h₂ + h₁² ≠ h₂ - h₁² = ψ₁ψ₃(h₂)`. -/
theorem psi1_psi3_not_commute : psi3 (psi1 (h 2)) ≠ psi1 (psi3 (h 2)) := by
  have h11 := EKAutomorphisms.psi3_hWord [1, 1]
  simp [EKAutomorphisms.pairExponent] at h11
  rw [EKPresentation.psi1_h, EKAutomorphisms.psi3_h, EKPresentation.psi1_h,
    EKDualBasesControls.elementary_two, map_sub, EKAutomorphisms.psi3_h, h11]
  intro hc
  have h2 : (2 : ℤ) • (h 1 * h 1) = 0 := by
    rw [two_smul]
    have := congrArg (fun x => x - h 2 + h 1 * h 1) hc
    simp only at this
    abel_nf at this ⊢
    simpa using this
  have h0 := EKInfiniteSymmetry.square_smul_injective
    (show (2 : ℤ) • (h 1 * h 1) = (0 : ℤ) • (h 1 * h 1) by rw [h2, zero_smul])
  norm_num at h0

/-- E §2.1, p. 5, "`ψ₂` commutes with `ψ₃`": true for EK's super anti-involution `ψ₃`. -/
theorem psi2_psi3_comm (x : Q) : psi3 (psi2 x) = psi2 (psi3 x) := by
  let f : Q →ₗ[ℤ] Q := psi3.toLinearMap.comp EKAutomorphisms.psi2L
  let g : Q →ₗ[ℤ] Q := EKAutomorphisms.psi2L.comp psi3.toLinearMap
  have hfg : f = g := by
    refine EKIntegralBases.hBasis.ext fun μ => ?_
    simp only [f, g, LinearMap.comp_apply, EKIntegralBases.hBasis_apply]
    change psi3 (psi2 ((μ.rowLens.map h).prod)) = psi2 (psi3 ((μ.rowLens.map h).prod))
    rw [EKAutomorphisms.psi2_word, map_zsmul, EKAutomorphisms.psi3_hWord, map_zsmul,
      EKAutomorphisms.psi2_word, EKAutomorphisms.wordSign_reverse, smul_comm]
  exact LinearMap.congr_fun hfg x

/-- E §2.1, p. 5, "`ψ₁` commutes with `ψ₃`", for the ordinary anti-involution `R`
(`R(xy) = R(y)R(x)`, `R(h_k) = h_k`). -/
theorem reverse_psi1_comm (x : Q) : reverseLinear (psi1 x) = psi1 (reverseLinear x) := by
  let f : Q →ₗ[ℤ] Q := reverseLinear.comp EKAutomorphisms.psi1L
  let g : Q →ₗ[ℤ] Q := EKAutomorphisms.psi1L.comp reverseLinear
  have hfg : f = g := by
    refine EKIntegralBases.hBasis.ext fun μ => ?_
    simp only [f, g, LinearMap.comp_apply, EKIntegralBases.hBasis_apply]
    change reverseLinear (psi1 ((μ.rowLens.map h).prod)) =
      psi1 (reverseLinear ((μ.rowLens.map h).prod))
    have he : psi1 ∘ h = e := funext fun n => EKPresentation.psi1_h n
    rw [EKAutomorphisms.reverse_word, map_list_prod psi1, map_list_prod psi1, List.map_map,
      List.map_map, he, EKLSectionTwo.reverse_eWord]
  exact LinearMap.congr_fun hfg x

/-- E §2.1, p. 5, "`ψ₂` commutes with `ψ₃`", for the ordinary anti-involution `R`. -/
theorem reverse_psi2_comm (x : Q) : reverseLinear (psi2 x) = psi2 (reverseLinear x) := by
  let f : Q →ₗ[ℤ] Q := reverseLinear.comp EKAutomorphisms.psi2L
  let g : Q →ₗ[ℤ] Q := EKAutomorphisms.psi2L.comp reverseLinear
  have hfg : f = g := by
    refine EKIntegralBases.hBasis.ext fun μ => ?_
    simp only [f, g, LinearMap.comp_apply, EKIntegralBases.hBasis_apply]
    change reverseLinear (psi2 ((μ.rowLens.map h).prod)) =
      psi2 (reverseLinear ((μ.rowLens.map h).prod))
    rw [EKAutomorphisms.psi2_word, map_zsmul, EKAutomorphisms.reverse_word,
      EKAutomorphisms.psi2_word, EKAutomorphisms.wordSign_reverse]
  exact LinearMap.congr_fun hfg x

/-- E §2.1, p. 5: `ψ₁` is a bialgebra automorphism "(not an involution)". -/
theorem psi1_not_involutive : psi1 (psi1 (h 2)) ≠ h 2 := by
  intro hc
  have h2 : (psi1^[2]) (h 2) = h 2 := hc
  rw [EKInfiniteSymmetry.psi1_iterate_h_two] at h2
  have h0 := EKInfiniteSymmetry.translation_injective
    (show h 2 - ((2 : ℕ) : ℤ) • (h 1 * h 1) = h 2 - (0 : ℤ) • (h 1 * h 1) by
      rw [h2, zero_smul, sub_zero])
  norm_num at h0

/-- `ψ₂ ⊗ ψ₂` on `OΛ ⊗ OΛ`. -/
def psi2Tensor : (Q ⊗[ℤ] Q) →ₗ[ℤ] (Q ⊗[ℤ] Q) :=
  TensorProduct.map EKAutomorphisms.psi2L EKAutomorphisms.psi2L

/-- E §2.1, p. 5: `ψ₂` is an algebra involution "(not a coalgebra homomorphism)":
`Δψ₂(h₂) - (ψ₂ ⊗ ψ₂)Δ(h₂) = -2 h₁ ⊗ h₁`. -/
theorem psi2_not_coalgebra : quotientCoproduct (psi2 (h 2)) ≠ psi2Tensor (quotientCoproduct (h 2)) := by
  intro hc
  have hm := congrArg EKAntipode.multiplication hc
  have hl : ∀ n, EKAutomorphisms.psi2L (h n) = s n • h n := fun n => EKAutomorphisms.psi2_h n
  have s0 : s 0 = 1 := by simp [EKAutomorphisms.s]
  have s1 : s 1 = -1 := by simp [EKAutomorphisms.s]
  have s2 : s 2 = -1 := by simp [EKAutomorphisms.s, Nat.choose]
  simp only [EKAutomorphisms.psi2_h, map_zsmul, EKAutomorphisms.coproduct_h, map_sum,
    Fin.sum_univ_succ, Fin.sum_univ_zero, map_add, map_zero, psi2Tensor, TensorProduct.map_tmul,
    EKAntipode.multiplication_tmul, hl, Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one,
    Fin.val_one, s2] at hm
  norm_num [s0, s1, s2, hq_zero] at hm
  exact EKAutomorphismsControls.super_square_not_ordinary hm

/-! ### (2.9b): the sign `η_λ = ε_λ sign(T_λ)` -/

theorem neg_one_pow_congr {a b : ℕ} (hab : (a : ZMod 2) = b) : (-1 : ℤ) ^ a = (-1) ^ b := by
  rw [neg_one_pow_eq_pow_mod_two, (ZMod.natCast_eq_natCast_iff' a b 2).mp hab,
    ← neg_one_pow_eq_pow_mod_two]

theorem list_sum_range (n : ℕ) (g : ℕ → ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem cross_cast {a b : ℕ} (hab : a ≤ b) :
    (EKTriangular.cross a b : ZMod 2) = a * b + a := by
  unfold EKTriangular.cross
  split_ifs with hlt
  · push_cast; rfl
  · obtain rfl : a = b := by omega
    have hev : ((a * a + a : ℕ) : ZMod 2) = 0 :=
      (ZMod.eq_zero_iff_even).mpr (by
        have := Nat.even_mul_succ_self a
        rwa [Nat.mul_succ] at this)
    push_cast at hev ⊢
    rw [hev]

/-- Parity of the straightening exponent of a reversed weakly decreasing list. -/
theorem invExp_reverse_cast (f : ℕ → ℕ) (r : ℕ) (hf : ∀ i j, i ≤ j → j < r → f j ≤ f i) :
    (EKTriangular.invExp ((List.range r).map f).reverse : ZMod 2) =
      ∑ i ∈ Finset.range r, ((i * f i + f i * ∑ k ∈ Finset.range i, f k : ℕ) : ZMod 2) := by
  induction r with
  | zero => simp [EKTriangular.invExp]
  | succ r ih =>
    rw [List.range_succ, List.map_append, List.reverse_append, List.map_singleton,
      List.reverse_singleton, List.singleton_append, EKTriangular.invExp,
      Finset.sum_range_succ, ← ih (fun i j hij hj => hf i j hij (by omega))]
    have hs : (((List.range r).map (EKTriangular.cross (f r) ∘ f)).sum : ZMod 2) =
        ∑ k ∈ Finset.range r, ((f r : ZMod 2) * f k + f r) := by
      rw [list_sum_range]
      push_cast
      refine Finset.sum_congr rfl fun k hk => ?_
      exact cross_cast (hf k r (by have := Finset.mem_range.mp hk; omega) (by omega))
    rw [List.map_reverse, List.map_map, List.sum_reverse, Nat.cast_add, hs]
    push_cast
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum]
    simp only [nsmul_eq_mul]
    ring

theorem sum_cells_fst (lam : YoungDiagram) (g : ℕ → ℕ) :
    ∑ p ∈ lam.cells, g p.1 = ∑ i ∈ Finset.range (lam.colLen 0), lam.rowLen i * g i := by
  classical
  rw [← EKKostkaValues.cells_box, Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  dsimp only
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  congr 1
  rw [← Finset.card_range (lam.rowLen i)]
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, ← YoungDiagram.mem_iff_lt_rowLen]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨lam.up_left_mem (Nat.zero_le _) le_rfl h, h⟩

/-- `N(λ) = Σ_{i<j} λ_i λ_j`. -/
theorem north_eq_rows (lam : YoungDiagram) :
    north lam = ∑ i ∈ Finset.range (lam.colLen 0),
      lam.rowLen i * ∑ k ∈ Finset.range i, lam.rowLen k := by
  classical
  set G : ℕ → ℕ := fun i =>
    ∑ k ∈ Finset.range (lam.colLen 0), lam.rowLen k * (if k < i then 1 else 0) with hG
  have hc : ∀ i, (lam.cells.filter (fun q => q.1 < i)).card = G i := by
    intro i
    rw [Finset.card_filter]
    exact sum_cells_fst lam (fun k => if k < i then 1 else 0)
  unfold north
  have h1 : ∑ p ∈ lam.cells, (lam.cells.filter (fun q => q.1 < p.1)).card =
      ∑ p ∈ lam.cells, G p.1 := Finset.sum_congr rfl (fun p _ => hc p.1)
  rw [h1, sum_cells_fst lam G]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  simp only [hG, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  omega

theorem rowLen_antitone (lam : YoungDiagram) {i j : ℕ} (hij : i ≤ j) :
    lam.rowLen j ≤ lam.rowLen i :=
  lam.rowLen_anti i j hij

/-- `η_λ = (-1)^{dN(λ) + N(λ)}`. -/
theorem eta_eq_directNorth_north (lam : YoungDiagram) :
    EKLSectionTwo.eta lam = (-1 : ℤ) ^ (directNorth lam + north lam) := by
  unfold EKLSectionTwo.eta
  apply neg_one_pow_congr
  rw [YoungDiagram.rowLens, invExp_reverse_cast _ _ (fun i j hij _ => rowLen_antitone lam hij),
    EKKostkaValues.directNorth_eq_rows, north_eq_rows]
  push_cast
  rw [← Finset.sum_add_distrib]

/-- E Proposition 2.3 (2.9), p. 6, sign bridge: the eigenvalue `η_λ` of the ordinary
anti-involution `R` on `s^K_λ` is `ε_λ sign(T_λ)`, `ε_λ = (-1)^{Σ_j C(λᵀ_j, 2)}`. -/
theorem eta_eq (lam : YoungDiagram) :
    EKLSectionTwo.eta lam = (-1 : ℤ) ^ EKSchurOrthonormalControls.transposeChoose lam *
      TableauDominance.tableauSign (TableauDominance.canonicalTableau lam) := by
  rw [eta_eq_directNorth_north, CompleteTableauExpansion.canonical_sign,
    ← EKClosureCompositionControls.sign_directNorth_eq_transposeChoose, pow_add]

/-- E Proposition 2.3 (2.9b), p. 6, for the ordinary anti-involution `R`:
`R(s^K_λ) = ε_λ sign(T_λ) s^K_λ`. -/
theorem reverse_sK_source (lam : YoungDiagram) :
    reverseLinear (sK lam) = ((-1 : ℤ) ^ EKSchurOrthonormalControls.transposeChoose lam *
      TableauDominance.tableauSign (TableauDominance.canonicalTableau lam)) • sK lam := by
  rw [EKLSectionTwo.reverse_sK, eta_eq]

/-! ### EK's `ψ₃` is a coalgebra homomorphism -/

open EKSignedQuotient (quotientTensorMul)
open EKIntegralBases (degreePiece)

/-- `ψ₃ ⊗ ψ₃` on `OΛ ⊗ OΛ`. -/
def psi3Tensor : (Q ⊗[ℤ] Q) →ₗ[ℤ] (Q ⊗[ℤ] Q) :=
  TensorProduct.map psi3.toLinearMap psi3.toLinearMap

@[simp] theorem psi3Tensor_tmul (x y : Q) : psi3Tensor (x ⊗ₜ[ℤ] y) = psi3 x ⊗ₜ[ℤ] psi3 y := rfl

/-- Tensors of total degree `a`. -/
def tensorDegree (a : ℕ) : Submodule ℤ (Q ⊗[ℤ] Q) :=
  Submodule.span ℤ {u | ∃ c d x y, c + d = a ∧ x ∈ degreePiece c ∧ y ∈ degreePiece d ∧
    u = x ⊗ₜ[ℤ] y}

theorem psi3Tensor_mul_tmul {c d e f : ℕ} {x y z t : Q} (hx : x ∈ degreePiece c)
    (hy : y ∈ degreePiece d) (hz : z ∈ degreePiece e) (ht : t ∈ degreePiece f) :
    psi3Tensor (quotientTensorMul (x ⊗ₜ[ℤ] y) (z ⊗ₜ[ℤ] t)) = (-1 : ℤ) ^ ((c+d)*(e+f)) •
      quotientTensorMul (psi3Tensor (z ⊗ₜ[ℤ] t)) (psi3Tensor (x ⊗ₜ[ℤ] y)) := by
  rw [EKAutomorphisms.tensorMul_homogeneous hx hy hz ht, map_zsmul, psi3Tensor_tmul,
    EKAutomorphisms.psi3_mul hx hz, EKAutomorphisms.psi3_mul hy ht, psi3Tensor_tmul,
    psi3Tensor_tmul, EKAutomorphisms.tensorMul_homogeneous (EKAutomorphisms.psi3_degree hz)
      (EKAutomorphisms.psi3_degree ht) (EKAutomorphisms.psi3_degree hx)
      (EKAutomorphisms.psi3_degree hy),
    TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', smul_smul, smul_smul, smul_smul]
  congr 1
  have key : ∀ a b : ℕ, (∃ k, b = a + 2 * k) → (-1 : ℤ) ^ a = (-1) ^ b := by
    rintro a b ⟨k, rfl⟩
    rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]
  simp only [← pow_add]
  exact key _ _ ⟨c * f, by ring⟩

theorem psi3Tensor_mul {a b : ℕ} {u v : Q ⊗[ℤ] Q} (hu : u ∈ tensorDegree a)
    (hv : v ∈ tensorDegree b) :
    psi3Tensor (quotientTensorMul u v) =
      (-1 : ℤ) ^ (a*b) • quotientTensorMul (psi3Tensor v) (psi3Tensor u) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨c, d, x, y, hcd, hx, hy, rfl⟩ := hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨e, f, z, t, hef, hz, ht, rfl⟩ := hv
      rw [psi3Tensor_mul_tmul hx hy hz ht, hcd, hef]
    | zero => simp
    | add v w _ _ h1 h2 => simp only [map_add, h1, h2, LinearMap.add_apply, smul_add]
    | smul r v _ h =>
      simp only [map_smul, h, LinearMap.smul_apply, smul_comm r]
  | zero => simp
  | add u w _ _ h1 h2 => simp only [map_add, LinearMap.add_apply, h1, h2, smul_add]
  | smul r u _ h => simp only [map_smul, LinearMap.smul_apply, h, smul_comm r]

theorem tensorDegree_mul {a b : ℕ} {u v : Q ⊗[ℤ] Q} (hu : u ∈ tensorDegree a)
    (hv : v ∈ tensorDegree b) : quotientTensorMul u v ∈ tensorDegree (a+b) := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨c, d, x, y, hcd, hx, hy, rfl⟩ := hu
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨e, f, z, t, hef, hz, ht, rfl⟩ := hv
      rw [EKAutomorphisms.tensorMul_homogeneous hx hy hz ht]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c+e, d+f, _, _, by omega,
        EKIntegralBases.degreePiece_mul hx hz, EKIntegralBases.degreePiece_mul hy ht, rfl⟩)
    | zero => simp
    | add v w _ _ h1 h2 => rw [map_add]; exact Submodule.add_mem _ h1 h2
    | smul r v _ h => rw [map_smul]; exact Submodule.smul_mem _ _ h
  | zero => simp
  | add u w _ _ h1 h2 => rw [map_add, LinearMap.add_apply]; exact Submodule.add_mem _ h1 h2
  | smul r u _ h => rw [map_smul, LinearMap.smul_apply]; exact Submodule.smul_mem _ _ h

theorem coproduct_h_mem (n : ℕ) : quotientCoproduct (h n) ∈ tensorDegree n := by
  rw [EKAutomorphisms.coproduct_h]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span
    ⟨i, n - i, _, _, by omega, h_mem_degree _, h_mem_degree _, rfl⟩

theorem coproduct_word_mem (w : List ℕ) :
    quotientCoproduct ((w.map h).prod) ∈ tensorDegree w.sum := by
  induction w with
  | nil =>
    rw [List.map_nil, List.prod_nil, ← hq_zero]
    exact coproduct_h_mem 0
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons, EKSignedQuotient.quotient_coproduct_mul, List.sum_cons]
    exact tensorDegree_mul (coproduct_h_mem a) ih

theorem psi3_coproduct_h (n : ℕ) :
    quotientCoproduct (psi3 (h n)) = psi3Tensor (quotientCoproduct (h n)) := by
  rw [EKAutomorphisms.psi3_h, EKAutomorphisms.coproduct_h, map_sum]
  simp only [psi3Tensor_tmul, EKAutomorphisms.psi3_h]

theorem psi3_coproduct_word (w : List ℕ) :
    quotientCoproduct (psi3 ((w.map h).prod)) = psi3Tensor (quotientCoproduct ((w.map h).prod)) := by
  induction w with
  | nil =>
    rw [List.map_nil, List.prod_nil, ← hq_zero]
    exact psi3_coproduct_h 0
  | cons a w ih =>
    have hw : (w.map h).prod ∈ degreePiece w.sum := EKAutomorphisms.hWord_degree w
    rw [List.map_cons, List.prod_cons, EKAutomorphisms.psi3_mul (h_mem_degree a) hw, map_zsmul,
      EKSignedQuotient.quotient_coproduct_mul, ih, psi3_coproduct_h,
      EKSignedQuotient.quotient_coproduct_mul,
      psi3Tensor_mul (coproduct_h_mem a) (coproduct_word_mem w)]

/-- E §2.1, p. 5, calls `ψ₃` an "algebra anti-involution (not a coalgebra homomorphism)". For
EK's super anti-involution `ψ₃`, the one with `S = ψ₁ψ₂ψ₃` (`EKAntipode.S`), this aside is false:
`Δ ∘ ψ₃ = (ψ₃ ⊗ ψ₃) ∘ Δ`. -/
theorem psi3_coproduct (x : Q) :
    quotientCoproduct (psi3 x) = psi3Tensor (quotientCoproduct x) := by
  induction x using EKPairingAdjoint.basis_induction EKIntegralBases.hBasis with
  | hz => simp
  | ha x y hx hy => simp only [map_add, hx, hy]
  | hb μ r =>
    simp only [map_zsmul, map_smul, EKIntegralBases.hBasis_apply]
    exact congrArg (fun x : Q ⊗[ℤ] Q => r • x) (psi3_coproduct_word μ.rowLens)

/-! ### The ordinary anti-involution `R` is not a coalgebra homomorphism -/

theorem hrepr_degree {d : ℕ} {x : Q} (hx : x ∈ degreePiece d) {ν : YoungDiagram}
    (hν : ν.card ≠ d) : EKIntegralBases.hBasis.repr x ν = 0 := by
  classical
  letI := DegreeShapes.degreeFintype d
  obtain ⟨a, ha, -⟩ := EKIntegralBases.degree_h_unique_coordinates d ⟨x, hx⟩
  rw [← show _ = x from ha, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun μ _ => ?_
  rw [map_zsmul, EKIntegralBases.h_coordinates_partition, Finsupp.smul_apply,
    Finsupp.single_apply, if_neg, smul_zero]
  intro he
  apply hν
  rw [← he]
  exact μ.property

/-- The diagram `(1)`. -/
def shape1 : YoungDiagram := YoungDiagram.ofRowLens [1] (by decide)

theorem hBasis_shape1 : EKIntegralBases.hBasis shape1 = h 1 := by
  rw [EKIntegralBases.hBasis_apply, EKPartitionSpanning.hPartition,
    show shape1.rowLens = [1] from YoungDiagram.rowLens_ofRowLens_eq_self (by simp)]
  simp

theorem card_shape1 : shape1.card = 1 := by
  rw [← EKIntegralBases.rowLens_sum,
    show shape1.rowLens = [1] from YoungDiagram.rowLens_ofRowLens_eq_self (by simp)]
  rfl

/-- `ℓ(x ⊗ y) = [x]_{(1)} y`. -/
def leftCoord : (Q ⊗[ℤ] Q) →ₗ[ℤ] Q :=
  TensorProduct.lift ((LinearMap.lsmul ℤ Q).compl₁₂ (EKIntegralBases.hBasis.coord shape1)
    LinearMap.id)

@[simp] theorem leftCoord_tmul (x y : Q) :
    leftCoord (x ⊗ₜ[ℤ] y) = EKIntegralBases.hBasis.repr x shape1 • y := rfl

theorem coord1_of_degree {d : ℕ} {x : Q} (hx : x ∈ degreePiece d) (hd : d ≠ 1) :
    EKIntegralBases.hBasis.repr x shape1 = 0 :=
  hrepr_degree hx (by rw [card_shape1]; exact fun h => hd h.symm)

theorem tmul_h (a b c d : ℕ) :
    quotientTensorMul (h a ⊗ₜ[ℤ] h b) (h c ⊗ₜ[ℤ] h d) =
      (-1 : ℤ) ^ (b*c) • ((h a * h c) ⊗ₜ[ℤ] (h b * h d)) :=
  EKAutomorphisms.tensorMul_homogeneous (h_mem_degree a) (h_mem_degree b) (h_mem_degree c)
    (h_mem_degree d)

/-- `R ⊗ R` on `OΛ ⊗ OΛ`. -/
def reverseTensor : (Q ⊗[ℤ] Q) →ₗ[ℤ] (Q ⊗[ℤ] Q) := TensorProduct.map reverseLinear reverseLinear

/-- E §2.1, p. 5: for the ordinary anti-involution `R` (`R(h_k) = h_k`), the aside
"(not a coalgebra homomorphism)" holds: `ΔR(h₁h₂) ≠ (R ⊗ R)Δ(h₁h₂)`. -/
theorem reverse_not_coalgebra :
    quotientCoproduct (reverseLinear (h 1 * h 2)) ≠ reverseTensor (quotientCoproduct (h 1 * h 2)) := by
  intro hc
  have hm := congrArg leftCoord hc
  have c0 : EKIntegralBases.hBasis.repr (1 : Q) shape1 = 0 :=
    coord1_of_degree EKIntegralBases.unit_mem_degree_zero (by norm_num)
  have c1 : EKIntegralBases.hBasis.repr (h 1) shape1 = 1 := by
    rw [← hBasis_shape1, Basis.repr_self, Finsupp.single_eq_same]
  have c2 : EKIntegralBases.hBasis.repr (h 2) shape1 = 0 :=
    coord1_of_degree (h_mem_degree 2) (by norm_num)
  have c11 : EKIntegralBases.hBasis.repr (h 1 * h 1) shape1 = 0 :=
    coord1_of_degree (EKIntegralBases.degreePiece_mul (h_mem_degree 1) (h_mem_degree 1))
      (by norm_num)
  have c21 : EKIntegralBases.hBasis.repr (h 2 * h 1) shape1 = 0 :=
    coord1_of_degree (EKIntegralBases.degreePiece_mul (h_mem_degree 2) (h_mem_degree 1))
      (by norm_num)
  simp only [EKAutomorphisms.reverse_mul, EKAutomorphisms.reverse_h,
    EKSignedQuotient.quotient_coproduct_mul, EKAutomorphisms.coproduct_h, Fin.sum_univ_succ,
    Fin.sum_univ_zero, map_add, map_zero, LinearMap.add_apply, LinearMap.zero_apply, tmul_h,
    map_zsmul, reverseTensor, TensorProduct.map_tmul, leftCoord_tmul, Fin.val_zero,
    Fin.val_succ, Fin.succ_zero_eq_one, Fin.val_one] at hm
  norm_num [hq_zero, EKAutomorphisms.reverse_mul, c0, c1, c2, c11, c21] at hm
  rw [add_comm, add_left_cancel_iff] at hm
  exact EKAutomorphismsControls.super_square_not_ordinary hm.symm

end OddMath.Frontier.OddLRMisc
