import OddMath.Frontier.EKClosureComposition
import OddMath.Frontier.EKRestrictedPairing
import OddMath.Frontier.EKFinalClosure

/-!
# Errata in [EK], §3.3: the one-dimensionality claims in the proofs of Proposition 3.10
# and Lemma 3.11

Source: A. P. Ellis, M. Khovanov, *The Hopf algebra of odd symmetric functions*,
arXiv:1107.5610v2, pp. 29–30. Objects: the integral quotient `Λ = Q`, its degree-`d` pieces,
`h_μ = hPartition μ`, `e_μ = ePartition μ`, and the odd Schur functions
`s_λ = EKProp310.schur d λ` of (3.6). The lexicographic order on partitions is
`List.Lex (· < ·)` on row lengths (`EKProp310.LexLT`).

* `H_{≥λ} = span{h_μ : μ ⊢ |λ|, μ ≥ λ}` is `EKTriangular.Hge λ`, and
  `E_{≥κ} = span{e_μ : μ ⊢ d, μ ≥ κ}` is `Ege d κ` below.
* **Proof of Prop. 3.10, p. 29.** The claim that `(H_{≥λ} ∩ E_{≥λᵀ}) ⊗ ℚ` is one-dimensional
  fails at `λ = (3,3)`: `s_{(3,3)}` and `s_{(4,1,1)}` are linearly independent elements of
  `H_{≥(3,3)} ∩ E_{≥(2,2,2)}` (`prop_3_10_intersection`), so no single element spans the
  intersection over `ℚ` (`prop_3_10_not_one_dim`). Prop. 3.10 holds
  (`EKClosureComposition.proposition_3_10`).
* **Proof of Lemma 3.11, pp. 29–30.** The two displays should read
  `ψ₁ψ₂(s_λ) = ±e_λ + Σ_{μ>λ} ±a_μ e_μ` (the printed `h_μ` should be `e_μ`) and
  `ψ₁ψ₂(s_λ) = ±h_{λᵀ} + Σ_{μ>λᵀ} ±b_μ h_μ`; so `ψ₁ψ₂(s_λ)` lies in `H_{≥λᵀ} ∩ E_{≥λ}`
  (`psi12_schur_mem_E`, `psi12_schur_mem_H`), with the indices of the printed
  `H_{≥λ} ∩ E_{≥λᵀ}` swapped. For `λ = (2,2,2)`:
  - the printed intersection `H_{≥(2,2,2)} ∩ E_{≥(3,3)}` does not contain `s_{λᵀ} = s_{(3,3)}`
    (`lemma_3_11_printed_not_mem`) and contains the independent `s_{(2,2,2)}`, `s_{(3,1,1,1)}`
    (`lemma_3_11_printed_intersection`);
  - the corrected intersection `H_{≥(3,3)} ∩ E_{≥(2,2,2)}` is the intersection of the proof of
    Prop. 3.10 at `(3,3)`, again not one-dimensional over `ℚ` (`lemma_3_11_not_one_dim`).
  Lemma 3.11 holds (`EKFinalClosure.lemma_3_11`).
-/

noncomputable section
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace OddMath.Frontier.ErrataChecks
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases
open EKPartitionSpanning (hPartition ePartition)
open EKProp310 (LexLT Dom schur)
open EKElementaryQuotient (h e)

local instance (d : ℕ) : Fintype (DegreeShape d) := degreeFintype d
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

/-- `E_{≥κ}` in degree `d` ([EK] §2.2): the integral span of the `e_μ`, `μ ⊢ d`, `μ ≥ κ` in the
lexicographic order. -/
def Ege (d : ℕ) (κ : YoungDiagram) : Submodule ℤ Q :=
  Submodule.span ℤ {x | ∃ ν : YoungDiagram, ν.card = d ∧
    (ν = κ ∨ List.Lex (· < ·) κ.rowLens ν.rowLens) ∧ ePartition ν = x}

private theorem map_mem_of_span {M : Type*} [AddCommGroup M] [Module ℤ M] {S : Set M}
    (f : M →ₗ[ℤ] Q) (T : Submodule ℤ Q) (hS : ∀ x ∈ S, f x ∈ T) {x : M}
    (hx : x ∈ Submodule.span ℤ S) : f x ∈ T := by
  have hle : Submodule.span ℤ S ≤ T.comap f := Submodule.span_le.mpr hS
  exact hle hx

private theorem lex_ge_trans {a b c : YoungDiagram} (h1 : b = a ∨ LexLT a b)
    (h2 : c = b ∨ LexLT b c) : c = a ∨ LexLT a c := by
  rcases h2 with rfl | h2
  · exact h1
  · rcases h1 with rfl | h1
    · exact Or.inr h2
    · exact Or.inr (lt_trans h1 h2)

private theorem hPartition_mem_Hge {lam ν : YoungDiagram} (hc : ν.card = lam.card)
    (h : ν = lam ∨ LexLT lam ν) : hPartition ν ∈ EKTriangular.Hge lam :=
  Submodule.subset_span ⟨ν, hc, h, rfl⟩

private theorem ePartition_mem_Ege {d : ℕ} {κ ν : YoungDiagram} (hc : ν.card = d)
    (h : ν = κ ∨ LexLT κ ν) : ePartition ν ∈ Ege d κ :=
  Submodule.subset_span ⟨ν, hc, h, rfl⟩

/-- `s_κ ∈ H_{≥λ}` whenever `κ ≥ λ`: by (3.6), `s_κ` is `h_κ` plus `h_ν` with `ν ⊳ κ`. -/
theorem schur_mem_Hge {d : ℕ} (lam κ : DegreeShape d) (h : κ.val = lam.val ∨ LexLT lam.val κ.val) :
    (schur d κ : Q) ∈ EKTriangular.Hge lam.val := by
  have hup := EKProp310.up_of_upS (EKProp310.schur_sub_mem_upS d κ)
  refine map_mem_of_span (degreePiece d).subtype _ ?_ hup
  rintro _ ⟨ν, hν, rfl⟩
  simp only [Submodule.subtype_apply, degreeHBasis_apply]
  refine hPartition_mem_Hge (by rw [ν.property, lam.property]) ?_
  rcases EKProp310.lex_le_of_dom hν with he | hl
  · exact lex_ge_trans h (Or.inl he.symm)
  · exact lex_ge_trans h (Or.inr hl)

/-- `span{e_μ : μ > κ} ⊆ E_{≥τ}` whenever `κ ≥ τ`. -/
private theorem eAbove_le_Ege {d : ℕ} {κ τ : YoungDiagram} (h : κ = τ ∨ LexLT τ κ) {y : degreePiece d}
    (hy : y ∈ EKProp310.EAbove d κ) : (y : Q) ∈ Ege d τ := by
  refine map_mem_of_span (degreePiece d).subtype _ ?_ hy
  rintro _ ⟨μ, hμ, rfl⟩
  simp only [Submodule.subtype_apply, degreeEBasis_apply]
  exact ePartition_mem_Ege μ.property (lex_ge_trans h (Or.inr hμ))

/-- `s_κ ∈ E_{≥τ}` whenever `κᵀ ≥ τ`: `s_κ` is `±e_{κᵀ}` plus `e_μ` with `μ > κᵀ`. -/
theorem schur_mem_Ege {d : ℕ} (κ : DegreeShape d) (τ : YoungDiagram)
    (h : κ.val.transpose = τ ∨ LexLT τ κ.val.transpose) : (schur d κ : Q) ∈ Ege d τ := by
  have h1 := eAbove_le_Ege h
    (EKProp310.schur_sub_e_mem d (EKClosureComposition.identity311 d) κ)
  have h2 : ePartition κ.val.transpose ∈ Ege d τ :=
    ePartition_mem_Ege (transposeShape d κ).property h
  have := Submodule.add_mem _ h1 (Submodule.smul_mem _ (EKProp310.sgn κ.val) h2)
  simpa [degreeEBasis_apply] using this

/-- Two distinct odd Schur functions of the same degree are linearly independent, by (3.11). -/
theorem schur_pair_linearIndependent {d : ℕ} {a b : DegreeShape d} (hab : a ≠ b) :
    LinearIndependent ℤ ![(schur d a : Q), (schur d b : Q)] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hpair (c : DegreeShape d) := congrArg (fun x => quotientPairing x (schur d c : Q)) hst
  have h311 := EKClosureComposition.identity311 d
  have ha := hpair a
  have hb := hpair b
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    map_zero, LinearMap.zero_apply] at ha hb
  rw [h311, h311, if_pos rfl, if_neg (Ne.symm hab), mul_zero, add_zero] at ha
  rw [h311, h311, if_pos rfl, if_neg hab, mul_zero, zero_add] at hb
  have hs : (-1 : ℤ) ^ EKProp310Controls.transposeChoose a.val ≠ 0 := pow_ne_zero _ (by norm_num)
  have ht : (-1 : ℤ) ^ EKProp310Controls.transposeChoose b.val ≠ 0 := pow_ne_zero _ (by norm_num)
  exact ⟨(mul_eq_zero.mp ha).resolve_right hs, (mul_eq_zero.mp hb).resolve_right ht⟩

/-- A submodule containing two linearly independent elements is not spanned over `ℚ` by a single
element: there is no `v` such that every `x` in it has a nonzero multiple in `ℤ v`. -/
theorem not_one_dim_of_pair {S : Submodule ℤ Q} {x y : Q} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : LinearIndependent ℤ ![x, y]) :
    ¬ ∃ v : Q, ∀ z ∈ S, ∃ n : ℤ, n ≠ 0 ∧ n • z ∈ Submodule.span ℤ {v} := by
  rintro ⟨v, hv⟩
  obtain ⟨n, hn, hnx⟩ := hv x hx
  obtain ⟨m, hm, hmy⟩ := hv y hy
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hnx
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hmy
  have key : (b * n) • x + (-(a * m)) • y = 0 := by
    rw [mul_smul, ← ha, neg_smul, mul_smul, ← hb, smul_smul, smul_smul, mul_comm b a,
      add_neg_cancel]
  obtain ⟨h1, h2⟩ := (LinearIndependent.pair_iff.mp hxy) _ _ key
  have hb0 : b = 0 := (mul_eq_zero.mp h1).resolve_right hn
  have ha0 : a = 0 := (mul_eq_zero.mp (neg_eq_zero.mp h2)).resolve_right hm
  have := (LinearIndependent.pair_iff.mp hxy) n 0 (by rw [← ha, ha0, zero_smul, zero_smul,
    add_zero])
  exact hn this.1

/-! ## The shapes of degree 6 -/

open EKRestrictedPairing (lam33 mu411 nu3111 lamT222)

/-- `(3,3)`, `(4,1,1)`, `(2,2,2)`, `(3,1,1,1)` as partitions of `6`. -/
def sh33 : DegreeShape 6 := ⟨lam33, EKRestrictedPairing.lam33_card⟩
def sh411 : DegreeShape 6 := ⟨mu411, EKRestrictedPairing.mu411_card⟩
def sh222 : DegreeShape 6 := ⟨lamT222, by decide⟩
def sh3111 : DegreeShape 6 := ⟨nu3111, EKRestrictedPairing.nu3111_card⟩

private theorem transpose222 : lamT222.transpose = lam33 := by
  rw [← EKRestrictedPairing.transpose33, YoungDiagram.transpose_transpose]

private theorem transpose3111 : nu3111.transpose = mu411 := by
  rw [← EKRestrictedPairing.transpose411, YoungDiagram.transpose_transpose]

private theorem lex_222_33 : LexLT lamT222 lam33 := by
  show List.Lex (· < ·) lamT222.rowLens lam33.rowLens
  rw [EKRestrictedPairing.lamT222_rows, EKRestrictedPairing.lam33_rows]; decide

private theorem lex_222_3111 : LexLT lamT222 nu3111 := by
  show List.Lex (· < ·) lamT222.rowLens nu3111.rowLens
  rw [EKRestrictedPairing.lamT222_rows, EKRestrictedPairing.nu3111_rows]; decide

private theorem lex_33_411 : LexLT lam33 mu411 := EKRestrictedPairing.lex33_411

private theorem ne_33_411 : sh33 ≠ sh411 := by
  intro h
  have := congrArg (fun μ : DegreeShape 6 => μ.val.rowLens) h
  simp [sh33, sh411] at this

private theorem ne_222_3111 : sh222 ≠ sh3111 := by
  intro h
  have := congrArg (fun μ : DegreeShape 6 => μ.val.rowLens) h
  simp [sh222, sh3111] at this

/-! ## Proposition 3.10, p. 29, at `λ = (3,3)` -/

/-- [EK] proof of Prop. 3.10 at `λ = (3,3)`: `s_{(3,3)}` and `s_{(4,1,1)}` are linearly
independent elements of `H_{≥(3,3)} ∩ E_{≥(2,2,2)}`. -/
theorem prop_3_10_intersection :
    (schur 6 sh33 : Q) ∈ EKTriangular.Hge lam33 ⊓ Ege 6 lam33.transpose ∧
    (schur 6 sh411 : Q) ∈ EKTriangular.Hge lam33 ⊓ Ege 6 lam33.transpose ∧
    LinearIndependent ℤ ![(schur 6 sh33 : Q), (schur 6 sh411 : Q)] := by
  refine ⟨⟨schur_mem_Hge sh33 sh33 (Or.inl rfl), schur_mem_Ege sh33 _ (Or.inl rfl)⟩,
    ⟨schur_mem_Hge sh33 sh411 (Or.inr lex_33_411), schur_mem_Ege sh411 _ (Or.inr ?_)⟩,
    schur_pair_linearIndependent ne_33_411⟩
  show LexLT lam33.transpose mu411.transpose
  rw [EKRestrictedPairing.transpose33, EKRestrictedPairing.transpose411]
  exact lex_222_3111

/-- [EK] proof of Prop. 3.10: `(H_{≥λ} ∩ E_{≥λᵀ}) ⊗ ℚ` is not one-dimensional at `λ = (3,3)`. -/
theorem prop_3_10_not_one_dim :
    ¬ ∃ v : Q, ∀ z ∈ EKTriangular.Hge lam33 ⊓ Ege 6 lam33.transpose,
      ∃ n : ℤ, n ≠ 0 ∧ n • z ∈ Submodule.span ℤ {v} :=
  not_one_dim_of_pair prop_3_10_intersection.1 prop_3_10_intersection.2.1
    prop_3_10_intersection.2.2

/-! ## Lemma 3.11, pp. 29–30 -/

open EKAutomorphisms (psi12)

/-- `ψ₁ψ₂` as a `ℤ`-linear map. -/
abbrev psi12L : Q →ₗ[ℤ] Q := psi12.toRingHom.toIntAlgHom.toLinearMap

/-- [EK] (2.25): `ψ₁ψ₂(h_μ) = (−1)^{C(μ,2)+|μ|} e_μ`, with `C(μ,2) + |μ| = Σ_i C(μ_i+1,2)`. -/
theorem psi12_hPartition (μ : YoungDiagram) :
    psi12 (hPartition μ) = (-1 : ℤ)^((μ.rowLens.map (fun n => (n+1).choose 2)).sum) •
      ePartition μ :=
  EKAutomorphisms.psi12_hWord_source μ.rowLens

/-- [EK] (2.25): `ψ₁ψ₂(e_μ) = (−1)^{C(μ,2)+|μ|} h_μ`. -/
theorem psi12_ePartition (μ : YoungDiagram) :
    psi12 (ePartition μ) = (-1 : ℤ)^((μ.rowLens.map (fun n => (n+1).choose 2)).sum) •
      hPartition μ :=
  EKAutomorphisms.psi12_eWord_source μ.rowLens

/-- [EK] Lemma 3.11 proof, first display, corrected (`e_μ` in place of the printed `h_μ`): for
`x = h_λ + Σ_{μ>λ} a_μ h_μ`, `ψ₁ψ₂(x) = ±e_λ + Σ_{μ>λ} ±a_μ e_μ` with the signs of (2.25). -/
theorem lemma_3_11_first_display {d : ℕ} (lam : DegreeShape d) (a : DegreeShape d → ℤ)
    (U : Finset (DegreeShape d)) :
    psi12 (hPartition lam.val + ∑ μ ∈ U, a μ • hPartition μ.val) =
      (-1 : ℤ)^((lam.val.rowLens.map (fun n => (n+1).choose 2)).sum) • ePartition lam.val +
      ∑ μ ∈ U, ((-1 : ℤ)^((μ.val.rowLens.map (fun n => (n+1).choose 2)).sum) * a μ) •
        ePartition μ.val := by
  rw [map_add, map_sum, psi12_hPartition]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_zsmul, psi12_hPartition, smul_smul, mul_comm]

/-- [EK] Lemma 3.11 proof, corrected first display: `ψ₁ψ₂(s_λ) ∈ E_{≥λ}`. -/
theorem psi12_schur_mem_E {d : ℕ} (lam : DegreeShape d) :
    psi12 (schur d lam : Q) ∈ Ege d lam.val := by
  have hup := EKProp310.up_of_upS (EKProp310.schur_sub_mem_upS d lam)
  refine map_mem_of_span (psi12L.comp (degreePiece d).subtype) _ ?_ hup
  rintro _ ⟨ν, hν, rfl⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, degreeHBasis_apply]
  change psi12 (hPartition ν.val) ∈ _
  rw [psi12_hPartition]
  refine Submodule.smul_mem _ _ (ePartition_mem_Ege ν.property ?_)
  rcases EKProp310.lex_le_of_dom hν with he | hl
  · exact Or.inl he.symm
  · exact Or.inr hl

/-- [EK] Lemma 3.11 proof, second display: `ψ₁ψ₂(s_λ) ∈ H_{≥λᵀ}`. -/
theorem psi12_schur_mem_H {d : ℕ} (lam : DegreeShape d) :
    psi12 (schur d lam : Q) ∈ EKTriangular.Hge lam.val.transpose := by
  have hsub := EKProp310.schur_sub_e_mem d (EKClosureComposition.identity311 d) lam
  have hcard : lam.val.transpose.card = d := (transposeShape d lam).property
  have h1 : psi12 ((schur d lam - EKProp310.sgn lam.val • degreeEBasis d (transposeShape d lam) :
      degreePiece d) : Q) ∈ EKTriangular.Hge lam.val.transpose := by
    refine map_mem_of_span (psi12L.comp (degreePiece d).subtype) _ ?_ hsub
    rintro _ ⟨μ, hμ, rfl⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, degreeEBasis_apply]
    change psi12 (ePartition μ.val) ∈ _
    rw [psi12_ePartition]
    exact Submodule.smul_mem _ _ (hPartition_mem_Hge (by rw [μ.property, hcard]) (Or.inr hμ))
  have h2 : psi12 (ePartition lam.val.transpose) ∈ EKTriangular.Hge lam.val.transpose := by
    rw [psi12_ePartition]
    exact Submodule.smul_mem _ _ (hPartition_mem_Hge rfl (Or.inl rfl))
  have := Submodule.add_mem _ h1 (Submodule.smul_mem _ (EKProp310.sgn lam.val) h2)
  simp only [Submodule.coe_sub, Submodule.coe_smul, degreeEBasis_apply, EKProp310.transposeShape_val,
    map_sub, map_zsmul] at this
  simpa using this

/-- [EK] Lemma 3.11 proof, with the indices corrected: `ψ₁ψ₂(s_λ) ∈ H_{≥λᵀ} ∩ E_{≥λ}`, and
`ψ₁ψ₂(s_λ) = ±s_{λᵀ}` (Lemma 3.11, `EKFinalClosure.lemma_3_11`). -/
theorem psi12_schur_mem_corrected {d : ℕ} (lam : DegreeShape d) :
    psi12 (schur d lam : Q) ∈ EKTriangular.Hge lam.val.transpose ⊓ Ege d lam.val :=
  ⟨psi12_schur_mem_H lam, psi12_schur_mem_E lam⟩

/-- [EK] proof of Lemma 3.11 at `λ = (2,2,2)`, printed indices: `s_{λᵀ} = s_{(3,3)}` does not
lie in `E_{≥λᵀ} = E_{≥(3,3)}`, hence not in the printed `H_{≥λ} ∩ E_{≥λᵀ}`. Every element of
`E_{≥(3,3)}` is orthogonal to `s_{(3,3)}`, while `(s_{(3,3)}, s_{(3,3)}) = ±1`. -/
theorem lemma_3_11_printed_not_mem :
    (schur 6 sh33 : Q) ∉ EKTriangular.Hge lamT222 ⊓ Ege 6 lamT222.transpose := by
  rintro ⟨-, hE⟩
  rw [transpose222] at hE
  have horth : ∀ z ∈ Ege 6 lam33, quotientPairing (schur 6 sh33 : Q) z = 0 := by
    intro z hz
    have hle : Ege 6 lam33 ≤ LinearMap.ker (quotientPairing (schur 6 sh33 : Q)) := by
      rw [Ege, Submodule.span_le]
      rintro _ ⟨ν, hν, hl, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      have hlt : LexLT sh33.val.transpose ν := by
        show LexLT lam33.transpose ν
        rw [EKRestrictedPairing.transpose33]
        rcases hl with rfl | hl
        · exact lex_222_33
        · exact lt_trans lex_222_33 hl
      exact EKProp310.pair_schur_e_vanish 6 sh33 ⟨ν, hν⟩ hlt
    exact hle hz
  have hself := horth _ hE
  rw [EKClosureComposition.identity311 6 sh33 sh33, if_pos rfl] at hself
  exact pow_ne_zero _ (by norm_num) hself

/-- [EK] proof of Lemma 3.11 at `λ = (2,2,2)`, printed indices: the printed intersection
`H_{≥(2,2,2)} ∩ E_{≥(3,3)}` contains the linearly independent `s_{(2,2,2)}`, `s_{(3,1,1,1)}`. -/
theorem lemma_3_11_printed_intersection :
    (schur 6 sh222 : Q) ∈ EKTriangular.Hge lamT222 ⊓ Ege 6 lamT222.transpose ∧
    (schur 6 sh3111 : Q) ∈ EKTriangular.Hge lamT222 ⊓ Ege 6 lamT222.transpose ∧
    LinearIndependent ℤ ![(schur 6 sh222 : Q), (schur 6 sh3111 : Q)] := by
  refine ⟨⟨schur_mem_Hge sh222 sh222 (Or.inl rfl), schur_mem_Ege sh222 _ (Or.inl rfl)⟩,
    ⟨schur_mem_Hge sh222 sh3111 (Or.inr lex_222_3111), schur_mem_Ege sh3111 _ (Or.inr ?_)⟩,
    schur_pair_linearIndependent ne_222_3111⟩
  show LexLT lamT222.transpose nu3111.transpose
  rw [transpose222, transpose3111]
  exact lex_33_411

/-- [EK] proof of Lemma 3.11 at `λ = (2,2,2)`, corrected indices: the intersection
`H_{≥λᵀ} ∩ E_{≥λ} = H_{≥(3,3)} ∩ E_{≥(2,2,2)}`, which contains `ψ₁ψ₂(s_λ)`, is not
one-dimensional over `ℚ`, so it is not generated by `s_{λᵀ}`. -/
theorem lemma_3_11_not_one_dim :
    psi12 (schur 6 sh222 : Q) ∈ EKTriangular.Hge lamT222.transpose ⊓ Ege 6 lamT222 ∧
    ¬ ∃ v : Q, ∀ z ∈ EKTriangular.Hge lamT222.transpose ⊓ Ege 6 lamT222,
      ∃ n : ℤ, n ≠ 0 ∧ n • z ∈ Submodule.span ℤ {v} := by
  refine ⟨psi12_schur_mem_corrected sh222, ?_⟩
  rw [transpose222, ← EKRestrictedPairing.transpose33]
  exact prop_3_10_not_one_dim

end OddMath.Frontier.ErrataChecks
