import OddMath.Frontier.EKLSectionTwoF
import OddMath.Frontier.EKTriangular
import OddMath.Frontier.EKAntipode
import OddMath.Frontier.EKAppendixData

/-! EKL arXiv:1111.1320v1, §2.3, Remark 2.27, displays (2.73) and (2.74), p.20.

The Remark obtains further Pieri rules from (2.71) with EK's automorphism `ψ₁ψ₂` and
anti-involution `ψ₃` (EK arXiv:1107.5610v2, §2.3), citing EK for the signs `(-1)^{ℓ(w_α)}` and
`η_α`. EK defines `ℓ(w_α)` (Prop. 2.14) but no `η_α`, and `ψ₃` is not diagonal on Schur
functions: `ψ₃(s_{(1,1)}) = -s_{(1,1)} - 2 s_{(2)}` (`psi3_not_diagonal`). The ordinary
anti-involution `R` of `OΛ` fixing every `h_n` (`EKAutomorphisms.reverseLinear`; on degree `d`,
`R = (-1)^{C(d+1,2)} ψ₃ψ₂`) is diagonal: `R(s_λ) = η_λ s_λ` with
`η_λ = (-1)^{Σ_{i<j, λ_i > λ_j} λ_j (λ_i + 1)}` (`reverse_sK`). With this `η`, (2.73) and (2.74)
hold as printed, in `OΛ` (`left_vertical_pieri_Q`, `left_horizontal_pieri_Q`) and in every `OΛ_a`,
`a ≥ 2` (`left_vertical_pieri`, `left_horizontal_pieri`), by applying `R` to (2.71) and (2.72).

`reverse_sK`: `R` fixes every `e_n` (EK (2.5) and its dual), hence commutes with `ψ₁ψ₂`;
straightening an `h`-word only moves up in dominance (`word_dom`); so `R s_λ` lies in
`span{h_κ : κ ⊵ λ}` and, through `ψ₁ψ₂` and EK Lemma 3.11, pairs to zero with `s_ρ` unless
`ρ ⊴ λ`. By EK (3.11) only `ρ = λ` survives, with the leading sign of `h_{λ^rev}` (EK Lemma 2.16). -/

namespace OddMath.Frontier.EKLSectionTwo
open EKRadicalQuotient (Q)
open EKElementaryQuotient (h e)
open EKAutomorphisms (reverseLinear psi12 s)
open scoped BigOperators
noncomputable section
set_option synthInstance.maxHeartbeats 200000

/-- Applying `reverseLinear` to the inverse relation gives `Σ_i s_i h_{n-i} R(e_i) = δ_{n0}`. -/
theorem reverse_generator (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), h (n-i) * (s i • reverseLinear (e i))) = if n = 0 then 1 else 0 := by
  have hh := congrArg reverseLinear (EKAntipode.generator_left n)
  rw [map_sum, Fin.sum_univ_eq_sum_range (fun i => reverseLinear (EKAntipode.S (h i) * h (n-i)))]
    at hh
  simp only [EKAutomorphisms.reverse_mul, EKAutomorphisms.reverse_h, EKAntipode.S_h,
    map_zsmul] at hh
  rw [hh]
  split_ifs <;> simp

theorem dual_generator (n : ℕ) :
    (∑ i ∈ Finset.range (n+1), h (n-i) * (s i • e i)) = if n = 0 then 1 else 0 := by
  have hh := EKAntipode.generator_right n
  rw [Fin.sum_univ_eq_sum_range (fun i => h i * EKAntipode.S (h (n-i)))] at hh
  rw [← Finset.sum_range_reflect] at hh
  simp only [EKAntipode.S_h] at hh
  rw [← hh]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < n+1 := Finset.mem_range.mp hi
  rw [show n + 1 - 1 - i = n - i by omega, show n - (n - i) = i by omega]

/-- The ordinary reversal fixes the elementary generators: `R(e_n) = e_n`. -/
theorem reverse_e (n : ℕ) : reverseLinear (e n) = e n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  have h1 := reverse_generator n
  have h2 := dual_generator n
  rw [Finset.sum_range_succ] at h1 h2
  have hs : (∑ i ∈ Finset.range n, h (n-i) * (s i • reverseLinear (e i))) =
      ∑ i ∈ Finset.range n, h (n-i) * (s i • e i) :=
    Finset.sum_congr rfl fun i hi => by rw [ih i (Finset.mem_range.mp hi)]
  rw [hs, ← h2, add_right_inj, Nat.sub_self] at h1
  have h0 : h 0 = 1 := by simp [h]
  rw [h0, one_mul, one_mul] at h1
  have := congrArg (fun x : Q => s n • x) h1
  simpa only [smul_smul, EKAutomorphisms.s_square, one_smul] using this

theorem reverse_eWord (w : List ℕ) :
    reverseLinear ((w.map e).prod) = (w.reverse.map e).prod := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [List.map_cons, List.prod_cons, EKAutomorphisms.reverse_mul, reverse_e,
      ih, List.reverse_cons, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, List.map_nil, List.prod_nil, mul_one]

/-- `R` commutes with EK's involution `ψ₁ψ₂`. -/
theorem reverse_psi12 (x : Q) : reverseLinear (psi12 x) = psi12 (reverseLinear x) := by
  let f : Q →ₗ[ℤ] Q := reverseLinear.comp psi12.toRingHom.toIntAlgHom.toLinearMap
  let g : Q →ₗ[ℤ] Q := psi12.toRingHom.toIntAlgHom.toLinearMap.comp reverseLinear
  have hfg : f = g := by
    refine EKIntegralBases.hBasis.ext fun μ => ?_
    simp only [f, g, LinearMap.comp_apply, EKIntegralBases.hBasis_apply]
    change reverseLinear (psi12 ((μ.rowLens.map h).prod)) =
      psi12 (reverseLinear ((μ.rowLens.map h).prod))
    rw [EKAutomorphisms.psi12_hWord, map_zsmul, reverse_eWord, EKAutomorphisms.reverse_word,
      EKAutomorphisms.psi12_hWord, EKAutomorphisms.wordSign_reverse]
  exact LinearMap.congr_fun hfg x

/-! ### Dominance straightening of complete words -/

open EKPartitionSpanning (hPartition word g)
open EKLemma311Cond (Dom colPrefix)

/-- `Σ_i min(w_i, k)`: for a partition, the number of cells in the first `k` columns. -/
def colF (w : List ℕ) (k : ℕ) : ℕ := (w.map (fun x => min x k)).sum

/-- `span{h_μ : |μ| = d, colPrefix μ ≤ F}`. -/
def DomSpan (d : ℕ) (F : ℕ → ℕ) : Submodule ℤ Q :=
  Submodule.span ℤ {x | ∃ μ : YoungDiagram, μ.card = d ∧ (∀ k, colF μ.rowLens k ≤ F k) ∧
    hPartition μ = x}

theorem domSpan_mono {d : ℕ} {F G : ℕ → ℕ} (h : ∀ k, F k ≤ G k) : DomSpan d F ≤ DomSpan d G := by
  apply Submodule.span_mono
  rintro x ⟨μ, hd, hF, rfl⟩
  exact ⟨μ, hd, fun k => (hF k).trans (h k), rfl⟩

theorem colF_append (u v : List ℕ) (k : ℕ) : colF (u ++ v) k = colF u k + colF v k := by
  simp [colF, List.map_append, List.sum_append]

theorem colF_cons (a : ℕ) (w : List ℕ) (k : ℕ) : colF (a :: w) k = min a k + colF w k := by
  simp [colF]

theorem colF_filter (w : List ℕ) (k : ℕ) : colF (w.filter (· != 0)) k = colF w k := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    by_cases ha : a = 0
    · subst ha; simp [colF_cons, ← ih]
    · simp [ha, colF_cons, ih]

theorem colF_perm {u v : List ℕ} (hp : u.Perm v) (k : ℕ) : colF u k = colF v k :=
  (hp.map _).sum_eq

theorem colF_normal (w : List ℕ) (k : ℕ) : colF (EKTriangular.normal w) k = colF w k := by
  unfold EKTriangular.normal
  rw [colF_perm (List.perm_insertionSort _ _) k, colF_filter]

/-- Straightening an `h`-word only moves toward dominance: `h_w ∈ span{h_μ : μ ⊵ sort(w)}`,
expressed through column counts (a sum over the letters of `w`). -/
theorem word_dom (w : List ℕ) : word false w ∈ DomSpan w.sum (colF w) := by
  induction hc : EKPartitionSpanning.cost w using Nat.strong_induction_on generalizing w with
  | h n ih =>
    rcases EKPartitionSpanning.sorted_or_ascent w with hw | ⟨p, q, a, b, rfl, hab⟩
    · rw [EKTriangular.sorted_word_shape hw]
      exact Submodule.subset_span ⟨EKTriangular.shape w, EKTriangular.shape_card w,
        fun k => by rw [EKTriangular.shape_rows, colF_normal], rfl⟩
    · have hh := EKPartitionSpanning.pair_mem false
        (DomSpan (p++a::b::q).sum (colF (p++a::b::q)))
        (word false p) (word false q) a b (by omega) (fun u v huv hu => by
          have hcost := EKPartitionSpanning.cost_replace p q hab huv hu
          have hm := ih (EKPartitionSpanning.cost (p++u::v::q)) (by omega) (p++u::v::q) rfl
          have hd : (p++u::v::q).sum = (p++a::b::q).sum := by
            simp only [List.sum_append, List.sum_cons]; omega
          rw [hd] at hm
          have hmono : ∀ k, colF (p++u::v::q) k ≤ colF (p++a::b::q) k := by
            intro k
            simp only [colF_append, colF_cons]
            have : min u k + min v k ≤ min a k + min b k := by
              simp only [Nat.min_def]; split_ifs <;> omega
            omega
          have hm' := domSpan_mono hmono hm
          simpa only [EKPartitionSpanning.word_append, EKPartitionSpanning.word_cons,
            mul_assoc] using hm')
      simpa only [EKPartitionSpanning.word_append, EKPartitionSpanning.word_cons, mul_assoc]
        using hh

theorem filter_cellsOfRowLens_card (w : List ℕ) (k : ℕ) :
    ((YoungDiagram.cellsOfRowLens w).filter (fun p => p.2 < k)).card = colF w k := by
  induction w with
  | nil => simp [YoungDiagram.cellsOfRowLens, colF]
  | cons a w ih =>
    rw [YoungDiagram.cellsOfRowLens, Finset.filter_union, Finset.card_union_of_disjoint
      ((EKTriangular.row_cells_disjoint a w).mono (Finset.filter_subset _ _)
        (Finset.filter_subset _ _)), Finset.filter_map, Finset.card_map, colF_cons]
    congr 1
    have : (({0} : Finset ℕ) ×ˢ Finset.range a).filter (fun p => p.2 < k) =
        ({0} : Finset ℕ) ×ˢ Finset.range (min a k) := by
      ext ⟨i, j⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton, Finset.mem_range,
        lt_min_iff]
      tauto
    rw [this, Finset.card_product, Finset.card_singleton, Finset.card_range, one_mul]

theorem colF_rowLens (μ : YoungDiagram) (k : ℕ) : colF μ.rowLens k = colPrefix μ k := by
  rw [colPrefix, ← EKTriangular.cells_rows μ, filter_cellsOfRowLens_card]

theorem dom_of_colF {ν κ : YoungDiagram} (hc : κ.card = ν.card)
    (h : ∀ k, colF κ.rowLens k ≤ colF ν.rowLens k) : Dom ν κ := by
  have h1 : Dom κ.transpose ν.transpose := fun k => by
    rw [EKLemma311Cond.shapePrefix_transpose, EKLemma311Cond.shapePrefix_transpose,
      ← colF_rowLens, ← colF_rowLens]
    exact h k
  have h2 := EKLemma311Cond.dom_transpose (by rw [card_transpose, card_transpose, hc]) h1
  simpa only [YoungDiagram.transpose_transpose] using h2

/-! ### `R` on Schur functions -/

open DegreeShapes (DegreeShape degreeFintype)
open EKRadicalQuotient (quotientPairing)
open TableauDominance (signedKostka)
open OddLREKIdentification (sK)

/-- `span{h_κ : κ ⊵ λ}` in `OΛ`. -/
def UpQ (lam : YoungDiagram) : Submodule ℤ Q :=
  Submodule.span ℤ {x | ∃ κ : YoungDiagram, κ.card = lam.card ∧ Dom lam κ ∧ hPartition κ = x}

/-- `span{h_κ : κ ▷ λ}` in `OΛ`. -/
def UpSQ (lam : YoungDiagram) : Submodule ℤ Q :=
  Submodule.span ℤ {x | ∃ κ : YoungDiagram, κ.card = lam.card ∧ Dom lam κ ∧ κ ≠ lam ∧
    hPartition κ = x}

theorem reverse_hPartition (ν : YoungDiagram) :
    reverseLinear (hPartition ν) = word false ν.rowLens.reverse :=
  EKAutomorphisms.reverse_word ν.rowLens

theorem reverse_hPartition_mem (ν : YoungDiagram) :
    reverseLinear (hPartition ν) ∈
      Submodule.span ℤ {x | ∃ κ : YoungDiagram, κ.card = ν.card ∧ Dom ν κ ∧ hPartition κ = x} := by
  have hw := word_dom ν.rowLens.reverse
  rw [List.sum_reverse, EKIntegralBases.rowLens_sum] at hw
  rw [reverse_hPartition]
  refine (Submodule.span_le.mpr ?_) hw
  rintro _ ⟨κ, hd, hF, rfl⟩
  refine Submodule.subset_span ⟨κ, hd, dom_of_colF hd fun k => ?_, rfl⟩
  have := hF k
  rwa [colF_perm (List.reverse_perm _) k] at this

theorem reverse_upQ (lam : YoungDiagram) : ∀ y ∈ UpQ lam, reverseLinear y ∈ UpQ lam := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨κ, hd, hdom, rfl⟩ := hx
    refine (Submodule.span_le.mpr ?_) (reverse_hPartition_mem κ)
    rintro _ ⟨μ, hμ, hκμ, rfl⟩
    exact Submodule.subset_span ⟨μ, hμ.trans hd, EKLemma311Cond.dom_trans hdom hκμ, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ _ hx

theorem reverse_upSQ (lam : YoungDiagram) : ∀ y ∈ UpSQ lam, reverseLinear y ∈ UpSQ lam := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨κ, hd, hdom, hne, rfl⟩ := hx
    refine (Submodule.span_le.mpr ?_) (reverse_hPartition_mem κ)
    rintro _ ⟨μ, hμ, hκμ, rfl⟩
    refine Submodule.subset_span ⟨μ, hμ.trans hd, EKLemma311Cond.dom_trans hdom hκμ, ?_, rfl⟩
    rintro rfl
    exact hne (EKLemma311Cond.dom_antisymm hκμ hdom)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_zsmul]; exact Submodule.smul_mem _ _ hx

attribute [local instance] degreeFintype
local instance (d : ℕ) : DecidableEq (DegreeShape d) := Classical.decEq _

theorem schur_eq_sK {d : ℕ} (lam : DegreeShape d) :
    (EKLemma311CondControls.schur d lam : Q) = sK lam.val := by
  obtain ⟨μ, rfl⟩ := lam
  rfl

theorem sK_sub_mem_upSQ (lam : YoungDiagram) : sK lam - hPartition lam ∈ UpSQ lam := by
  have h := EKLemma311Cond.schur_sub_mem_upS lam.card ⟨lam, rfl⟩
  have key : ∀ y ∈ EKLemma311Cond.UpS lam.card ⟨lam, rfl⟩, (y : Q) ∈ UpSQ lam := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨ν, ⟨hν, hne⟩, rfl⟩ := hx
      refine Submodule.subset_span ⟨ν.val, ν.property, hν, fun he => hne (Subtype.ext he), ?_⟩
      rw [EKIntegralBases.degreeHBasis_apply]
    | zero => simp
    | add x y _ _ hx hy => rw [Submodule.coe_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [Submodule.coe_smul]; exact Submodule.smul_mem _ _ hx
  have := key _ h
  rwa [Submodule.coe_sub, EKIntegralBases.degreeHBasis_apply] at this

theorem upSQ_le_upQ (lam : YoungDiagram) : UpSQ lam ≤ UpQ lam := by
  apply Submodule.span_mono
  rintro x ⟨κ, hd, hdom, _, rfl⟩
  exact ⟨κ, hd, hdom, rfl⟩

theorem sK_mem_upQ (lam : YoungDiagram) : sK lam ∈ UpQ lam := by
  have h1 := upSQ_le_upQ lam (sK_sub_mem_upSQ lam)
  have h2 : hPartition lam ∈ UpQ lam := Submodule.subset_span ⟨lam, rfl, fun _ => le_rfl, rfl⟩
  simpa using Submodule.add_mem _ h1 h2

/-- EK (3.11), every degree. -/
theorem schurOrthonormal (d : ℕ) : EKLemma311CondControls.Identity311 d := EKClosureComposition.identity311 d

/-- `(s_ρ, h_κ) = (-1)^{C(ρᵀ,2)} K_{ρκ}`. -/
theorem pair_sK_h (rho κ : YoungDiagram) (hc : κ.card = rho.card) :
    quotientPairing (sK rho) (hPartition κ) =
      (-1 : ℤ) ^ EKLemma311CondControls.transposeChoose rho * signedKostka rho κ := by
  have := EKLemma311Cond.pair_schur_h rho.card (schurOrthonormal _) ⟨rho, rfl⟩ ⟨κ, hc⟩
  rwa [schur_eq_sK] at this

theorem pair_upQ (lam rho : YoungDiagram) (hc : rho.card = lam.card) (hd : ¬ Dom lam rho) :
    ∀ y ∈ UpQ lam, quotientPairing (sK rho) y = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨κ, hκ, hdom, rfl⟩ := hx
    rw [pair_sK_h rho κ (hκ.trans hc.symm)]
    by_cases hK : signedKostka rho κ = 0
    · rw [hK, mul_zero]
    · exact absurd (EKLemma311Cond.dom_trans hdom (EKLemma311Cond.dom_of_kostka_ne_zero hK)) hd
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_zsmul, hx, smul_zero]

theorem pair_upSQ (lam : YoungDiagram) : ∀ y ∈ UpSQ lam, quotientPairing (sK lam) y = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨κ, hκ, hdom, hne, rfl⟩ := hx
    rw [pair_sK_h lam κ hκ]
    by_cases hK : signedKostka lam κ = 0
    · rw [hK, mul_zero]
    · exact absurd (EKLemma311Cond.dom_antisymm hdom
        (EKLemma311Cond.dom_of_kostka_ne_zero hK)).symm hne
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_zsmul, hx, smul_zero]

theorem pair_psi12_upQ (lam rho : YoungDiagram) (hc : rho.card = lam.card)
    (hd : ¬ Dom rho lam.transpose) :
    ∀ y ∈ UpQ lam, quotientPairing (sK rho) (psi12 y) = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨ν, hν, hdom, rfl⟩ := hx
    rw [EKLemma311Cond.psi12_hPartition, map_zsmul]
    by_cases h0 : quotientPairing (sK rho) (EKPartitionSpanning.ePartition ν) = 0
    · rw [h0, smul_zero]
    · have h1 := EKLemma311Cond.pair_schur_e_dom rho.card ⟨rho, rfl⟩ ⟨ν, hν.trans hc.symm⟩
        (by rwa [schur_eq_sK])
      exact absurd (EKLemma311Cond.dom_trans h1
        (EKLemma311Cond.dom_transpose hν.symm hdom)) hd
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_zsmul, map_zsmul, hx, smul_zero]

theorem pair_strictSpan (lam : YoungDiagram) :
    ∀ y ∈ EKTriangular.strictSpan lam.card lam.rowLens, quotientPairing (sK lam) y = 0 := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨μ, hμ, hlt, rfl⟩ := hx
    rw [pair_sK_h lam μ hμ]
    by_cases hK : signedKostka lam μ = 0
    · rw [hK, mul_zero]
    · exfalso
      rcases EKLemma311Cond.lex_le_of_dom (EKLemma311Cond.dom_of_kostka_ne_zero hK) with he | hl
      · rw [he] at hlt; exact lt_irrefl _ hlt
      · exact lt_asymm hlt hl
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_zsmul, hx, smul_zero]

/-- The sign `η_λ` of Remark 2.27 (not defined in EK arXiv:1107.5610v2): the eigenvalue of the
ordinary reversal `R` on `s_λ`, `η_λ = (-1)^{Σ_{i<j, λ_i > λ_j} λ_j (λ_i + 1)}`, written via
the straightening exponent of the reversed row word. -/
def eta (lam : YoungDiagram) : ℤ := (-1 : ℤ) ^ EKTriangular.invExp lam.rowLens.reverse

theorem eta_sq (lam : YoungDiagram) : eta lam * eta lam = 1 := EKLemma311Cond.sign_mul_self _

/-- `(s_λ, R s_λ) = η_λ (-1)^{C(λᵀ,2)}`. -/
theorem pair_sK_reverse_self (lam : YoungDiagram) :
    quotientPairing (sK lam) (reverseLinear (sK lam)) =
      eta lam * (-1 : ℤ) ^ EKLemma311CondControls.transposeChoose lam := by
  have hsplit : reverseLinear (sK lam) =
      reverseLinear (hPartition lam) + reverseLinear (sK lam - hPartition lam) := by
    rw [← map_add, add_sub_cancel]
  rw [hsplit, map_add, pair_upSQ lam _ (reverse_upSQ lam _ (sK_sub_mem_upSQ lam)), add_zero]
  have hm := EKTriangular.word_leading lam.rowLens.reverse
  have hp := List.reverse_perm lam.rowLens
  rw [List.sum_reverse, EKIntegralBases.rowLens_sum, EKTriangular.normal_perm hp,
    EKTriangular.normal_partition, EKTriangular.shape_perm hp,
    EKTriangular.shape_partition] at hm
  have h0 := pair_strictSpan lam _ hm
  rw [map_sub, map_zsmul, sub_eq_zero] at h0
  rw [reverse_hPartition, h0, pair_sK_h lam lam rfl, TableauDominance.signedKostka_diag,
    mul_one, smul_eq_mul, eta]

/-- `(s_ρ, R s_λ) = 0` for `ρ ≠ λ`. -/
theorem pair_sK_reverse_ne (lam rho : YoungDiagram) (hc : rho.card = lam.card) (heq : rho ≠ lam) :
    quotientPairing (sK rho) (reverseLinear (sK lam)) = 0 := by
  by_cases hd : Dom lam rho
  · have hnd : ¬ Dom rho lam.transpose.transpose := by
      rw [YoungDiagram.transpose_transpose]
      exact fun h => heq (EKLemma311Cond.dom_antisymm h hd)
    have hps := OddGrassmannSchur.psi12_sK lam.transpose
    rw [YoungDiagram.transpose_transpose, card_transpose] at hps
    have hsk : sK lam = ((-1 : ℤ) ^ (EKSemiorthogonality.ell lam.transpose + lam.card)) •
        psi12 (sK lam.transpose) := by
      rw [hps, smul_smul, EKLemma311Cond.sign_mul_self, one_smul]
    rw [hsk, map_zsmul, reverse_psi12, map_zsmul,
      pair_psi12_upQ lam.transpose rho (hc.trans (card_transpose lam).symm) hnd _
        (reverse_upQ _ _ (sK_mem_upQ _)), smul_zero]
  · exact pair_upQ lam rho hc hd _ (reverse_upQ lam _ (sK_mem_upQ lam))

theorem sK_mem_degree (lam : YoungDiagram) : sK lam ∈ EKIntegralBases.degreePiece lam.card :=
  (OddLREKIdentification.schurK lam.card ⟨lam, rfl⟩).property

/-- The ordinary anti-involution `R` of `OΛ` (`R(h_n) = h_n`, `R(xy) = R(y)R(x)`) acts diagonally
on EK's Schur functions: `R(s_λ) = η_λ s_λ`. -/
theorem reverse_sK (lam : YoungDiagram) : reverseLinear (sK lam) = eta lam • sK lam := by
  have hxd := EKAutomorphisms.reverse_degree (sK_mem_degree lam)
  have hexp := congrArg Subtype.val (EKLemma311Cond.expansion lam.card (schurOrthonormal _) ⟨_, hxd⟩)
  simp only [Subtype.coe_mk] at hexp
  rw [hexp, Submodule.coe_sum]
  simp only [Submodule.coe_smul, schur_eq_sK]
  refine (Finset.sum_eq_single_of_mem (⟨lam, rfl⟩ : DegreeShape lam.card)
    (Finset.mem_univ (α := DegreeShape lam.card) _)
    fun b _ hb => ?_).trans ?_
  · rw [pair_sK_reverse_ne lam b.val b.property (fun he => hb (Subtype.ext he)), mul_zero,
      zero_smul]
  · rw [pair_sK_reverse_self, mul_left_comm, EKLemma311Cond.sign_mul_self, mul_one]

/-! ### `ψ₃` is not diagonal on Schur functions -/

theorem sum_degree_two [Fintype (DegreeShape 2)] (f : DegreeShape 2 → Q) :
    ∑ ν, f ν = f (EKAppendixData.hshapes2 0) + f (EKAppendixData.hshapes2 1) := by
  have hb : Function.Bijective EKAppendixData.hshapes2 :=
    ⟨EKAppendixData.inj2, fun ν => (EKAppendixData.exhaust2 ν).imp fun _ h => h.symm⟩
  rw [← Fintype.sum_bijective _ hb (f ∘ EKAppendixData.hshapes2) f (fun _ => rfl),
    Fin.sum_univ_two, Function.comp_apply, Function.comp_apply]

/-- `(1,1)` and `(2)`. -/
abbrev shape11 : YoungDiagram := (EKAppendixData.hshapes2 0).val
abbrev shape2 : YoungDiagram := (EKAppendixData.hshapes2 1).val

theorem hPartition_shape11 : hPartition shape11 = h 1 * h 1 := by
  change ((YoungDiagram.ofRowLens [1,1] (by decide)).rowLens.map h).prod = _
  rw [YoungDiagram.rowLens_ofRowLens_eq_self (by decide)]
  simp

theorem hPartition_shape2 : hPartition shape2 = h 2 := by
  change ((YoungDiagram.ofRowLens [2] (by decide)).rowLens.map h).prod = _
  rw [YoungDiagram.rowLens_ofRowLens_eq_self (by decide)]
  simp

theorem sK_shape2 : sK shape2 = h 2 := by
  have hd := congrArg Subtype.val (EKLemma311CondControls.schur_defining 2 (EKAppendixData.hshapes2 1))
  rw [Submodule.coe_sum, sum_degree_two] at hd
  simp only [Submodule.coe_smul, schur_eq_sK, EKIntegralBases.degreeHBasis_apply] at hd
  rw [show TableauDominance.signedKostka shape11 shape2 = 0 from EKAppendixData.kostka2_11_2,
    show TableauDominance.signedKostka shape2 shape2 = 1 from EKAppendixData.kostka2_2_2,
    zero_smul, zero_add, one_smul, hPartition_shape2] at hd
  exact hd.symm

theorem sK_shape11 : sK shape11 = h 1 * h 1 - h 2 := by
  have hd := congrArg Subtype.val (EKLemma311CondControls.schur_defining 2 (EKAppendixData.hshapes2 0))
  rw [Submodule.coe_sum, sum_degree_two] at hd
  simp only [Submodule.coe_smul, schur_eq_sK, EKIntegralBases.degreeHBasis_apply] at hd
  rw [show TableauDominance.signedKostka shape11 shape11 = 1 from EKAppendixData.kostka2_11_11,
    show TableauDominance.signedKostka shape2 shape11 = 1 from EKAppendixData.kostka2_2_11,
    one_smul, one_smul, hPartition_shape11, sK_shape2] at hd
  rw [hd]; abel

/-- `ψ₃(s_{(1,1)}) = -h₁² - h₂ = -s_{(1,1)} - 2 s_{(2)}`. -/
theorem psi3_sK_shape11 : EKAutomorphisms.psi3 (sK shape11) = -(h 1 * h 1) - h 2 := by
  have h11 := EKAutomorphisms.psi3_hWord [1, 1]
  simp [EKAutomorphisms.pairExponent] at h11
  rw [sK_shape11, map_sub, h11, EKAutomorphisms.psi3_h]

/-- EK's anti-involution `ψ₃` does not act on `s_{(1,1)}` by a scalar, so no sign `η_α` with
`ψ₃(s_α) = η_α s_α` exists. -/
theorem psi3_not_diagonal : ¬ ∃ c : ℤ, EKAutomorphisms.psi3 (sK shape11) = c • sK shape11 := by
  rintro ⟨c, hc⟩
  rw [psi3_sK_shape11, sK_shape11, ← hPartition_shape11, ← hPartition_shape2] at hc
  have h1 := congrArg (fun x => EKIntegralBases.hBasis.repr x shape11) hc
  have h2 := congrArg (fun x => EKIntegralBases.hBasis.repr x shape2) hc
  have hne : shape11 ≠ shape2 := fun he => by
    have := EKAppendixData.inj2 (Subtype.ext he)
    exact absurd this (by decide)
  simp only [map_sub, map_neg, map_zsmul, EKIntegralBases.h_coordinates_partition,
    Finsupp.sub_apply, Finsupp.neg_apply, Finsupp.smul_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hne, Finsupp.single_eq_of_ne hne.symm, smul_eq_mul] at h1 h2
  omega

/-! ### Remark 2.27: (2.73) and (2.74) -/

open OddLRVerticalPieri (Vertical stripBelow column)
open TableauStripCorners (Horizontal)
open EKSemiorthogonality (ell)
attribute [local instance] Classical.propDecidable

theorem column_rowLens (k : ℕ) : (column k).rowLens = List.replicate k 1 := by
  rw [List.eq_replicate_iff]
  refine ⟨by rw [YoungDiagram.length_rowLens, OddLRVerticalPieri.column_colLen], fun b hb => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
  have hi' : i < k := by
    have := hi
    rwa [YoungDiagram.length_rowLens, OddLRVerticalPieri.column_colLen] at this
  rw [YoungDiagram.get_rowLens, OddLRVerticalPieri.column_rowLen k i hi']

theorem eta_column (k : ℕ) : eta (column k) = 1 := by
  rw [eta, column_rowLens, List.reverse_replicate, EKTriangular.invExp_sorted, pow_zero]
  exact List.pairwise_replicate.mpr (Or.inr le_rfl)

theorem eta_row (k : ℕ) : eta (column k).transpose = 1 := by
  have hlen : (column k).transpose.rowLens.length ≤ 1 := by
    rw [YoungDiagram.length_rowLens, YoungDiagram.colLen_transpose]
    by_contra h
    push_neg at h
    have hm : (0, 1) ∈ column k := YoungDiagram.mem_iff_lt_rowLen.mpr h
    exact one_ne_zero ((OddLRVerticalPieri.mem_column k (0, 1)).mp hm).2
  unfold eta
  rcases hl : (column k).transpose.rowLens with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rfl
  · simp [EKTriangular.invExp]
  · rw [hl] at hlen; simp at hlen

/-- **EKL (2.73)** in `OΛ` (EK's `Q`), for every `α` and `k`:
`η_α s_{(1^k)} s_α = Σ_{μ/α vertical} (-1)^{|i₁/α|+⋯+|i_k/α|} η_μ s_μ`, with `η` = `eta`.
Obtained from (2.71) by the ordinary anti-involution `R` (`reverse_sK`); EK's `ψ₃` itself is
not diagonal on Schur functions. -/
theorem left_vertical_pieri_Q (α : YoungDiagram) (k : ℕ) :
    letI := degreeFintype (α.card + k)
    eta α • (sK (column k) * sK α) =
      ∑ mu : DegreeShape (α.card + k), if Vertical α mu.val then
        ((-1 : ℤ) ^ stripBelow α mu.val * eta mu.val) • sK mu.val else 0 := by
  letI := degreeFintype (α.card + k)
  have hv := congrArg reverseLinear (vertical_pieri_Q α k)
  rw [EKAutomorphisms.reverse_mul, reverse_sK, reverse_sK, eta_column, one_smul, map_sum,
    mul_smul_comm] at hv
  rw [hv]
  refine Finset.sum_congr rfl fun mu _ => ?_
  split_ifs
  · rw [map_zsmul, reverse_sK, smul_smul]
  · rw [map_zero]

/-- **EKL (2.74)** in `OΛ`, for every `α` and `k`:
`η_α (-1)^{ℓ(w_α)} s_{(k)} s_α = Σ_{μ/α horizontal} (-1)^{ℓ(w_μ)} (-1)^{|i₁/ᾱ|+⋯+|i_k/ᾱ|} η_μ s_μ`,
`(k) = (1^k)ᵀ`, obtained from (2.72) by `R`. -/
theorem left_horizontal_pieri_Q (α : YoungDiagram) (k : ℕ) :
    letI := degreeFintype (α.card + k)
    (eta α * (-1 : ℤ) ^ ell α) • (sK (column k).transpose * sK α) =
      ∑ mu : DegreeShape (α.card + k), if Horizontal α mu.val then
        ((-1 : ℤ) ^ ell mu.val * (-1 : ℤ) ^ stripRight α mu.val * eta mu.val) • sK mu.val
      else 0 := by
  letI := degreeFintype (α.card + k)
  have hv := congrArg reverseLinear (horizontal_pieri_Q α k)
  rw [map_zsmul, EKAutomorphisms.reverse_mul, reverse_sK, reverse_sK, eta_row, one_smul,
    map_sum, mul_smul_comm, smul_smul] at hv
  rw [mul_comm, hv]
  refine Finset.sum_congr rfl fun mu _ => ?_
  split_ifs
  · rw [map_zsmul, reverse_sK, smul_smul]
  · rw [map_zero]

/-- **EKL (2.73)** in `OΛ_a`, `a = n+2`, with the odd Schur polynomials of Definition 2.24
(`schurA`; shapes with more than `a` rows contribute `0`). -/
theorem left_vertical_pieri (n : ℕ) (α : YoungDiagram) (k : ℕ) :
    letI := degreeFintype (α.card + k)
    eta α • (schurA n (column k) * schurA n α) =
      ∑ mu : DegreeShape (α.card + k), if Vertical α mu.val then
        ((-1 : ℤ) ^ stripBelow α mu.val * eta mu.val) • schurA n mu.val else 0 := by
  letI := degreeFintype (α.card + k)
  have h := congrArg (OddLREKIdentification.piN (n+2)) (left_vertical_pieri_Q α k)
  simp only [map_zsmul, map_mul, map_sum, piN_sK_eq_schurA] at h
  rw [h]
  refine Finset.sum_congr rfl fun mu _ => ?_
  split_ifs
  · rw [map_zsmul, piN_sK_eq_schurA]
  · rw [map_zero]

/-- **EKL (2.74)** in `OΛ_a`, `a = n+2`, with `schurA`. -/
theorem left_horizontal_pieri (n : ℕ) (α : YoungDiagram) (k : ℕ) :
    letI := degreeFintype (α.card + k)
    (eta α * (-1 : ℤ) ^ ell α) • (schurA n (column k).transpose * schurA n α) =
      ∑ mu : DegreeShape (α.card + k), if Horizontal α mu.val then
        ((-1 : ℤ) ^ ell mu.val * (-1 : ℤ) ^ stripRight α mu.val * eta mu.val) • schurA n mu.val
      else 0 := by
  letI := degreeFintype (α.card + k)
  have h := congrArg (OddLREKIdentification.piN (n+2)) (left_horizontal_pieri_Q α k)
  simp only [map_zsmul, map_mul, map_sum, piN_sK_eq_schurA] at h
  rw [h]
  refine Finset.sum_congr rfl fun mu _ => ?_
  split_ifs
  · rw [map_zsmul, piN_sK_eq_schurA]
  · rw [map_zero]

end
end OddMath.Frontier.EKLSectionTwo
