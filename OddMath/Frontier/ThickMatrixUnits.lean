import OddMath.Frontier.ThickBubble
import OddMath.Frontier.ProjectorRank
import OddMath.Frontier.BoxPartitionCount
import OddMath.Frontier.OddSchurPieri
import OddMath.Frontier.FiniteCompleteElementary
import OddMath.Frontier.ThickDecomposition

/-! # The odd nilHecke algebra as a matrix algebra

EKL arXiv:1111.1320v1, §4.4, (4.37)–(4.50), Lemmas 4.13–4.14, Theorem 4.15, pp. 38–42.
Ambient ring `ONH_a = NilHeckeAction.Presented n`, `a = n+2`, strands `0, …, a-1`; a written
product `x * y` is `x` drawn on top of `y` (the rightmost factor acts first).

`Sq(a)` (4.37) is `BoxPartitionCount.Sq (n+2)`: `ℓ : Fin (n+1) → ℕ` with `ℓ ν ≤ ν+1`, where
`ℓ ν` is the paper's `ℓ_{ν+1}`.

* (4.38), with the splitters of (4.1) (`ThickBubble`): `S_ν = (e_ν ⊗ 1) X_{ν,1}` splits a thick
  `ν+1` strand into the thick strand `[0, ν)` and the thin strand `ν`, and `ε_k` on the thick
  strand `ν` is `e_ν ε_k e_ν` (`thickElem`), `ε_k` the odd elementary polynomial (2.16) of
  `x_0, …, x_{ν-1}` (`FiniteCompleteElementary.elementaryPoly`); on one strand `ε_k = x^k`.
  - `σ_ℓ = ε_{ℓ_1} S_1 ε_{ℓ_2} S_2 ⋯ ε_{ℓ_{a-1}} S_{a-1}` (`sigma`);
  - `λ_ℓ = (-1)^{C(a,3)} e_a x_{a-1}^{ℓ̂_{a-1}} ⋯ x_1^{ℓ̂_1}` with `ℓ̂_ν = ν - ℓ_ν` (`lam`):
    no dot on the leftmost strand, the dot on the rightmost strand drawn highest, as in (4.40).
  With this reading the printed statements hold without change of sign.
* (4.41) `eq_4_41`: Prop 4.11 with `b = 1` on the window `[0, ν+1)` (`prop_4_11_one`,
  transported by `OnhWindow.windowHom`) and `s_{(1^k)} = (-1)^{C(k,2)} ε_k`
  (`OddSchurPieri.schur_column`, EKL (2.70)).
* Lemma 4.13 (4.39) `lemma_4_13`: `λ_{ℓ'} σ_ℓ = δ_{ℓℓ'} e_a`, by induction on the number of strands
  (4.40), with `∑_{ν<a} C(ν,2) = C(a,3)`.
* Theorem 4.15 (4.48): `thm_4_15_orthogonal` (`e_ℓ e_{ℓ'} = δ_{ℓℓ'} e_ℓ`) and `thm_4_15_sum`
  (`∑_{ℓ ∈ Sq(a)} e_ℓ = 1`).  For the sum, instead of the induction (4.49)–(4.50), a graded rank
  count in the faithful polynomial representation (`GradedTrace.eq_sum_of_finrank`): `σ_ℓ` has
  degree `|ℓ| - C(a,2)`, `λ_ℓ` degree `C(a,2) - |ℓ|`, and the number of monomials of degree `d`
  is `∑_{ℓ ∈ Sq(a)} p_a(d - |ℓ|)` (`BoxPartitionCount.monomial_count`), where
  `p_a(m) = rk e_a(V_{m+C(a,2)})` is the number of partitions of `m` into at most `a` parts.
* Lemma 4.14 (4.43) `lemma_4_14`, in `ONH_{a+1}`: from Theorem 4.16 for `b = 1`
  (`ThickDecomposition.thm_4_16_right_one`), `P(a,1) = {(1^k)}` and `s_{(1^k)} = ±ε_k`. -/

namespace OddMath.Frontier.ThickMatrixUnits
open OddMath.SkewPolynomial (SkewPolynomial monomial generator)
open NilHeckeAction NilCoxeterWords NilHeckeBasis
open ZeroHecke OnhPolynomial OnhWindow StrandCrossing BoxComplement ThickBubble

noncomputable section

variable {n : ℕ}

/-! ## Transport along the window `[0, m+2)` -/

section Transport
variable {m : ℕ} (h : 0 + (m+2) ≤ n+2)

theorem natWord_map_shift (l : List ℕ) (hl : ∀ j ∈ l, j < m+1) :
    (natWord m l).map (shiftIndex h) = natWord n l := by
  induction l with
  | nil => rfl
  | cons j l ih =>
      obtain ⟨hj, hl⟩ := List.forall_mem_cons.mp hl
      have hj' : j < n+1 := by omega
      change (List.filterMap _ (j :: l)).map _ = List.filterMap _ (j :: l)
      simp only [List.filterMap_cons, dif_pos hj, dif_pos hj', List.map_cons]
      exact congrArg₂ List.cons (Fin.ext rfl) (ih hl)

theorem windowHom_blockE {k : ℕ} (hk : k ≤ m+2) :
    windowHom m n 0 h (blockE m 0 k) = blockE n 0 k := by
  rw [blockE, ThickBubble.windowHom_zeroHeckeProduct, blockE, triWord, triWord,
    natWord_map_shift h _ fun j hj => by have := mem_triList hj; omega]

theorem windowHom_crossWord {a b : ℕ} (hab : a + b ≤ m+2) :
    windowHom m n 0 h (product (crossWord m 0 a b)) = product (crossWord n 0 a b) := by
  rw [windowHom_product, crossWord, crossWord,
    natWord_map_shift h _ fun j hj => by have := mem_crossList hj; omega]

theorem windowHom_blockMono {p k : ℕ} (h₁ : p + k ≤ m+2) (h₂ : p + k ≤ n+2) (A : Fin k → ℕ) :
    windowHom m n 0 h (blockMono m p k h₁ A) = blockMono n p k h₂ A := by
  rw [blockMono, map_list_prod, List.map_map, blockMono]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply, map_pow, windowHom_dot]
  rfl

theorem windowHom_blockSchur {k : ℕ} (h₁ : 0 + k ≤ m+2) (h₂ : 0 + k ≤ n+2) (α : Fin k → ℕ) :
    windowHom m n 0 h (blockSchur m 0 k h₁ α) = blockSchur n 0 k h₂ α := by
  match k, h₁, h₂, α with
  | 0, h₁, h₂, α => exact windowHom_blockMono h h₁ h₂ α
  | 1, h₁, h₂, α => exact windowHom_blockMono h h₁ h₂ α
  | j+2, h₁, h₂, α => exact windowHom_comp_apply h₁ h h₂ _

theorem windowHom_polyElem (f : SkewPolynomial (m+2)) :
    windowHom m n 0 h (polyElem m f) = polyElem n (ProjectorRank.place 0 h f) := by
  obtain ⟨x, rfl⟩ := (PbwEquivalence.presentedEquiv (m+2)).surjective f
  have key : ((windowHom m n 0 h).comp (polyElem m)).comp
      (PbwEquivalence.presentedEquiv (m+2)).toRingHom =
      ((polyElem n).comp (ProjectorRank.place 0 h)).comp
        (PbwEquivalence.presentedEquiv (m+2)).toRingHom := by
    apply SignedPermutation.presentedHom_ext
    intro j
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, PbwEquivalence.presentedEquiv_apply]
    rw [OddMath.PbwL3.Phi_q, polyElem_generator, windowHom_dot, ProjectorRank.place_generator,
      polyElem_generator]
    rfl
  exact congrArg (fun φ => φ x) key

end Transport

/-! ## Definitions (4.38) -/

/-- The odd elementary symmetric polynomial `ε_k` (2.16) of the strands `[0, ν)`. -/
def epsWin (n ν k : ℕ) : Presented n :=
  if h : 0 + ν ≤ n+2 then
    polyElem n (ProjectorRank.place 0 h (FiniteCompleteElementary.elementaryPoly ν k))
  else 0

/-- `ε_k` on the thick strand `ν = [0, ν)`: `e_ν ε_k e_ν`. -/
def thickElem (n ν k : ℕ) : Presented n := blockE n 0 ν * epsWin n ν k * blockE n 0 ν

/-- The splitter (4.1) of a thick `ν+1` strand into a thick `ν` strand `[0, ν)` and the thin
strand `ν`: `(e_ν ⊗ 1) X_{ν,1}`. -/
def splitOne (n ν : ℕ) : Presented n := blockE n 0 ν * product (crossWord n 0 ν 1)

/-- The dot on strand `j` (`0` off the diagram). -/
def dotAt (n j : ℕ) : Presented n := if h : j < n+2 then dot n ⟨j, h⟩ else 0

/-- The lower part of `σ_ℓ` in (4.38), on the strands `[0, j+1)`:
`ε_{ℓ_1} S_1 ε_{ℓ_2} S_2 ⋯ ε_{ℓ_j} S_j`, where `ℓ_ν = ℓ (ν-1)` and `S_ν = splitOne n ν`. -/
def sigmaUpTo (n : ℕ) (ℓ : ℕ → ℕ) : ℕ → Presented n
  | 0 => 1
  | j+1 => sigmaUpTo n ℓ j * thickElem n (j+1) (ℓ j) * splitOne n (j+1)

/-- The dots of `λ_ℓ` in (4.38) on the strands `[0, j+1)`:
`x_j^{j - ℓ_j} ⋯ x_1^{1 - ℓ_1}` with `ℓ_ν = ℓ (ν-1)` and 0-based strands (the dot on the
rightmost strand drawn highest). -/
def dotsUpTo (n : ℕ) (ℓ : ℕ → ℕ) : ℕ → Presented n
  | 0 => 1
  | j+1 => dotAt n (j+1) ^ (j+1 - ℓ j) * dotsUpTo n ℓ j

/-- A sequence `ℓ_1 … ℓ_{a-1}` (0-based) extended by `0`. -/
def extend (ℓ : Fin (n+1) → ℕ) : ℕ → ℕ := fun i => if h : i < n+1 then ℓ ⟨i, h⟩ else 0

/-- EKL (4.38): `σ_ℓ`, thick `a = n+2` at the bottom exploded into thin strands, with `ε_{ℓ_ν}`
on the thick `ν` strand (`ℓ ν` is the paper's `ℓ_{ν+1}`). -/
def sigma (ℓ : Fin (n+1) → ℕ) : Presented n := sigmaUpTo n (extend ℓ) (n+1)

/-- EKL (4.38): `λ_ℓ = (-1)^{C(a,3)} e_a x_{a-1}^{ℓ̂_{a-1}} ⋯ x_1^{ℓ̂_1}` with
`ℓ̂_ν = ν - ℓ_ν` dots on the (0-based) strand `ν`. -/
def lam (ℓ : Fin (n+1) → ℕ) : Presented n :=
  (-1 : ℤ)^((n+2).choose 3) • (projector n * dotsUpTo n (extend ℓ) (n+1))

/-- Theorem 4.15: `e_ℓ = σ_ℓ λ_ℓ`. -/
def idem (ℓ : Fin (n+1) → ℕ) : Presented n := sigma ℓ * lam ℓ

/-! ## Block identities -/

theorem blockE_n (n : ℕ) : blockE n 0 (n+2) = projector n := by
  rw [blockE_eq (by omega), windowHom_id, RingHom.id_apply]

/-- `e_K e_k = e_K` for nested blocks `[0, k) ⊂ [0, K)`. -/
theorem blockE_mul_blockE_le {k K : ℕ} (hkK : k ≤ K) (hK : K ≤ n+2) :
    blockE n 0 K * blockE n 0 k = blockE n 0 K := by
  match K, hkK, hK with
  | 0, hkK, _ => obtain rfl : k = 0 := by omega
                 exact mul_one _
  | 1, hkK, _ =>
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> exact mul_one _
  | m+2, hkK, hK =>
      have h0 : 0 + (m+2) ≤ n+2 := by omega
      rw [blockE_eq h0, ← windowHom_blockE h0 hkK, ← map_mul, blockE,
        projector_mul_zeroHeckeProduct]

/-- The thin strand `ν` supercommutes past anything on `[0, ν)`: even `e_ν` commutes. -/
theorem dotAt_pow_mul_blockE {ν : ℕ} (hν : ν < n+2) (c : ℕ) :
    dotAt n ν ^ c * blockE n 0 ν = blockE n 0 ν * dotAt n ν ^ c := by
  rw [dotAt, dif_pos hν]
  exact (homog_comm_of_even (homog_blockE (by omega : 0 + ν ≤ n+2))
    (homog_pow (IsGen.dot (l := ν) (r := ν+1) ⟨ν, hν⟩ le_rfl (Nat.lt_succ_self ν)) c) (by omega)
    (Nat.even_mul.mpr (Or.inl (even_two_mul _)))).symm

/-! ## `s_{(1^k)} = (-1)^{C(k,2)} ε_k` on a block (EKL (2.70)) -/

/-- The column `(1^k)` in `ν` rows. -/
def col (ν k : ℕ) : Fin ν → ℕ := fun i => if i.val < k then 1 else 0

theorem col_antitone (ν k : ℕ) : Antitone (col ν k) := by
  intro i j hij
  have : i.val ≤ j.val := hij
  simp only [col]
  split_ifs <;> omega

theorem col_le (ν k : ℕ) (i : Fin ν) : col ν k i ≤ 1 := by
  simp only [col]; split_ifs <;> omega

theorem sum_col {ν k : ℕ} (hk : k ≤ ν) : ∑ i, col ν k i = k := by
  simp only [col]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < k then 1 else 0), Finset.sum_boole]
  have : (Finset.range ν).filter (· < k) = Finset.range k := by
    ext x; simp only [Finset.mem_filter, Finset.mem_range]; omega
  simp [this]

theorem epsWin_eq {ν k : ℕ} (hν : 1 ≤ ν) (h : 0 + ν ≤ n+2) (hk : k ≤ ν) :
    epsWin n ν k = (-1 : ℤ)^(k.choose 2) • blockSchur n 0 ν h (col ν k) := by
  rw [epsWin, dif_pos h]
  match ν, hν, h, hk with
  | 1, _, h, hk =>
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
      · simp [blockSchur_one, col]
      · rw [(blockSchur_one h _).1]
        simp [col, FiniteCompleteElementary.elementaryPoly, PlacticEvaluation.tildeGenerator,
          ProjectorRank.place_generator, polyElem_generator]
        rw [if_pos (Subsingleton.strictMono _), ProjectorRank.place_generator, polyElem_generator]
        rfl
  | m+2, _, h, hk =>
      have hs := OddSchurPieri.schur_column m k hk
      rw [blockSchur_eq, ← ThickDots.schur_eq_oddSymmetrizer] at *
      rw [show col (m+2) k = (OddSchurPieri.column m k).val from rfl, hs, map_zsmul, map_zsmul,
        windowHom_polyElem, smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul]

/-! ## Proposition 4.11 with `b = 1` on the window `[0, ν+1)` -/

theorem prop_4_11_one {ν : ℕ} (hν : 1 ≤ ν) (h : ν + 1 ≤ n+2) {α : Fin ν → ℕ}
    (hα : Antitone α) (hα1 : ∀ i, α i ≤ 1) {c : ℕ} (hc : c ≤ ν) :
    blockE n 0 (ν+1) * (blockE n 0 ν * blockSchur n 0 ν (by omega) α * blockE n 0 ν) *
        dotAt n ν ^ c * splitOne n ν =
      (if (fun _ : Fin 1 => c) = hat 1 α then (-1 : ℤ)^(bubbleSign ν 1 α) else 0) •
        blockE n 0 (ν+1) := by
  obtain ⟨m, rfl⟩ : ∃ m, ν = m+1 := ⟨ν - 1, by omega⟩
  have h0 : 0 + (m+2) ≤ n+2 := by omega
  have H := congrArg (windowHom m n 0 h0) (prop_4_11 (n := m) (a := m+1) (b := 1) rfl hα hα1
    (β := fun _ => c) (fun _ _ _ => le_rfl) (fun _ => hc))
  rw [merger, splitter, blockE_one, mul_one, one_mul, mul_one, (blockSchur_one _ _).2] at H
  simp only [map_mul, map_zsmul, map_pow, windowHom_dot] at H
  rw [← blockE_eq h0, windowHom_blockE h0 (by omega), windowHom_blockSchur h0 _ (by omega),
    windowHom_crossWord h0 (by omega)] at H
  rw [dotAt, dif_pos (by omega), splitOne]
  exact H

/-! ## The bubble (4.41) -/

theorem neg_one_pow_congr {X Y : ℕ} (h : X % 2 = Y % 2) : (-1 : ℤ)^X = (-1 : ℤ)^Y := by
  rw [neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

theorem sum_range_ite_lt (f : ℕ → ℕ) {k ν : ℕ} (hk : k ≤ ν) :
    ∑ i ∈ Finset.range ν, (if i < k then f i else 0) = ∑ i ∈ Finset.range k, f i := by
  induction ν, hk using Nat.le_induction with
  | base => exact Finset.sum_congr rfl fun i hi => if_pos (Finset.mem_range.mp hi)
  | succ ν hkν ih => rw [Finset.sum_range_succ, ih, if_neg (by omega), add_zero]

theorem hat_col (ν k : ℕ) : hat 1 (col ν k) = fun _ => ν - k := by
  funext j
  simp only [hat, col]
  rw [Finset.card_filter, Fin.sum_univ_eq_sum_range
    (fun i => if (if i < k then 1 else 0) ≤ 1 - 1 - j.val then 1 else 0), Finset.sum_boole]
  have : (Finset.range ν).filter (fun i => (if i < k then 1 else 0) ≤ 1 - 1 - j.val) =
      Finset.Ico k ν := by
    ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; split_ifs <;> omega
  rw [this, Nat.card_Ico, Nat.cast_id]

theorem blockChi_col {ν k : ℕ} (hν : 1 ≤ ν) (hk : k ≤ ν) :
    blockChi ν (col ν k) =
      ν.choose 3 + k * ν.choose 2 + ∑ i ∈ Finset.range k, (ν - i).choose 2 := by
  match ν, hν, hk with
  | 1, _, hk =>
      rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl <;> simp [blockChi, Nat.choose_eq_zero_of_lt]
  | m+2, _, hk =>
      rw [blockChi_eq, ThickDots.chi, sum_col hk, ← sum_range_ite_lt _ hk,
        ← Fin.sum_univ_eq_sum_range (fun i => if i < k then (m+2-i).choose 2 else 0)]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [col]
      split_ifs <;> simp

theorem hockey (k r : ℕ) :
    ∑ i ∈ Finset.range k, (k + r - i).choose 2 + (r+1).choose 3 = (k + r + 1).choose 3 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ', Finset.sum_congr rfl fun i _ =>
        (show (k + 1 + r - (i+1)).choose 2 = (k + r - i).choose 2 by congr 1; omega)]
      rw [show k + 1 + r - 0 = k + r + 1 by omega, add_right_comm, ih,
        show k + 1 + r + 1 = (k + r + 1) + 1 by omega, Nat.choose_succ_succ' (k + r + 1) 2]
      ring

theorem choose_two_add (k c : ℕ) : (c + k).choose 2 = c.choose 2 + k.choose 2 + c * k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [← add_assoc, Nat.choose_succ_succ', ih, Nat.choose_succ_succ' k, Nat.choose_one_right,
        Nat.choose_one_right]
      ring

theorem mul_choose_two (ν : ℕ) : ν * ν.choose 2 = 3 * ν.choose 3 + 2 * ν.choose 2 := by
  match ν with
  | 0 => simp
  | 1 => simp [Nat.choose_eq_zero_of_lt]
  | m+2 =>
      have h := Nat.choose_succ_right_eq (m+2) 2
      rw [show m + 2 - 2 = m by omega] at h
      linarith

/-- The sign of (4.41): `C(k,2) + |α||α̂| + X^{ν,1}_{(1^k)} ≡ C(ν,2)` for `k + c = ν`. -/
theorem sign_4_41 (k c : ℕ) :
    (k.choose 2 + (2 * (c+k).choose 2 + ((c+k).choose 2 + k) + (c+k).choose 2) * c +
      ((c+k).choose 3 + k * (c+k).choose 2 +
        ∑ i ∈ Finset.range k, (c + k - i).choose 2 + 0 + (c+k).choose 2 * (c + 0) +
          c.choose 3 + (c + k + 1).choose 3)) % 2 = (c+k).choose 2 % 2 := by
  have F1 := hockey k c
  rw [show k + c + 1 = c + k + 1 by omega] at F1
  have F1' : ∑ i ∈ Finset.range k, (c + k - i).choose 2 =
      ∑ i ∈ Finset.range k, (k + c - i).choose 2 :=
    Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm c k]
  have F2 : (c+1).choose 3 = c.choose 3 + c.choose 2 := by
    have := Nat.choose_succ_succ' c 2; simp only [Nat.reduceAdd] at this; omega
  have F3 : (c+k+1).choose 3 = (c+k).choose 3 + (c+k).choose 2 := by
    have := Nat.choose_succ_succ' (c+k) 2; simp only [Nat.reduceAdd] at this; omega
  have F4 := choose_two_add k c
  have F5 := mul_choose_two (c+k)
  have F6 : (2 * (c+k).choose 2 + ((c+k).choose 2 + k) + (c+k).choose 2) * c =
      4 * ((c+k).choose 2 * c) + c * k := by ring
  have F7 : k * (c+k).choose 2 + (c+k).choose 2 * (c + 0) = (c+k) * (c+k).choose 2 := by ring
  omega

/-- The thick box `e_ν s_{(1^k)} e_ν` has super-degree `≡ k`. -/
theorem homog_thickSchur {ν k : ℕ} (h : 0 + ν ≤ n+2) (hk : k ≤ ν) :
    Homog 0 (0+ν) (2 * ν.choose 2 + (ν.choose 2 + k) + ν.choose 2)
      (blockE n 0 ν * blockSchur n 0 ν h (col ν k) * blockE n 0 ν) := by
  rw [blockE_schur_blockE]
  refine Homog.zsmul ?_ _
  have := ((homog_blockE h).mul (homog_blockMono h (expA (col ν k)))).mul (homog_blockD h)
  rwa [sum_expA, sum_col hk] at this

theorem thickElem_eq {ν k : ℕ} (hν : 1 ≤ ν) (h : 0 + ν ≤ n+2) (hk : k ≤ ν) :
    thickElem n ν k =
      (-1 : ℤ)^(k.choose 2) • (blockE n 0 ν * blockSchur n 0 ν h (col ν k) * blockE n 0 ν) := by
  rw [thickElem, epsWin_eq hν h hk, mul_smul_comm, smul_mul_assoc]

/-- EKL (4.41): `e_{ν+1} (ε_k ⊗ x^c) (e_ν ⊗ 1) X_{ν,1} = δ_{c, ν-k} (-1)^{C(ν,2)} e_{ν+1}`
on the strands `[0, ν+1)`, `k, c ≤ ν`. -/
theorem eq_4_41 {ν k c : ℕ} (hν : 1 ≤ ν) (h : ν + 1 ≤ n+2) (hk : k ≤ ν) (hc : c ≤ ν) :
    blockE n 0 (ν+1) * dotAt n ν ^ c * thickElem n ν k * splitOne n ν =
      if c + k = ν then (-1 : ℤ)^(ν.choose 2) • blockE n 0 (ν+1) else 0 := by
  have h0 : 0 + ν ≤ n+2 := by omega
  set T := blockE n 0 ν * blockSchur n 0 ν h0 (col ν k) * blockE n 0 ν with hT
  have hx : Homog ν (ν+1) c (dotAt n ν ^ c) := by
    rw [dotAt, dif_pos (by omega)]
    exact homog_pow (IsGen.dot (l := ν) (r := ν+1) ⟨ν, by omega⟩ le_rfl (Nat.lt_succ_self ν)) c
  have hsw := homog_supercomm_zsmul (homog_thickSchur h0 hk) hx (by omega)
  have hswap : dotAt n ν ^ c * T = (-1 : ℤ)^((2 * ν.choose 2 + (ν.choose 2 + k) +
      ν.choose 2) * c) • (T * dotAt n ν ^ c) := by
    rw [hsw, smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul]
  rw [thickElem_eq hν h0 hk, ← hT, mul_smul_comm, smul_mul_assoc, mul_assoc _ (dotAt n ν ^ c),
    hswap, mul_smul_comm, smul_mul_assoc, ← mul_assoc (blockE n 0 (ν+1)) T, hT,
    prop_4_11_one hν h (col_antitone ν k) (col_le ν k) hc, hat_col, smul_smul]
  by_cases hck : c + k = ν
  · have hfun : (fun _ : Fin 1 => c) = fun _ => ν - k := funext fun _ => by omega
    rw [if_pos hfun, if_pos hck, smul_smul, ← pow_add]
    congr 1
    obtain rfl := hck
    rw [← pow_add]
    apply neg_one_pow_congr
    have := sign_4_41 k c
    simp only [bubbleSign, blockChi_col hν hk, hat_col, StaircaseEvaluation.omega,
      Finset.univ_unique, Finset.sum_singleton] at this ⊢
    simp only [blockChi, Nat.add_sub_cancel, Fin.default_eq_zero, Fin.val_zero, zero_add,
      Nat.choose_eq_zero_of_lt (by norm_num : 1 < 2), add_zero] at this ⊢
    exact this
  · have hfun : ¬ (fun _ : Fin 1 => c) = fun _ => ν - k :=
      fun e => hck (by have := congrFun e 0; omega)
    rw [if_neg hfun, if_neg hck, zero_smul, smul_zero]

/-! ## Lemma 4.13 -/

theorem blockE_mul_thickElem (ν k : ℕ) (h : 0 + ν ≤ n+2) :
    blockE n 0 ν * thickElem n ν k = thickElem n ν k := by
  rw [thickElem, ← mul_assoc, ← mul_assoc, blockE_mul_blockE h]

/-- The induction behind (4.40): on the strands `[0, j+1)`,
`e_{j+1} x_j^{j-ℓ'_j} ⋯ x_1^{1-ℓ'_1} · ε_{ℓ_1} S_1 ⋯ ε_{ℓ_j} S_j =
δ_{ℓ ℓ'} (-1)^{C(j+1,3)} e_{j+1}`. -/
theorem lambda_sigma_upTo (ℓ ℓ' : ℕ → ℕ) :
    ∀ j, j + 1 ≤ n+2 → (∀ i < j, ℓ i ≤ i+1) → (∀ i < j, ℓ' i ≤ i+1) →
      blockE n 0 (j+1) * dotsUpTo n ℓ' j * sigmaUpTo n ℓ j =
        if ∀ i < j, ℓ' i = ℓ i then (-1 : ℤ)^((j+1).choose 3) • blockE n 0 (j+1) else 0
  | 0, _, _, _ => by simp [dotsUpTo, sigmaUpTo, blockE_one, Nat.choose_eq_zero_of_lt]
  | j+1, hj, hℓ, hℓ' => by
      have ih := lambda_sigma_upTo ℓ ℓ' j (by omega) (fun i hi => hℓ i (by omega))
        (fun i hi => hℓ' i (by omega))
      set x := dotAt n (j+1) ^ (j+1 - ℓ' j)
      have hins : blockE n 0 (j+2) * x = blockE n 0 (j+2) * x * blockE n 0 (j+1) := by
        rw [mul_assoc, dotAt_pow_mul_blockE (by omega), ← mul_assoc,
          blockE_mul_blockE_le (by omega) hj]
      have key : blockE n 0 (j+1+1) * dotsUpTo n ℓ' (j+1) * sigmaUpTo n ℓ (j+1) =
          blockE n 0 (j+2) * x * (blockE n 0 (j+1) * dotsUpTo n ℓ' j * sigmaUpTo n ℓ j) *
            thickElem n (j+1) (ℓ j) * splitOne n (j+1) := by
        rw [dotsUpTo, sigmaUpTo]
        calc _ = blockE n 0 (j+2) * x * (dotsUpTo n ℓ' j * sigmaUpTo n ℓ j) *
              thickElem n (j+1) (ℓ j) * splitOne n (j+1) := by simp only [x, mul_assoc]
          _ = _ := by conv_lhs => rw [hins]
                      simp only [mul_assoc]
      rw [key, ih]
      have hstep := eq_4_41 (n := n) (ν := j+1) (k := ℓ j) (c := j+1 - ℓ' j) (by omega) hj
        (hℓ j (by omega)) (by omega)
      by_cases hprev : ∀ i < j, ℓ' i = ℓ i
      · rw [if_pos hprev, mul_smul_comm, smul_mul_assoc, smul_mul_assoc,
          mul_assoc _ (blockE n 0 (j+1)), blockE_mul_thickElem _ _ (by omega), hstep]
        by_cases hj' : ℓ' j = ℓ j
        · have hall : ∀ i < j+1, ℓ' i = ℓ i := fun i hi => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
            · exact hprev i hi
            · exact hj'
          rw [if_pos (by have := hℓ' j (by omega); omega), if_pos hall, smul_smul, ← pow_add]
          congr 2
          rw [show j + 1 + 1 = (j+1) + 1 from rfl, Nat.choose_succ_succ' (j+1) 2]
          simp only [Nat.reduceAdd]
          ring
        · have hnot : ¬ ∀ i < j+1, ℓ' i = ℓ i := fun hall => hj' (hall j (by omega))
          rw [if_neg (by have := hℓ' j (by omega); have := hℓ j (by omega); omega), if_neg hnot,
            smul_zero]
      · have hnot : ¬ ∀ i < j+1, ℓ' i = ℓ i := fun hall => hprev fun i hi => hall i (by omega)
        rw [if_neg hprev, if_neg hnot, mul_zero, zero_mul, zero_mul]

/-- EKL Lemma 4.13 (4.39): `λ_{ℓ'} σ_ℓ = δ_{ℓ ℓ'} e_a` for `ℓ, ℓ' ∈ Sq(a)`. -/
theorem lemma_4_13 {ℓ ℓ' : Fin (n+1) → ℕ} (hℓ : ∀ ν, ℓ ν ≤ ν.val + 1)
    (hℓ' : ∀ ν, ℓ' ν ≤ ν.val + 1) :
    lam ℓ' * sigma ℓ = if ℓ' = ℓ then projector n else 0 := by
  have ext_le : ∀ (m : Fin (n+1) → ℕ), (∀ ν : Fin (n+1), m ν ≤ ν.val + 1) →
      ∀ i < n+1, extend m i ≤ i + 1 := fun m hm i hi => by
    rw [extend, dif_pos hi]; exact hm _
  have H := lambda_sigma_upTo (n := n) (extend ℓ) (extend ℓ') (n+1) le_rfl (ext_le ℓ hℓ)
    (ext_le ℓ' hℓ')
  rw [blockE_n] at H
  rw [lam, sigma, smul_mul_assoc, mul_assoc, ← mul_assoc, H]
  have hiff : (∀ i < n+1, extend ℓ' i = extend ℓ i) ↔ ℓ' = ℓ := by
    constructor
    · intro hall; funext ν
      have := hall ν.val ν.isLt
      simp only [extend, dif_pos ν.isLt] at this
      exact this
    · rintro rfl i _; rfl
  by_cases he : ℓ' = ℓ
  · rw [if_pos (hiff.mpr he), if_pos he, smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩,
      one_smul]
  · rw [if_neg (fun h => he (hiff.mp h)), if_neg he, smul_zero]

/-! ## Theorem 4.15: orthogonality -/

theorem projector_mul_lam (ℓ : Fin (n+1) → ℕ) : projector n * lam ℓ = lam ℓ := by
  rw [lam, mul_smul_comm, ← mul_assoc, projector_mul_projector]

/-- EKL Theorem 4.15 (4.48), first half: `e_ℓ e_{ℓ'} = δ_{ℓ ℓ'} e_ℓ`. -/
theorem thm_4_15_orthogonal {ℓ ℓ' : Fin (n+1) → ℕ} (hℓ : ∀ ν, ℓ ν ≤ ν.val + 1)
    (hℓ' : ∀ ν, ℓ' ν ≤ ν.val + 1) :
    idem ℓ * idem ℓ' = if ℓ = ℓ' then idem ℓ else 0 := by
  rw [idem, idem, mul_assoc, ← mul_assoc (lam ℓ), lemma_4_13 hℓ' hℓ]
  by_cases he : ℓ = ℓ'
  · subst he
    rw [if_pos rfl, if_pos rfl, projector_mul_lam]
  · rw [if_neg he, if_neg he, zero_mul, mul_zero]

/-! ## Degrees in the polynomial representation -/

section Degrees
open GradedTrace ProjectorRank

theorem hasDegree_congr {a b : ℤ} {T : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2)}
    (h : HasDegree (Vd (n+2)) a T) (e : a = b) : HasDegree (Vd (n+2)) b T := e ▸ h

theorem hasDegree_blockE (p k : ℕ) : HasDegree (Vd (n+2)) 0 (action n (blockE n p k)) :=
  hasDegree_zeroHeckeProduct _

theorem hasDegree_dot_pow (j : Fin (n+2)) (e : ℕ) :
    HasDegree (Vd (n+2)) (e : ℤ) (action n (dot n j ^ e)) := by
  induction e with
  | zero => simpa using hasDegree_action_one (n := n)
  | succ e ih =>
      rw [pow_succ]
      exact hasDegree_congr (hasDegree_action_mul ih (hasDegree_dot j)) (by push_cast; ring)

theorem hasDegree_blockMono {p k : ℕ} (h : p + k ≤ n+2) (A : Fin k → ℕ) :
    HasDegree (Vd (n+2)) ((∑ i, A i : ℕ) : ℤ) (action n (blockMono n p k h A)) := by
  have key : ∀ l : List (Fin k), HasDegree (Vd (n+2)) (((l.map A).sum : ℕ) : ℤ)
      (action n ((l.map fun i => dot n (shiftFin h i) ^ A i).prod)) := by
    intro l
    induction l with
    | nil => simpa using hasDegree_action_one (n := n)
    | cons i l ih =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons]
        exact hasDegree_congr (hasDegree_action_mul (hasDegree_dot_pow _ _) ih) (by push_cast; ring)
  rw [Fin.sum_univ_def]
  exact key _

theorem hasDegree_blockD {p k : ℕ} (h : p + k ≤ n+2) :
    HasDegree (Vd (n+2)) (-((k.choose 2 : ℕ) : ℤ)) (action n (blockD n p k)) := by
  rw [← length_triWord h]
  exact hasDegree_product _

theorem length_crossWord_one (ν : ℕ) (h : ν + 1 ≤ n+2) : (crossWord n 0 ν 1).length = ν := by
  rw [← List.length_map (f := Fin.val), natWord_values n _ fun j hj => by
    have := mem_crossList hj; omega]
  simp [crossList, downList]

theorem hasDegree_splitOne {ν : ℕ} (h : ν + 1 ≤ n+2) :
    HasDegree (Vd (n+2)) (-(ν : ℤ)) (action n (splitOne n ν)) := by
  have := hasDegree_action_mul (hasDegree_blockE (n := n) 0 ν)
    (hasDegree_product (crossWord n 0 ν 1))
  rw [length_crossWord_one ν h, zero_add] at this
  exact this

theorem hasDegree_thickElem {ν k : ℕ} (hν : 1 ≤ ν) (h : 0 + ν ≤ n+2) (hk : k ≤ ν) :
    HasDegree (Vd (n+2)) (k : ℤ) (action n (thickElem n ν k)) := by
  rw [thickElem_eq hν h hk, blockE_schur_blockE, map_zsmul, map_zsmul]
  refine hasDegree_smul _ (hasDegree_smul _ ?_)
  have := hasDegree_action_mul (hasDegree_action_mul (hasDegree_blockE (n := n) 0 ν)
    (hasDegree_blockMono h (expA (col ν k)))) (hasDegree_blockD (p := 0) h)
  rw [sum_expA, sum_col hk] at this
  exact hasDegree_congr this (by push_cast; ring)

/-- The degree `|ℓ| - C(j+1,2)` of `σ` on `[0, j+1)`. -/
def sigmaDeg (ℓ : ℕ → ℕ) (j : ℕ) : ℤ := ∑ i ∈ Finset.range j, ((ℓ i : ℤ) - (i + 1))

theorem hasDegree_sigmaUpTo (ℓ : ℕ → ℕ) :
    ∀ j, j + 1 ≤ n+2 → (∀ i < j, ℓ i ≤ i+1) →
      HasDegree (Vd (n+2)) (sigmaDeg ℓ j) (action n (sigmaUpTo n ℓ j))
  | 0, _, _ => by simpa [sigmaDeg, sigmaUpTo] using hasDegree_action_one (n := n)
  | j+1, hj, hℓ => by
      have ih := hasDegree_sigmaUpTo ℓ j (by omega) fun i hi => hℓ i (by omega)
      have := hasDegree_action_mul (hasDegree_action_mul ih
        (hasDegree_thickElem (n := n) (ν := j+1) (k := ℓ j) (by omega) (by omega)
          (hℓ j (by omega)))) (hasDegree_splitOne (n := n) (ν := j+1) hj)
      refine hasDegree_congr this ?_
      rw [sigmaDeg, sigmaDeg, Finset.sum_range_succ]
      push_cast; ring

theorem hasDegree_dotsUpTo (ℓ : ℕ → ℕ) :
    ∀ j, j + 1 ≤ n+2 → (∀ i < j, ℓ i ≤ i+1) →
      HasDegree (Vd (n+2)) (-sigmaDeg ℓ j) (action n (dotsUpTo n ℓ j))
  | 0, _, _ => by simpa [sigmaDeg, dotsUpTo] using hasDegree_action_one (n := n)
  | j+1, hj, hℓ => by
      have ih := hasDegree_dotsUpTo ℓ j (by omega) fun i hi => hℓ i (by omega)
      have hd : dotAt n (j+1) = dot n ⟨j+1, by omega⟩ := dif_pos (by omega)
      have := hasDegree_action_mul (hasDegree_dot_pow (n := n) ⟨j+1, by omega⟩ (j+1 - ℓ j)) ih
      rw [← hd] at this
      refine hasDegree_congr this ?_
      have := hℓ j (by omega)
      rw [sigmaDeg, sigmaDeg, Finset.sum_range_succ, Nat.cast_sub this]
      push_cast; ring

end Degrees

/-! ## Theorem 4.15: completeness -/

section Completeness
open GradedTrace ProjectorRank Module

theorem card_index (N d : ℕ) :
    Fintype.card (ElementaryBasis.Index N d) = BoxPartitionCount.pcount N d := by
  rw [BoxPartitionCount.pcount, BoxPartitionCount.partitions]
  exact Fintype.card_of_subtype _ fun a => by
    simp [Finset.Nat.mem_antidiagonalTuple, and_comm]

theorem sum_range_succ_cast (m : ℕ) :
    ∑ i ∈ Finset.range m, ((i : ℤ) + 1) = (((m+1).choose 2 : ℕ) : ℤ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ' (m+1) 1, Nat.choose_one_right]
      push_cast; ring

theorem sigmaDeg_extend (ℓ : Fin (n+1) → ℕ) :
    sigmaDeg (extend ℓ) (n+1) = ((∑ ν, ℓ ν : ℕ) : ℤ) - (((n+2).choose 2 : ℕ) : ℤ) := by
  rw [sigmaDeg, Finset.sum_sub_distrib, sum_range_succ_cast]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun i => (extend ℓ i : ℤ)) (n+1)]
  push_cast
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp [extend]

theorem ext_le {ℓ : Fin (n+1) → ℕ} (hℓ : ∀ ν : Fin (n+1), ℓ ν ≤ ν.val + 1) :
    ∀ i < n+1, extend ℓ i ≤ i + 1 := fun i hi => by
  rw [extend, dif_pos hi]; exact hℓ _

theorem hasDegree_sigma {ℓ : Fin (n+1) → ℕ} (hℓ : ∀ ν : Fin (n+1), ℓ ν ≤ ν.val + 1) :
    HasDegree (Vd (n+2)) (sigmaDeg (extend ℓ) (n+1)) (action n (sigma ℓ)) :=
  hasDegree_sigmaUpTo _ _ le_rfl (ext_le hℓ)

theorem hasDegree_lam {ℓ : Fin (n+1) → ℕ} (hℓ : ∀ ν : Fin (n+1), ℓ ν ≤ ν.val + 1) :
    HasDegree (Vd (n+2)) (-sigmaDeg (extend ℓ) (n+1)) (action n (lam ℓ)) := by
  rw [lam, map_zsmul]
  exact hasDegree_smul _ (hasDegree_congr (hasDegree_action_mul hasDegree_projector
    (hasDegree_dotsUpTo _ _ le_rfl (ext_le hℓ))) (zero_add _))

/-- The graded rank count: `#{monomials of degree d} = ∑_{ℓ ∈ Sq(a)} rk e_a(V_{d + C(a,2) - |ℓ|})`
(`BoxPartitionCount.monomial_count`). -/
theorem finrank_count (d : ℤ) :
    finrank ℤ ((Vd (n+2) d).map (action n 1)) =
      ∑ i : BoxPartitionCount.Sq (n+2), finrank ℤ ((Vd (n+2) (d - sigmaDeg (extend i.1) (n+1))).map
        (action n (projector n))) := by
  rw [map_one, Module.End.one_eq_id, Submodule.map_id, finrank_Vd]
  simp only [finrank_map_projector, sigmaDeg_extend]
  rcases lt_or_le d 0 with hd | hd
  · have : expSet (n+2) d = ∅ := by
      rw [expSet, Finset.filter_false_of_mem fun _ _ => by omega]
    rw [this, Finset.card_empty]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg (by omega)]
  · obtain ⟨D, rfl⟩ : ∃ D : ℕ, d = D := ⟨d.toNat, by omega⟩
    rw [expSet, Finset.filter_true_of_mem fun _ _ => by omega, Int.toNat_natCast,
      BoxPartitionCount.monomial_count, Finset.sum_filter,
      ← Finset.sum_coe_sort (BoxPartitionCount.Sq (n+2))]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (∑ ν : Fin (n+1), i.1 ν) = ∑ ν : Fin (n+2-1), i.1 ν := rfl
    by_cases hi : ∑ ν, i.1 ν ≤ D
    · rw [if_pos hi, if_pos (by omega), card_index]
      congr 1
      omega
    · rw [if_neg hi, if_neg (by omega)]

/-- EKL Theorem 4.15 (4.48), second half: `∑_{ℓ ∈ Sq(a)} e_ℓ = 1` in `ONH_a`. -/
theorem thm_4_15_sum : ∑ ℓ ∈ BoxPartitionCount.Sq (n+2), idem (n := n) ℓ = 1 := by
  have hb : ∀ i : BoxPartitionCount.Sq (n+2), ∀ ν : Fin (n+1), i.1 ν ≤ ν.val + 1 :=
    fun i => BoxPartitionCount.mem_Sq.mp i.2
  have H := eq_sum_of_finrank (Vd := Vd (n+2)) (s := fun i : BoxPartitionCount.Sq (n+2) =>
      sigmaDeg (extend i.1) (n+1)) (σ := fun i => action n (sigma i.1))
    (ρ := fun i => action n (lam i.1)) (P := action n 1) (e := action n (projector n))
    (iSup_Vd (n+2)) hasDegree_action_one hasDegree_projector
    (fun i => hasDegree_sigma (hb i)) (fun i => hasDegree_lam (hb i))
    (by rw [← Module.End.mul_eq_comp, ← map_mul, one_mul]) projector_idem
    (fun i => by rw [← Module.End.mul_eq_comp, ← map_mul, lemma_4_13 (hb i) (hb i), if_pos rfl])
    (fun i j hij => by
      rw [← Module.End.mul_eq_comp, ← map_mul, lemma_4_13 (hb i) (hb j),
        if_neg fun e => hij (Subtype.ext e).symm, map_zero])
    (fun i => by rw [← Module.End.mul_eq_comp, ← map_mul, one_mul])
    (fun i => by rw [← Module.End.mul_eq_comp, ← map_mul, mul_one])
    (fun i => by
      rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp, ← map_mul, ← map_mul,
        ← mul_assoc, mul_assoc (sigma i.1), projector_mul_lam, map_mul]
      rfl)
    finrank_count
  apply NilHeckeBasis.action_injective n
  rw [H, map_sum, ← Finset.sum_coe_sort (BoxPartitionCount.Sq (n+2))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [idem, map_mul, Module.End.mul_eq_comp]

end Completeness

/-! ## Lemma 4.14 -/

section Lemma414

/-- The sign of (4.43): `|α||α̂| + X^{ν,1}_{(1^k)} ≡ C(ν,2) + C(k,2)`, cf. `sign_4_41`. -/
theorem signX_col {ν k : ℕ} (hν : 1 ≤ ν) (hk : k ≤ ν) :
    (signX ν 1 (col ν k) + k.choose 2) % 2 = ν.choose 2 % 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, ν = c + k := ⟨ν - k, by omega⟩
  have := sign_4_41 k c
  simp only [signX, bubbleSign, blockChi_col hν hk, hat_col, StaircaseEvaluation.omega,
    Finset.univ_unique, Finset.sum_singleton, sum_col hk] at this ⊢
  simp only [blockChi, Nat.add_sub_cancel, Fin.default_eq_zero, Fin.val_zero, zero_add,
    Nat.choose_eq_zero_of_lt (by norm_num : 1 < 2), add_zero] at this ⊢
  have F : (2 * (c+k).choose 2 + ((c+k).choose 2 + k) + (c+k).choose 2) * c =
      4 * ((c+k).choose 2 * c) + k * c := by ring
  omega

/-- An antitone `0/1` vector is the column of its weight. -/
theorem col_sum {ν : ℕ} {α : Fin ν → ℕ} (hα : Antitone α) (hα1 : ∀ i, α i ≤ 1) :
    col ν (∑ i, α i) = α := by
  have hsum : ∑ i, α i = (Finset.univ.filter fun j => α j = 1).card := by
    rw [Finset.card_filter]
    exact Finset.sum_congr rfl fun j _ => by have := hα1 j; split_ifs <;> omega
  funext i
  simp only [col]
  rcases (by have := hα1 i; omega : α i = 0 ∨ α i = 1) with h0 | h1
  · rw [if_neg, h0]
    rw [hsum, not_lt]
    calc (Finset.univ.filter fun j => α j = 1).card ≤ (Finset.Iio i).card := by
          refine Finset.card_le_card fun j hj => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio] at hj ⊢
          by_contra hji
          have := hα (not_lt.mp hji)
          omega
      _ = i.val := Fin.card_Iio i
  · rw [if_pos, h1]
    rw [hsum]
    calc i.val < i.val + 1 := Nat.lt_succ_self _
      _ = (Finset.Iic i).card := (Fin.card_Iic i).symm
      _ ≤ _ := by
          refine Finset.card_le_card fun j hj => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic] at hj ⊢
          have := hα hj
          have := hα1 j
          omega

/-- EKL Lemma 4.14 (4.43) in `ONH_{a+1}`, `a = n+1`:
`e_a ⊗ 1 = (-1)^{C(a,2)} ∑_{s=0}^{a} (ε_{a-s} ⊗ 1)(e_a ⊗ 1) X_{a,1} e_{a+1} (e_a ⊗ x^s)`,
with `ε_{a-s}` on the thick strand above the splitter and `s` dots on the thin strand below the
merger. -/
theorem lemma_4_14 :
    blockE n 0 (n+1) = (-1 : ℤ)^((n+1).choose 2) • ∑ s ∈ Finset.range (n+2),
      thickElem n (n+1) (n+1-s) * splitOne n (n+1) *
        (projector n * (blockE n 0 (n+1) * dotAt n (n+1) ^ s)) := by
  have hre : ∑ α ∈ BoxPartitionCount.box (n+1) 1, ThickBubble.idem n (n+1) 1 rfl α =
      ∑ k ∈ Finset.range (n+2), ThickBubble.idem n (n+1) 1 rfl (col (n+1) k) := by
    symm
    refine Finset.sum_nbij' (fun k => col (n+1) k) (fun α => ∑ i, α i) ?_ ?_ ?_ ?_ ?_
    · intro k _
      exact BoxPartitionCount.mem_box.mpr ⟨col_antitone _ _, col_le _ _⟩
    · intro α hα
      have h1 := (BoxPartitionCount.mem_box.mp hα).2
      rw [Finset.mem_range, Nat.lt_succ_iff]
      calc ∑ i, α i ≤ ∑ _i : Fin (n+1), 1 := Finset.sum_le_sum fun i _ => h1 i
        _ = n+1 := by simp
    · intro k hk
      exact sum_col (by have := Finset.mem_range.mp hk; omega)
    · intro α hα
      exact col_sum (BoxPartitionCount.mem_box.mp hα).1 (BoxPartitionCount.mem_box.mp hα).2
    · intro _ _; rfl
  conv_lhs => rw [ThickDecomposition.thm_4_16_right_one (n := n) (a := n+1) rfl, hre,
    ← Finset.sum_range_reflect]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n+1 := by have := Finset.mem_range.mp hk; omega
  rw [show n + 2 - 1 - k = n+1-k by omega, thickElem_eq (by omega) (by omega) (by omega),
    ThickBubble.idem, ThickBubble.sigma, ThickBubble.lam,
    hat_col, blockE_one, (blockSchur_one _ _).2, splitOne, dotAt, dif_pos (by omega),
    show n+1-(n+1-k) = k by omega]
  simp only [mul_one, one_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [← pow_add, neg_one_pow_congr (X := signX (n+1) 1 (col (n+1) (n+1-k)))
    (Y := (n+1).choose 2 + (n+1-k).choose 2)
    (by have := signX_col (ν := n+1) (k := n+1-k) (by omega) (by omega); omega)]
  congr 1
  simp only [mul_assoc]
  rw [← mul_assoc (blockE n 0 (n+1)) (blockE n 0 (n+1)), blockE_mul_blockE (by omega)]

end Lemma414

end

end OddMath.Frontier.ThickMatrixUnits
