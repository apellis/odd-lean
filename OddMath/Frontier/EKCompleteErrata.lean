import OddMath.Frontier.EKCompleteKostka
import OddMath.Frontier.EKCenterPower
import OddMath.Frontier.EKPrimitives

/-!
# [EK] Errata in the proofs of Prop 3.4 and Cor 3.12

Source: Ellis–Khovanov, arXiv:1107.5610v2.

* §3.2, p. 25: `p_n = m_n`; the printed expansions of `p₁, …, p₄` are proved
  (`p_one` … `p_four`), as input for the items below.
* Proof of Prop 3.4, pp. 25–26. The proof asserts that, paired against `p_k h_m` or `h_m p_k`,
  only `λ = (k+1, 1^{m−1})` and `λ = (k, 1^m)` give nonzero results, and that
  `(p_k h_m, e_{k+1}e_1^{m−1}) = 1`, `(h_m p_k, e_{k+1}e_1^{m−1}) = (−1)^{k(m−1)}`,
  `(p_k h_m, e_k e_1^m) = 1`, `(h_m p_k, e_k e_1^m) = (−1)^{km}`.
  - support claim false: `(p₃h₁, e₂₂) = (h₁p₃, e₂₂) = 2` (`prop_3_4_support_false`);
  - values false at `k = 4, m = 1`: `(p₄h₁, e₅) = (h₁p₄, e₅) = −1`, printed `1`, `1`
    (`prop_3_4_values_false_k4`);
  - values false at `k = 1, m = 1`: `(p₁h₁, e₁₁) = (h₁p₁, e₁₁) = 0`, printed `1`, `−1`
    (`prop_3_4_values_false_k1`).
  Prop 3.4 itself holds (`EKCenterPower.center_iff`).
* Proof of Cor 3.12, p. 30 ("Apply `ψ₁ψ₂` to (3.6) and (3.10)"): `ψ₁ψ₂` does not send `m_μ`
  to `±f_μ`: `ψ₁ψ₂(m₃) = −h₁₁₁ + h₂₁ − h₃`, `f₃ = h₁₁₁ + h₂₁ − h₃` (`cor_3_12_proof_gap`).
  The second equation of (3.14) holds (`EKFinalClosure.cor_3_12_second`).

Method: explicit `h`-expansions are identified with `p_k`, `f₃`, `ψ₁ψ₂(m₃)` by comparing
pairings with every `h_ν`, `ν ⊢ d`; all pairings of `h`/`e` words are evaluated by the
kernel-reducible evaluator `EKNondegeneracy.ev`, proved sound against `quotientPairing`.
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKComplete
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases
open EKNondegeneracy (hL eL evL partsF)
open EKElementaryQuotient (h e)

/-! ## Evaluation tools -/

theorem pairing_hL_eL (l l' : List ℕ) :
    quotientPairing (hL l) (eL l') = evL false true l l' := by
  rw [EKNondegeneracy.hL_eq, EKNondegeneracy.eL_eq, quotientPairing_pi,
    EKNondegeneracy.pairing_word_ev]; rfl

/-- An integer combination of `h`-words. -/
def comb (c : List (ℤ × List ℕ)) : Q := (c.map fun t => t.1 • hL t.2).sum

theorem pair_hL_comb (l : List ℕ) (c : List (ℤ × List ℕ)) :
    quotientPairing (hL l) (comb c) = (c.map fun t => t.1 * evL false false l t.2).sum := by
  induction c with
  | nil => simp [comb]
  | cons t c ih =>
    simp only [comb, List.map_cons, List.sum_cons, map_add, map_zsmul, smul_eq_mul] at ih ⊢
    rw [ih, EKNondegeneracy.pairing_hL]

theorem pairing_eL_hL (l l' : List ℕ) :
    quotientPairing (eL l) (hL l') = evL true false l l' := by
  rw [EKNondegeneracy.hL_eq, EKNondegeneracy.eL_eq, quotientPairing_pi,
    EKNondegeneracy.pairing_word_ev]; rfl

/-- Evaluated with the `e`-word on top (the cheaper recursion). -/
theorem pair_comb_eL (c : List (ℤ × List ℕ)) (l : List ℕ) :
    quotientPairing (comb c) (eL l) = (c.map fun t => t.1 * evL true false l t.2).sum := by
  induction c with
  | nil => simp [comb]
  | cons t c ih =>
    simp only [comb, List.map_cons, List.sum_cons, map_add, map_zsmul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul] at ih ⊢
    rw [ih, quotientPairing_symm, pairing_eL_hL]

theorem hL_append (l l' : List ℕ) : hL (l ++ l') = hL l * hL l' := by
  simp [hL, List.map_append, List.prod_append]

theorem comb_mul_h (c : List (ℤ × List ℕ)) (m : ℕ) :
    comb c * h m = comb (c.map fun t => (t.1, t.2 ++ [m])) := by
  induction c with
  | nil => simp [comb]
  | cons t c ih =>
    simp only [comb, List.map_cons, List.sum_cons, add_mul, smul_mul_assoc] at ih ⊢
    rw [ih, hL_append]
    simp [hL]

theorem h_mul_comb (c : List (ℤ × List ℕ)) (m : ℕ) :
    h m * comb c = comb (c.map fun t => (t.1, m :: t.2)) := by
  induction c with
  | nil => simp [comb]
  | cons t c ih =>
    simp only [comb, List.map_cons, List.sum_cons, mul_add, mul_smul_comm] at ih ⊢
    rw [ih]
    simp [hL]

theorem hL_mem (l : List ℕ) : hL l ∈ degreePiece l.sum := EKAutomorphisms.hWord_degree l

theorem comb_mem (d : ℕ) (c : List (ℤ × List ℕ)) (hc : ∀ t ∈ c, t.2.sum = d) :
    comb c ∈ degreePiece d := by
  induction c with
  | nil => simp [comb]
  | cons t c ih =>
    simp only [comb, List.map_cons, List.sum_cons]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (ih fun t' ht' => hc t' (by simp [ht']))
    rw [← hc t (by simp)]; exact hL_mem t.2

/-- Two degree-`d` elements with equal pairings against every `h_ν`, `ν ⊢ d`, are equal. -/
theorem eq_of_pair_hL {d : ℕ} {x y : Q} (hx : x ∈ degreePiece d) (hy : y ∈ degreePiece d)
    (hxy : ∀ l ∈ partsF d d d, quotientPairing (hL l) x = quotientPairing (hL l) y) : x = y := by
  rw [← sub_eq_zero]
  apply quotientPairing_nondegenerate_right
  have hlin : quotientPairing.flip (x - y) = 0 := by
    refine hBasis.ext fun μ => ?_
    rw [hBasis_apply, LinearMap.flip_apply, LinearMap.zero_apply, map_sub]
    by_cases hμ : μ.card = d
    · have := hxy _ (EKNondegeneracy.rowLens_mem_parts d μ hμ)
      rw [show EKPartitionSpanning.hPartition μ = hL μ.rowLens from rfl, this, sub_self]
    · rw [EKPrimitives.pairing_degree_orth hμ (EKPrimitives.hPartition_mem μ) hx,
        EKPrimitives.pairing_degree_orth hμ (EKPrimitives.hPartition_mem μ) hy, sub_self]
  intro z
  exact LinearMap.congr_fun hlin z

/-- `(h_ν, p_k) = δ_{ν,(k)}` on `h`-words of partitions. -/
theorem pair_hL_p {k : ℕ} (hk : 0 < k) (l : List ℕ) (hs : l.Sorted (· ≥ ·))
    (hp : ∀ x ∈ l, 0 < x) :
    quotientPairing (hL l) (EKCenterPower.p k) = if l = [k] then 1 else 0 := by
  classical
  have hr := YoungDiagram.rowLens_ofRowLens_eq_self (hw := hs) hp
  have hl : hL l = EKPartitionSpanning.hPartition (YoungDiagram.ofRowLens l hs) := by
    rw [EKPartitionSpanning.hPartition, hr]; rfl
  rw [hl, EKCenterPower.pair_hPartition_p]
  have := EKCenterPower.rows_iff k hk (YoungDiagram.ofRowLens l hs)
  rw [hr] at this
  by_cases h1 : l = [k]
  · rw [if_pos (this.mp h1), if_pos h1]
  · rw [if_neg (fun h2 => h1 (this.mpr h2)), if_neg h1]

theorem p_mem (k : ℕ) : EKCenterPower.p k ∈ degreePiece k :=
  (mBasis k (EKCenterPower.rowShape k)).property

/-- Identification of `p_k` with an explicit combination, from a kernel check. -/
theorem p_eq_comb {k : ℕ} (hk : 0 < k) (c : List (ℤ × List ℕ)) (hc : ∀ t ∈ c, t.2.sum = k)
    (hshape : ∀ l ∈ partsF k k k, l.Sorted (· ≥ ·) ∧ ∀ x ∈ l, 0 < x)
    (hval : ∀ l ∈ partsF k k k,
      (c.map fun t => t.1 * evL false false l t.2).sum = if l = [k] then 1 else 0) :
    EKCenterPower.p k = comb c := by
  refine eq_of_pair_hL (p_mem k) (comb_mem k c hc) fun l hl => ?_
  rw [pair_hL_comb, hval l hl, pair_hL_p hk l (hshape l hl).1 (hshape l hl).2]

/-! ## The printed expansions of `p₁, …, p₄` (p. 25) -/

def P1 : List (ℤ × List ℕ) := [(1, [1])]
def P2 : List (ℤ × List ℕ) := [(1, [1, 1])]
def P3 : List (ℤ × List ℕ) := [(1, [1, 1, 1]), (1, [2, 1]), (-1, [3])]
def P4 : List (ℤ × List ℕ) := [(-1, [1, 1, 1, 1]), (-2, [2, 2]), (4, [4])]

theorem p_one : EKCenterPower.p 1 = comb P1 :=
  p_eq_comb (by decide) P1 (by decide) (by decide) (by decide +kernel)
theorem p_two : EKCenterPower.p 2 = comb P2 :=
  p_eq_comb (by decide) P2 (by decide) (by decide) (by decide +kernel)
theorem p_three : EKCenterPower.p 3 = comb P3 :=
  p_eq_comb (by decide) P3 (by decide) (by decide) (by decide +kernel)
theorem p_four : EKCenterPower.p 4 = comb P4 :=
  p_eq_comb (by decide) P4 (by decide) (by decide) (by decide +kernel)

/-! ## N3: the proof of Prop 3.4 -/

/-- The support claim in the proof of Prop 3.4 fails: for `k = 3`, `m = 1`, `λ = (2,2)` is
neither `(4)` nor `(3,1)`, yet `(p₃h₁, e₂₂) = (h₁p₃, e₂₂) = 2`. -/
theorem prop_3_4_support_false :
    quotientPairing (EKCenterPower.p 3 * h 1) (eL [2, 2]) = 2 ∧
    quotientPairing (h 1 * EKCenterPower.p 3) (eL [2, 2]) = 2 := by
  rw [p_three, comb_mul_h, h_mul_comb, pair_comb_eL, pair_comb_eL]
  decide +kernel

/-- The printed values fail at `k = 4`, `m = 1`, `λ = (k+1) = (5)`: both pairings are `−1`,
while the proof states `1` and `(−1)^{k(m−1)} = 1`. The true common value is `(p₄, e₄) = −1`. -/
theorem prop_3_4_values_false_k4 :
    quotientPairing (EKCenterPower.p 4 * h 1) (eL [5]) = -1 ∧
    quotientPairing (h 1 * EKCenterPower.p 4) (eL [5]) = -1 ∧
    quotientPairing (EKCenterPower.p 4) (eL [4]) = -1 := by
  rw [p_four, comb_mul_h, h_mul_comb, pair_comb_eL, pair_comb_eL, pair_comb_eL]
  decide +kernel

/-- The printed values fail at `k = 1`, `m = 1`, `λ = (k, 1^m) = (1,1)`: both pairings are
`0`, while the proof states `1` and `(−1)^{km} = −1`. -/
theorem prop_3_4_values_false_k1 :
    quotientPairing (EKCenterPower.p 1 * h 1) (eL [1, 1]) = 0 ∧
    quotientPairing (h 1 * EKCenterPower.p 1) (eL [1, 1]) = 0 := by
  rw [p_one, comb_mul_h, h_mul_comb, pair_comb_eL, pair_comb_eL]
  decide +kernel

/-! ## N7: the proof of Cor 3.12 -/

open EKAutomorphisms (psi12)

theorem psi12_comb (c : List (ℤ × List ℕ)) :
    psi12 (comb c) = (c.map fun t => (t.1 * EKAutomorphisms.wordSign t.2) • eL t.2).sum := by
  induction c with
  | nil => simp [comb]
  | cons t c ih =>
    simp only [comb, List.map_cons, List.sum_cons, map_add, map_zsmul] at ih ⊢
    rw [ih, show hL t.2 = (t.2.map h).prod from rfl, EKAutomorphisms.psi12_hWord, smul_smul]
    rfl

theorem pair_hL_eLcomb (l : List ℕ) (c : List (ℤ × List ℕ)) :
    quotientPairing (hL l) ((c.map fun t => t.1 • eL t.2).sum) =
      (c.map fun t => t.1 * evL false true l t.2).sum := by
  induction c with
  | nil => simp
  | cons t c ih =>
    simp only [List.map_cons, List.sum_cons, map_add, map_zsmul, smul_eq_mul] at ih ⊢
    rw [ih, pairing_hL_eL]

/-- `ψ₁ψ₂(m₃) = −h₁₁₁ + h₂₁ − h₃`. -/
theorem psi12_m3 :
    psi12 (EKCenterPower.p 3) = comb [(-1, [1, 1, 1]), (1, [2, 1]), (-1, [3])] := by
  have hmem : psi12 (EKCenterPower.p 3) ∈ degreePiece 3 := by
    rw [EKAutomorphisms.psi12_apply]
    exact EKAutomorphisms.psi1_degree (EKAutomorphisms.psi2_degree (p_mem 3))
  refine eq_of_pair_hL hmem (comb_mem 3 _ (by decide)) fun l hl => ?_
  rw [p_three, psi12_comb, pair_hL_comb]
  have : (P3.map fun t => (t.1 * EKAutomorphisms.wordSign t.2) • eL t.2) =
      ([(-1, [1, 1, 1]), (1, [2, 1]), (-1, [3])] : List (ℤ × List ℕ)).map
        (fun t => t.1 • eL t.2) := by
    simp [P3, EKAutomorphisms.wordSign, EKAutomorphisms.s, Nat.choose_two_right]
  rw [this, pair_hL_eLcomb]
  revert l
  decide +kernel

theorem pair_eL_comb (l : List ℕ) (c : List (ℤ × List ℕ)) :
    quotientPairing (eL l) (comb c) = (c.map fun t => t.1 * evL true false l t.2).sum := by
  rw [quotientPairing_symm, pair_comb_eL]

/-- `f₃ = h₁₁₁ + h₂₁ − h₃` (EK §5.1). -/
theorem f3_eq :
    ((fBasis 3 (EKCenterPower.rowShape 3) : degreePiece 3) : Q) =
      comb [(1, [1, 1, 1]), (1, [2, 1]), (-1, [3])] := by
  classical
  have hmem := comb_mem 3 [(1, [1, 1, 1]), (1, [2, 1]), (-1, [3])] (by decide)
  have hval : ∀ l ∈ partsF 3 3 3,
      (([(1, [1, 1, 1]), (1, [2, 1]), (-1, [3])] : List (ℤ × List ℕ)).map
        fun t => t.1 * evL true false l t.2).sum = if l = [3] then 1 else 0 := by
    decide +kernel
  have key := f_unique 3 (EKCenterPower.rowShape 3) ⟨_, hmem⟩ fun ν => by
    have hν := EKNondegeneracy.rowLens_mem_parts 3 ν.val ν.property
    have hiff : ν = EKCenterPower.rowShape 3 ↔ ν.val.rowLens = [3] := by
      rw [EKCenterPower.rows_iff 3 (by decide)]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    change quotientPairing (eL ν.val.rowLens) (comb _) = _
    rw [pair_eL_comb, hval _ hν]
    by_cases h1 : ν.val.rowLens = [3]
    · rw [if_pos h1, if_pos (hiff.mpr h1)]
    · rw [if_neg h1, if_neg (fun h2 => h1 (hiff.mp h2))]
  rw [← key]

/-- **N7.** `ψ₁ψ₂(m₃) ≠ ±f₃`, so applying `ψ₁ψ₂` to (3.10) does not give the second
equation of (3.14) as the proof of Cor 3.12 asserts. -/
theorem cor_3_12_proof_gap :
    psi12 (EKCenterPower.p 3) = comb [(-1, [1, 1, 1]), (1, [2, 1]), (-1, [3])] ∧
    ((fBasis 3 (EKCenterPower.rowShape 3) : degreePiece 3) : Q) =
      comb [(1, [1, 1, 1]), (1, [2, 1]), (-1, [3])] ∧
    psi12 (EKCenterPower.p 3) ≠ ((fBasis 3 (EKCenterPower.rowShape 3) : degreePiece 3) : Q) ∧
    psi12 (EKCenterPower.p 3) ≠ -((fBasis 3 (EKCenterPower.rowShape 3) : degreePiece 3) : Q) := by
  refine ⟨psi12_m3, f3_eq, ?_, ?_⟩
  · rw [psi12_m3, f3_eq]
    intro heq
    have := congrArg (quotientPairing (hL [3])) heq
    rw [pair_hL_comb, pair_hL_comb] at this
    revert this
    decide +kernel
  · rw [psi12_m3, f3_eq]
    intro heq
    have := congrArg (quotientPairing (hL [2, 1])) heq
    rw [pair_hL_comb, map_neg, pair_hL_comb] at this
    revert this
    decide +kernel

/-- The statement the gap concerns holds: (3.14), second equation, every degree. -/
theorem cor_3_12_second_holds (d : ℕ) : EKOddRSKII.Second312 d := EKFinalClosure.cor_3_12_second d

end OddMath.Frontier.EKComplete
