import OddMath.Frontier.EKGeneralQ
import OddMath.Frontier.EKAppendixData

/-!
# EK §5.2, unspecialised-q table, at arbitrary q over an arbitrary commutative ring

Source: Ellis–Khovanov, arXiv:1107.5610v2, §5.2, p.38, the table "The bilinear form for
unspecialized q is" (degrees 1–4, compositions in printed order, `[n] = 1 + q + ⋯ + q^{n-1}`,
`[n]! = [n][n-1]⋯[1]`, `∗` = the symmetric entry).

Every printed entry is proved for `EKGeneralQ.form q`, the form (2.1), with `k` an arbitrary
commutative ring and `q : k` arbitrary; the entries below the diagonal follow from
`EKGeneralQ.form_symm`.  This supersedes the `q = -1` evaluations `EKAppendixData.qgen*`.

Method: the margin-matrix sum defining `matForm` is transported to the
explicit enumeration `EKAppendixData.matSet` (`matSet_sum`), and the sum of `q ^ crossings` is
regrouped by crossing number (`sum_pow_eq_counts`).  The crossing-number distribution of each
entry is a natural-number list checked by kernel reduction (`decide +kernel`); the resulting
polynomial identity in `q` is closed by `ring`.
-/
set_option maxRecDepth 100000

noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKGeneralQ
open EKPairingMatrices

variable {k : Type*} [CommRing k] (q : k)

/-- EK p.38: the unbalanced q-number `[n] = 1 + q + ⋯ + q^{n-1}`. -/
def qnum (n : ℕ) : k := ∑ i ∈ Finset.range n, q ^ i

/-- EK p.38: the q-factorial `[n]! = [n][n-1]⋯[2][1]`. -/
def qfact (n : ℕ) : k := ∏ i ∈ Finset.range n, qnum q (i + 1)

/-- Margin-matrix sums as sums over the explicit enumeration `matSet`, for any values. -/
theorem matSet_sum {M : Type*} [AddCommMonoid M] {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ)
    (F : List (List ℕ) → M) :
    ∑ A : Mat β α, F (EKAppendixData.toL A.val) =
      ∑ L ∈ EKAppendixData.matSet (List.ofFn β) (List.ofFn α), F L := by
  classical
  open EKAppendixData in
  apply Finset.sum_bij (fun A _ => toL A.val)
  · intro A _
    simp only [matSet, List.mem_toFinset, List.mem_filter, decide_eq_true_iff, List.length_ofFn]
    refine ⟨(mem_matCands c _ _).mpr (forall₂_ofFn _ _
      (fun i => (mem_comps c _ _).mpr ⟨by simp, ?_⟩)), ?_⟩
    · rw [List.sum_ofFn]; exact congrFun A.property.1 i
    · apply List.ext_getElem
      · simp [colSumsL]
      · intro j h1 h2
        simp only [colSumsL, List.getElem_map, List.getElem_range, List.getElem_ofFn]
        rw [list_sum_range, show (toL A.val).length = r by simp [toL],
          ← Fin.sum_univ_eq_sum_range (fun i => ent (toL A.val) i j) r]
        have hj : j < c := by simpa [colSumsL] using h1
        simp only [ent_toL A.val _ ⟨j, hj⟩]
        exact congrFun A.property.2 ⟨j, hj⟩
  · intro A _ B _ h
    exact Subtype.ext (EKAppendixData.toL_injective h)
  · intro L hL
    open EKAppendixData in
    simp only [matSet, List.mem_toFinset, List.mem_filter, decide_eq_true_iff, List.length_ofFn,
      mem_matCands] at hL
    obtain ⟨hF, hcol⟩ := hL
    have hlen : L.length = r := by simpa using hF.length_eq
    have hrow : ∀ (i : ℕ) (hi : i < L.length), L[i].length = c ∧ L[i].sum = β ⟨i, by omega⟩ := by
      intro i hi
      have := (List.forall₂_iff_get.mp hF).2 i hi (by simp; omega)
      simpa using (EKAppendixData.mem_comps c _ _).mp this
    let A : Raw r c := fun i j => EKAppendixData.ent L i j
    have hA : EKAppendixData.toL A = L := by
      apply List.ext_getElem
      · simp [EKAppendixData.toL, hlen]
      · intro i h1 h2
        simp only [EKAppendixData.toL, List.getElem_ofFn]
        apply List.ext_getElem
        · simp [(hrow i h2).1]
        · intro j h3 h4
          simp [A, EKAppendixData.ent, List.getD_eq_getElem?_getD, h2, h4]
    refine ⟨⟨A, ?_, ?_⟩, Finset.mem_univ _, hA⟩
    · funext i
      have hi : i.val < L.length := by omega
      rw [← (hrow i hi).2]
      show ∑ j, A i j = _
      rw [← List.sum_ofFn]
      congr 1
      apply List.ext_getElem
      · simp [(hrow i hi).1]
      · intro j h1 h2
        simp [A, EKAppendixData.ent, List.getD_eq_getElem?_getD, hi, h2]
    · funext j
      have h := congrArg (fun l => l[j.val]?) hcol
      simp only [EKAppendixData.colSumsL, List.getElem?_map, List.getElem?_range j.isLt,
        List.getElem?_ofFn, Option.map_some'] at h
      have h' : ((List.range L.length).map (fun i => EKAppendixData.ent L i j)).sum = α j := by
        simpa using h
      rw [EKAppendixData.list_sum_range, hlen,
        ← Fin.sum_univ_eq_sum_range (fun i => EKAppendixData.ent L i j) r] at h'
      exact h'
  · intro A _; rfl

/-- `matForm` (hence (2.1)) evaluated on the explicit enumeration. -/
theorem matForm_eq_matSet {r c : ℕ} (β : Fin r → ℕ) (α : Fin c → ℕ) :
    matForm q β α = ∑ L ∈ EKAppendixData.matSet (List.ofFn β) (List.ofFn α),
      q ^ EKAppendixData.crossL L r c := by
  have h := matSet_sum β α (fun L => q ^ EKAppendixData.crossL L r c)
  simp only [← EKAppendixData.crossing_toL] at h
  exact h

/-- Regrouping a sum of powers of `q` by exponent. -/
theorem sum_pow_eq_counts {ι : Type*} [DecidableEq ι] (S : Finset ι) (g : ι → ℕ) (N : ℕ)
    (hN : ∀ x ∈ S, g x < N) :
    ∑ x ∈ S, q ^ g x = ∑ n ∈ Finset.range N, ((S.filter (fun x => g x = n)).card : k) * q ^ n := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := g) (t := Finset.range N)
    (fun x hx => Finset.mem_range.mpr (hN x hx))]
  apply Finset.sum_congr rfl
  intro n _
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2]),
    Finset.sum_const, nsmul_eq_mul]

/-- Number of margin matrices (rows `bl`, columns `al`) with exactly `n` crossings. -/
def crossCount (bl al : List ℕ) (n : ℕ) : ℕ :=
  ((EKAppendixData.matSet bl al).filter
    (fun L => EKAppendixData.crossL L bl.length al.length = n)).card

/-- Certified evaluator: if `cs` is the crossing-number distribution of the pair
`(bl, al)`, then `(h_bl, h_al) = Σ_n cs[n] q^n` (EK (2.1)). -/
theorem form_eval (bl al cs : List ℕ)
    (hc : (∀ L ∈ EKAppendixData.matSet bl al,
        EKAppendixData.crossL L bl.length al.length < cs.length) ∧
      (List.range cs.length).map (crossCount bl al) = cs) :
    form q (hWord k bl) (hWord k al) =
      ∑ n ∈ Finset.range cs.length, (cs.getD n 0 : k) * q ^ n := by
  rw [form_hWords, sourceFormAll_eq_matForm, matForm_eq_matSet, List.ofFn_get, List.ofFn_get]
  rw [sum_pow_eq_counts q _ _ cs.length hc.1]
  apply Finset.sum_congr rfl
  intro n hn
  congr 2
  have h := congrArg (fun l => l.getD n 0) hc.2
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (Finset.mem_range.mp hn), Option.map_some', Option.getD_some] at h
  exact h
/-- EK §5.2 p.38, degree 1: `(h_1, h_1) = 1`. -/
theorem table1_1_1 : form q (hWord k [1]) (hWord k [1]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 2: `(h_11, h_11) = [2]`. -/
theorem table2_11_11 : form q (hWord k [1, 1]) (hWord k [1, 1]) = qnum q 2 := by
  rw [form_eval q _ _ [1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 2: `(h_11, h_2) = 1`. -/
theorem table2_11_2 : form q (hWord k [1, 1]) (hWord k [2]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 2: `(h_2, h_2) = 1`. -/
theorem table2_2_2 : form q (hWord k [2]) (hWord k [2]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 3: `(h_111, h_111) = [3]!`. -/
theorem table3_111_111 : form q (hWord k [1, 1, 1]) (hWord k [1, 1, 1]) = qfact q 3 := by
  rw [form_eval q _ _ [1, 2, 2, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 3: `(h_111, h_12) = [3]`. -/
theorem table3_111_12 : form q (hWord k [1, 1, 1]) (hWord k [1, 2]) = qnum q 3 := by
  rw [form_eval q _ _ [1, 1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 3: `(h_111, h_21) = [3]`. -/
theorem table3_111_21 : form q (hWord k [1, 1, 1]) (hWord k [2, 1]) = qnum q 3 := by
  rw [form_eval q _ _ [1, 1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 3: `(h_111, h_3) = 1`. -/
theorem table3_111_3 : form q (hWord k [1, 1, 1]) (hWord k [3]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 3: `(h_12, h_12) = [2]`. -/
theorem table3_12_12 : form q (hWord k [1, 2]) (hWord k [1, 2]) = qnum q 2 := by
  rw [form_eval q _ _ [1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 3: `(h_12, h_21) = 1 + q^2`. -/
theorem table3_12_21 : form q (hWord k [1, 2]) (hWord k [2, 1]) = 1 + q^2 := by
  rw [form_eval q _ _ [1, 0, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 3: `(h_12, h_3) = 1`. -/
theorem table3_12_3 : form q (hWord k [1, 2]) (hWord k [3]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 3: `(h_21, h_21) = [2]`. -/
theorem table3_21_21 : form q (hWord k [2, 1]) (hWord k [2, 1]) = qnum q 2 := by
  rw [form_eval q _ _ [1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 3: `(h_21, h_3) = 1`. -/
theorem table3_21_3 : form q (hWord k [2, 1]) (hWord k [3]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 3: `(h_3, h_3) = 1`. -/
theorem table3_3_3 : form q (hWord k [3]) (hWord k [3]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_1111, h_1111) = [4]!`. -/
theorem table4_1111_1111 : form q (hWord k [1, 1, 1, 1]) (hWord k [1, 1, 1, 1]) = qfact q 4 := by
  rw [form_eval q _ _ [1, 3, 5, 6, 5, 3, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 4: `(h_1111, h_112) = [4] * [3]`. -/
theorem table4_1111_112 : form q (hWord k [1, 1, 1, 1]) (hWord k [1, 1, 2]) = qnum q 4 * qnum q 3 := by
  rw [form_eval q _ _ [1, 2, 3, 3, 2, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 4: `(h_1111, h_121) = [4] * [3]`. -/
theorem table4_1111_121 : form q (hWord k [1, 1, 1, 1]) (hWord k [1, 2, 1]) = qnum q 4 * qnum q 3 := by
  rw [form_eval q _ _ [1, 2, 3, 3, 2, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 4: `(h_1111, h_211) = [4] * [3]`. -/
theorem table4_1111_211 : form q (hWord k [1, 1, 1, 1]) (hWord k [2, 1, 1]) = qnum q 4 * qnum q 3 := by
  rw [form_eval q _ _ [1, 2, 3, 3, 2, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 4: `(h_1111, h_22) = [5] + q^2`. -/
theorem table4_1111_22 : form q (hWord k [1, 1, 1, 1]) (hWord k [2, 2]) = qnum q 5 + q^2 := by
  rw [form_eval q _ _ [1, 1, 2, 1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 4: `(h_1111, h_13) = [4]`. -/
theorem table4_1111_13 : form q (hWord k [1, 1, 1, 1]) (hWord k [1, 3]) = qnum q 4 := by
  rw [form_eval q _ _ [1, 1, 1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_1111, h_31) = [4]`. -/
theorem table4_1111_31 : form q (hWord k [1, 1, 1, 1]) (hWord k [3, 1]) = qnum q 4 := by
  rw [form_eval q _ _ [1, 1, 1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_1111, h_4) = 1`. -/
theorem table4_1111_4 : form q (hWord k [1, 1, 1, 1]) (hWord k [4]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_112, h_112) = [5] + q * [2]`. -/
theorem table4_112_112 : form q (hWord k [1, 1, 2]) (hWord k [1, 1, 2]) = qnum q 5 + q * qnum q 2 := by
  rw [form_eval q _ _ [1, 2, 2, 1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 4: `(h_112, h_121) = [5] + q^2 * [2]`. -/
theorem table4_112_121 : form q (hWord k [1, 1, 2]) (hWord k [1, 2, 1]) = qnum q 5 + q^2 * qnum q 2 := by
  rw [form_eval q _ _ [1, 1, 2, 2, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 4: `(h_112, h_211) = [6] + q^2`. -/
theorem table4_112_211 : form q (hWord k [1, 1, 2]) (hWord k [2, 1, 1]) = qnum q 6 + q^2 := by
  rw [form_eval q _ _ [1, 1, 2, 1, 1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 4: `(h_112, h_22) = [3] + q^4`. -/
theorem table4_112_22 : form q (hWord k [1, 1, 2]) (hWord k [2, 2]) = qnum q 3 + q^4 := by
  rw [form_eval q _ _ [1, 1, 1, 0, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_112, h_13) = [3]`. -/
theorem table4_112_13 : form q (hWord k [1, 1, 2]) (hWord k [1, 3]) = qnum q 3 := by
  rw [form_eval q _ _ [1, 1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_112, h_31) = [1] + q^2 * [2]`. -/
theorem table4_112_31 : form q (hWord k [1, 1, 2]) (hWord k [3, 1]) = qnum q 1 + q^2 * qnum q 2 := by
  rw [form_eval q _ _ [1, 0, 1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 4: `(h_112, h_4) = 1`. -/
theorem table4_112_4 : form q (hWord k [1, 1, 2]) (hWord k [4]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_121, h_121) = [4] + q + q^3 + q^5`. -/
theorem table4_121_121 : form q (hWord k [1, 2, 1]) (hWord k [1, 2, 1]) = qnum q 4 + q + q^3 + q^5 := by
  rw [form_eval q _ _ [1, 2, 1, 2, 0, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 4: `(h_121, h_211) = [5] + q^2 * [2]`. -/
theorem table4_121_211 : form q (hWord k [1, 2, 1]) (hWord k [2, 1, 1]) = qnum q 5 + q^2 * qnum q 2 := by
  rw [form_eval q _ _ [1, 1, 2, 2, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 4: `(h_121, h_22) = 1 + 2*q^2 + q^3`. -/
theorem table4_121_22 : form q (hWord k [1, 2, 1]) (hWord k [2, 2]) = 1 + 2*q^2 + q^3 := by
  rw [form_eval q _ _ [1, 0, 2, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_121, h_13) = [2] + q^3`. -/
theorem table4_121_13 : form q (hWord k [1, 2, 1]) (hWord k [1, 3]) = qnum q 2 + q^3 := by
  rw [form_eval q _ _ [1, 1, 0, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_121, h_31) = [2] + q^3`. -/
theorem table4_121_31 : form q (hWord k [1, 2, 1]) (hWord k [3, 1]) = qnum q 2 + q^3 := by
  rw [form_eval q _ _ [1, 1, 0, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_121, h_4) = 1`. -/
theorem table4_121_4 : form q (hWord k [1, 2, 1]) (hWord k [4]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_211, h_211) = [5] + q * [2]`. -/
theorem table4_211_211 : form q (hWord k [2, 1, 1]) (hWord k [2, 1, 1]) = qnum q 5 + q * qnum q 2 := by
  rw [form_eval q _ _ [1, 2, 2, 1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 4: `(h_211, h_22) = [3] + q^4`. -/
theorem table4_211_22 : form q (hWord k [2, 1, 1]) (hWord k [2, 2]) = qnum q 3 + q^4 := by
  rw [form_eval q _ _ [1, 1, 1, 0, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_211, h_13) = 1 + q^2 * [2]`. -/
theorem table4_211_13 : form q (hWord k [2, 1, 1]) (hWord k [1, 3]) = 1 + q^2 * qnum q 2 := by
  rw [form_eval q _ _ [1, 0, 1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]
  ring

/-- EK §5.2 p.38, degree 4: `(h_211, h_31) = [3]`. -/
theorem table4_211_31 : form q (hWord k [2, 1, 1]) (hWord k [3, 1]) = qnum q 3 := by
  rw [form_eval q _ _ [1, 1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_211, h_4) = 1`. -/
theorem table4_211_4 : form q (hWord k [2, 1, 1]) (hWord k [4]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_22, h_22) = [2] + q^4`. -/
theorem table4_22_22 : form q (hWord k [2, 2]) (hWord k [2, 2]) = qnum q 2 + q^4 := by
  rw [form_eval q _ _ [1, 1, 0, 0, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_22, h_13) = 1 + q^2`. -/
theorem table4_22_13 : form q (hWord k [2, 2]) (hWord k [1, 3]) = 1 + q^2 := by
  rw [form_eval q _ _ [1, 0, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_22, h_31) = 1 + q^2`. -/
theorem table4_22_31 : form q (hWord k [2, 2]) (hWord k [3, 1]) = 1 + q^2 := by
  rw [form_eval q _ _ [1, 0, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_22, h_4) = 1`. -/
theorem table4_22_4 : form q (hWord k [2, 2]) (hWord k [4]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_13, h_13) = [2]`. -/
theorem table4_13_13 : form q (hWord k [1, 3]) (hWord k [1, 3]) = qnum q 2 := by
  rw [form_eval q _ _ [1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_13, h_31) = 1 + q^3`. -/
theorem table4_13_31 : form q (hWord k [1, 3]) (hWord k [3, 1]) = 1 + q^3 := by
  rw [form_eval q _ _ [1, 0, 0, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_13, h_4) = 1`. -/
theorem table4_13_4 : form q (hWord k [1, 3]) (hWord k [4]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_31, h_31) = [2]`. -/
theorem table4_31_31 : form q (hWord k [3, 1]) (hWord k [3, 1]) = qnum q 2 := by
  rw [form_eval q _ _ [1, 1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_31, h_4) = 1`. -/
theorem table4_31_4 : form q (hWord k [3, 1]) (hWord k [4]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]

/-- EK §5.2 p.38, degree 4: `(h_4, h_4) = 1`. -/
theorem table4_4_4 : form q (hWord k [4]) (hWord k [4]) = 1 := by
  rw [form_eval q _ _ [1] (by decide +kernel)]
  simp [qnum, qfact, Finset.sum_range_succ, Finset.prod_range_succ]


/-! ## The printed tables as matrices, all entries (the `∗` entries by symmetry) -/

/-- Printed degree-1 compositions, printed order. -/
def comps1 : Fin 1 → List ℕ := ![[1]]

/-- EK §5.2 p.38: the printed degree-1 table at unspecialised `q`, `∗` filled in. -/
def printed1 (_q : k) : Matrix (Fin 1) (Fin 1) k := !![1]

/-- EK §5.2 p.38, degree 1: every printed entry, at arbitrary `q` over any commutative ring. -/
theorem table1 (i j : Fin 1) :
    form q (hWord k (comps1 i)) (hWord k (comps1 j)) = printed1 q i j := by
  fin_cases i; fin_cases j
  exacts [table1_1_1 q]

/-- Printed degree-2 compositions, printed order. -/
def comps2 : Fin 2 → List ℕ := ![[1, 1], [2]]

/-- EK §5.2 p.38: the printed degree-2 table at unspecialised `q`, `∗` filled in. -/
def printed2 (q : k) : Matrix (Fin 2) (Fin 2) k := !![qnum q 2, 1;
    1, 1]

/-- EK §5.2 p.38, degree 2: every printed entry, at arbitrary `q` over any commutative ring. -/
theorem table2 (i j : Fin 2) :
    form q (hWord k (comps2 i)) (hWord k (comps2 j)) = printed2 q i j := by
  fin_cases i <;> fin_cases j
  exacts [table2_11_11 q, table2_11_2 q, (form_symm q _ _).trans (table2_11_2 q), table2_2_2 q]

/-- Printed degree-3 compositions, printed order. -/
def comps3 : Fin 4 → List ℕ := ![[1, 1, 1], [1, 2], [2, 1], [3]]

/-- EK §5.2 p.38: the printed degree-3 table at unspecialised `q`, `∗` filled in. -/
def printed3 (q : k) : Matrix (Fin 4) (Fin 4) k := !![qfact q 3, qnum q 3, qnum q 3, 1;
    qnum q 3, qnum q 2, 1 + q^2, 1;
    qnum q 3, 1 + q^2, qnum q 2, 1;
    1, 1, 1, 1]

/-- EK §5.2 p.38, degree 3: every printed entry, at arbitrary `q` over any commutative ring. -/
theorem table3 (i j : Fin 4) :
    form q (hWord k (comps3 i)) (hWord k (comps3 j)) = printed3 q i j := by
  fin_cases i <;> fin_cases j
  exacts [table3_111_111 q, table3_111_12 q, table3_111_21 q, table3_111_3 q, (form_symm q _ _).trans (table3_111_12 q), table3_12_12 q, table3_12_21 q, table3_12_3 q, (form_symm q _ _).trans (table3_111_21 q), (form_symm q _ _).trans (table3_12_21 q), table3_21_21 q, table3_21_3 q, (form_symm q _ _).trans (table3_111_3 q), (form_symm q _ _).trans (table3_12_3 q), (form_symm q _ _).trans (table3_21_3 q), table3_3_3 q]

/-- Printed degree-4 compositions, printed order. -/
def comps4 : Fin 8 → List ℕ := ![[1, 1, 1, 1], [1, 1, 2], [1, 2, 1], [2, 1, 1], [2, 2], [1, 3], [3, 1], [4]]

/-- EK §5.2 p.38: the printed degree-4 table at unspecialised `q`, `∗` filled in. -/
def printed4 (q : k) : Matrix (Fin 8) (Fin 8) k := !![qfact q 4, qnum q 4 * qnum q 3, qnum q 4 * qnum q 3, qnum q 4 * qnum q 3, qnum q 5 + q^2, qnum q 4, qnum q 4, 1;
    qnum q 4 * qnum q 3, qnum q 5 + q * qnum q 2, qnum q 5 + q^2 * qnum q 2, qnum q 6 + q^2, qnum q 3 + q^4, qnum q 3, qnum q 1 + q^2 * qnum q 2, 1;
    qnum q 4 * qnum q 3, qnum q 5 + q^2 * qnum q 2, qnum q 4 + q + q^3 + q^5, qnum q 5 + q^2 * qnum q 2, 1 + 2*q^2 + q^3, qnum q 2 + q^3, qnum q 2 + q^3, 1;
    qnum q 4 * qnum q 3, qnum q 6 + q^2, qnum q 5 + q^2 * qnum q 2, qnum q 5 + q * qnum q 2, qnum q 3 + q^4, 1 + q^2 * qnum q 2, qnum q 3, 1;
    qnum q 5 + q^2, qnum q 3 + q^4, 1 + 2*q^2 + q^3, qnum q 3 + q^4, qnum q 2 + q^4, 1 + q^2, 1 + q^2, 1;
    qnum q 4, qnum q 3, qnum q 2 + q^3, 1 + q^2 * qnum q 2, 1 + q^2, qnum q 2, 1 + q^3, 1;
    qnum q 4, qnum q 1 + q^2 * qnum q 2, qnum q 2 + q^3, qnum q 3, 1 + q^2, 1 + q^3, qnum q 2, 1;
    1, 1, 1, 1, 1, 1, 1, 1]

/-- EK §5.2 p.38, degree 4: every printed entry, at arbitrary `q` over any commutative ring. -/
theorem table4 (i j : Fin 8) :
    form q (hWord k (comps4 i)) (hWord k (comps4 j)) = printed4 q i j := by
  fin_cases i <;> fin_cases j
  exacts [table4_1111_1111 q, table4_1111_112 q, table4_1111_121 q, table4_1111_211 q, table4_1111_22 q, table4_1111_13 q, table4_1111_31 q, table4_1111_4 q, (form_symm q _ _).trans (table4_1111_112 q), table4_112_112 q, table4_112_121 q, table4_112_211 q, table4_112_22 q, table4_112_13 q, table4_112_31 q, table4_112_4 q, (form_symm q _ _).trans (table4_1111_121 q), (form_symm q _ _).trans (table4_112_121 q), table4_121_121 q, table4_121_211 q, table4_121_22 q, table4_121_13 q, table4_121_31 q, table4_121_4 q, (form_symm q _ _).trans (table4_1111_211 q), (form_symm q _ _).trans (table4_112_211 q), (form_symm q _ _).trans (table4_121_211 q), table4_211_211 q, table4_211_22 q, table4_211_13 q, table4_211_31 q, table4_211_4 q, (form_symm q _ _).trans (table4_1111_22 q), (form_symm q _ _).trans (table4_112_22 q), (form_symm q _ _).trans (table4_121_22 q), (form_symm q _ _).trans (table4_211_22 q), table4_22_22 q, table4_22_13 q, table4_22_31 q, table4_22_4 q, (form_symm q _ _).trans (table4_1111_13 q), (form_symm q _ _).trans (table4_112_13 q), (form_symm q _ _).trans (table4_121_13 q), (form_symm q _ _).trans (table4_211_13 q), (form_symm q _ _).trans (table4_22_13 q), table4_13_13 q, table4_13_31 q, table4_13_4 q, (form_symm q _ _).trans (table4_1111_31 q), (form_symm q _ _).trans (table4_112_31 q), (form_symm q _ _).trans (table4_121_31 q), (form_symm q _ _).trans (table4_211_31 q), (form_symm q _ _).trans (table4_22_31 q), (form_symm q _ _).trans (table4_13_31 q), table4_31_31 q, table4_31_4 q, (form_symm q _ _).trans (table4_1111_4 q), (form_symm q _ _).trans (table4_112_4 q), (form_symm q _ _).trans (table4_121_4 q), (form_symm q _ _).trans (table4_211_4 q), (form_symm q _ _).trans (table4_22_4 q), (form_symm q _ _).trans (table4_13_4 q), (form_symm q _ _).trans (table4_31_4 q), table4_4_4 q]

/-! ## Gram determinants in degrees ≤ 3 and the §5.2 remarks N1, N2 -/

/-- The degree-`n` Gram matrix of (2.1) on the printed composition words. -/
def gramPrinted {m : ℕ} (c : Fin m → List ℕ) : Matrix (Fin m) (Fin m) k :=
  Matrix.of fun i j => form q (hWord k (c i)) (hWord k (c j))

theorem det_gram2 : (gramPrinted q comps2).det = q := by
  have h : gramPrinted q comps2 = printed2 q := Matrix.ext (table2 q)
  rw [h, Matrix.det_fin_two]
  simp [printed2, qnum, Finset.sum_range_succ]

/-- EK §5.2: the degree-3 Gram determinant is `-q⁵(q-1)(q+1)`, at arbitrary `q` over any
commutative ring. -/
theorem det_gram3 : (gramPrinted q comps3).det = -(q ^ 5 * (q - 1) * (q + 1)) := by
  have h : gramPrinted q comps3 = printed3 q := Matrix.ext (table3 q)
  rw [h, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, printed3, qnum, qfact, Finset.sum_range_succ,
    Finset.prod_range_succ, Matrix.submatrix, Fin.succAbove]
  ring

open Polynomial in
/-- EK §5.2 p.40, "It is immediate from the definition of the bilinear form that this
determinant is monic in q": FALSE in degree 3.  Over `ℤ[q]` the degree-3 Gram determinant is
`-q⁵(q-1)(q+1)`, of the printed degree `D = 2^{n-2}(n²-3n+4) - 1 = 7` (5.2), with leading
coefficient `-1`. -/
theorem det_gram3_not_monic :
    (gramPrinted (X : ℤ[X]) comps3).det = -(X ^ 5 * (X - 1) * (X + 1)) ∧
    (gramPrinted (X : ℤ[X]) comps3).det.natDegree = 7 ∧
    (gramPrinted (X : ℤ[X]) comps3).det.leadingCoeff = -1 ∧
    ¬ (gramPrinted (X : ℤ[X]) comps3).det.Monic := by
  have hd := det_gram3 (X : ℤ[X])
  have hlc : (-(X ^ 5 * (X - 1) * (X + 1)) : ℤ[X]).leadingCoeff = -1 := by
    have h1 : (X - 1 : ℤ[X]).leadingCoeff = 1 := by
      simpa using (monic_X_sub_C (1 : ℤ)).leadingCoeff
    have h2 : (X + 1 : ℤ[X]).leadingCoeff = 1 := by
      simpa using (monic_X_add_C (1 : ℤ)).leadingCoeff
    rw [leadingCoeff_neg, leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_X_pow, h1, h2]
    norm_num
  have hdeg : (-(X ^ 5 * (X - 1) * (X + 1)) : ℤ[X]).natDegree = 7 := by
    have h1 : (X - 1 : ℤ[X]).natDegree = 1 := by simpa using natDegree_X_sub_C (1 : ℤ)
    have h0 : (X - 1 : ℤ[X]) ≠ 0 := by simpa using X_sub_C_ne_zero (1 : ℤ)
    have h2 : (X + 1 : ℤ[X]).natDegree = 1 := by simpa using natDegree_X_add_C (1 : ℤ)
    have h3 : (X + 1 : ℤ[X]) ≠ 0 := by simpa using X_add_C_ne_zero (1 : ℤ)
    rw [natDegree_neg, natDegree_mul, natDegree_mul, natDegree_X_pow, h1, h2]
    · exact pow_ne_zero _ X_ne_zero
    · exact h0
    · exact mul_ne_zero (pow_ne_zero _ X_ne_zero) h0
    · exact h3
  refine ⟨hd, hd ▸ hdeg, hd ▸ hlc, ?_⟩
  intro hm
  have h1 := hm.leadingCoeff
  rw [hd, hlc] at h1
  norm_num at h1

open Polynomial in
/-- EK §5.2 p.39, "Note that all are monic and with constant coefficient 1, so their roots are
units in the ring of algebraic integers": FALSE for the listed degree-2 and degree-3 factors.
The degree-2 Gram determinant is `q`, whose root `0` is not a unit, and the listed factor
`q - 1` of the degree-3 determinant has constant coefficient `-1`.  What holds in degrees
`≤ 3`: every listed factor (`q`, `q - 1`, `q + 1`) is monic, and the multiplicities printed
there, `(2,1)`, `(3,5)` for `q` and `(3,1)` for `q ∓ 1`, are those of `det₂ = q`,
`det₃ = -q⁵(q-1)(q+1)`. -/
theorem minimal_polynomials_counterexample :
    (gramPrinted (X : ℤ[X]) comps2).det = X ∧ (X : ℤ[X]).coeff 0 = 0 ∧
    ¬ IsUnit (0 : ℤ) ∧ (X : ℤ[X]).IsRoot 0 ∧
    (X - 1 : ℤ[X]) ∣ (gramPrinted (X : ℤ[X]) comps3).det ∧ (X - 1 : ℤ[X]).coeff 0 = -1 ∧
    (X : ℤ[X]).Monic ∧ (X - 1 : ℤ[X]).Monic ∧ (X + 1 : ℤ[X]).Monic := by
  refine ⟨det_gram2 _, coeff_X_zero, not_isUnit_zero, IsRoot.def.mpr (eval_X), ?_, ?_,
    monic_X, monic_X_sub_C 1, monic_X_add_C 1⟩
  · rw [det_gram3]
    exact ⟨-(X ^ 5 * (X + 1)), by ring⟩
  · simp

end OddMath.Frontier.EKGeneralQ
