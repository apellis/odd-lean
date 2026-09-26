import OddMath.Frontier.EKFinalGramEval

/-!
# Certified evaluation of the Gram determinants of §5.2

Source: Ellis–Khovanov, arXiv:1107.5610v2, §5.2, pp. 39–40.

Lemmas for proving an identity `det G_n(q) = Q(q)` in `ℤ[q]`, where `G_n(q) = EKGeneralQ.gram q n`
is the Gram matrix of the form (2.1) on `Λ'_n` in the basis `h_α`:

* **Kronecker substitution** (`eq_of_eval_of_bound`): two integer polynomials whose
  coefficients are bounded by `B` in absolute value and which agree at one integer `t > 2B`
  are equal.
* **A priori bound** (`abs_coeff_det_le`): all entries of `G_n(q)` have nonnegative coefficients,
  so every coefficient of `det G_n(q)` is bounded by `∏_α Σ_β G_n(1)_{βα}`.
  For the comparison polynomial, a majorant bound (`Maj`) is used.
* **Integer determinants** (`det_of_cert`): if `L` is lower triangular with nonzero diagonal
  and `L A = U` is upper triangular, then `det A = ∏ Uᵢᵢ / ∏ Lᵢᵢ`.  The matrix `L` may be
  produced by any procedure (here: fraction-free elimination); only the product is checked.
* **Enumeration** (`compEquiv`): a duplicate-free list of all compositions of `n` indexes the
  Gram matrix.
-/

noncomputable section
open scoped BigOperators
open Polynomial

namespace OddMath.Frontier.EKFinal
open EKGeneralQ

/-! ## Integer polynomials from coefficient lists -/

/-- `ofList [a₀, a₁, …] = a₀ + a₁ X + ⋯`. -/
def ofList : List ℤ → ℤ[X]
  | [] => 0
  | a :: l => C a + X * ofList l

/-- Horner evaluation of a coefficient list. -/
def hornerL (t : ℤ) : List ℤ → ℤ
  | [] => 0
  | a :: l => a + t * hornerL t l

theorem eval_ofList (t : ℤ) (l : List ℤ) : (ofList l).eval t = hornerL t l := by
  induction l with
  | nil => simp [ofList, hornerL]
  | cons a l ih => simp [ofList, hornerL, ih]

theorem coeff_ofList (l : List ℤ) (e : ℕ) : (ofList l).coeff e = l.getD e 0 := by
  induction l generalizing e with
  | nil => simp [ofList]
  | cons a l ih =>
    cases e with
    | zero => simp [ofList]
    | succ e =>
      rw [ofList, coeff_add, coeff_C, coeff_X_mul, ih]
      simp

/-- A product of powers of coefficient-list polynomials. -/
def prodPow (fs : List (List ℤ × ℕ)) : ℤ[X] := (fs.map fun f => (ofList f.1) ^ f.2).prod

/-- Its value at `t`. -/
def prodPowEval (t : ℤ) (fs : List (List ℤ × ℕ)) : ℤ :=
  (fs.map fun f => (hornerL t f.1) ^ f.2).prod

theorem eval_prodPow (t : ℤ) (fs : List (List ℤ × ℕ)) :
    (prodPow fs).eval t = prodPowEval t fs := by
  induction fs with
  | nil => simp [prodPow, prodPowEval]
  | cons f fs ih =>
    simp only [prodPow, prodPowEval, List.map_cons, List.prod_cons, eval_mul, eval_pow,
      eval_ofList] at ih ⊢
    rw [ih]

/-! ## Coefficient majorants -/

/-- `M` majorizes `P` coefficientwise. -/
def Maj (P M : ℤ[X]) : Prop := ∀ e, |P.coeff e| ≤ M.coeff e

theorem Maj.nonneg {P M : ℤ[X]} (h : Maj P M) (e : ℕ) : 0 ≤ M.coeff e :=
  le_trans (abs_nonneg _) (h e)

theorem Maj.mul {P M P' M' : ℤ[X]} (h : Maj P M) (h' : Maj P' M') : Maj (P * P') (M * M') := by
  intro e
  rw [coeff_mul, coeff_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_mul (h _) (h' _) (abs_nonneg _) (h.nonneg _)

theorem maj_one : Maj 1 1 := by
  intro e
  rw [coeff_one]
  split_ifs <;> simp

theorem Maj.pow {P M : ℤ[X]} (h : Maj P M) (m : ℕ) : Maj (P ^ m) (M ^ m) := by
  induction m with
  | zero => simpa using maj_one
  | succ m ih => rw [pow_succ, pow_succ]; exact ih.mul h

theorem maj_ofList (l : List ℤ) : Maj (ofList l) (ofList (l.map abs)) := by
  intro e
  rw [coeff_ofList, coeff_ofList]
  induction l generalizing e with
  | nil => simp
  | cons a l ih =>
    cases e with
    | zero => simp
    | succ e => simpa using ih e

theorem maj_prodPow (fs : List (List ℤ × ℕ)) :
    Maj (prodPow fs) (prodPow (fs.map fun f => (f.1.map abs, f.2))) := by
  induction fs with
  | nil => simpa [prodPow] using maj_one
  | cons f fs ih =>
    simp only [prodPow, List.map_cons, List.prod_cons] at ih ⊢
    exact ((maj_ofList f.1).pow f.2).mul ih

/-- Nonnegative coefficients. -/
def NN (p : ℤ[X]) : Prop := ∀ e, 0 ≤ p.coeff e

theorem NN.mul {p p' : ℤ[X]} (h : NN p) (h' : NN p') : NN (p * p') := by
  intro e
  rw [coeff_mul]
  exact Finset.sum_nonneg fun x _ => mul_nonneg (h _) (h' _)

theorem NN.prod {ι : Type*} (s : Finset ι) (f : ι → ℤ[X]) (h : ∀ i ∈ s, NN (f i)) :
    NN (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro e; rw [Finset.prod_empty, coeff_one]; split_ifs <;> simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h _ (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem NN.coeff_le_eval_one {p : ℤ[X]} (h : NN p) (e : ℕ) : p.coeff e ≤ p.eval 1 := by
  rw [eval_eq_sum_range]
  simp only [one_pow, mul_one]
  by_cases he : e < p.natDegree + 1
  · exact Finset.single_le_sum (fun i _ => h i) (Finset.mem_range.mpr he)
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact Finset.sum_nonneg fun i _ => h i

theorem Maj.le_eval_one {P M : ℤ[X]} (h : Maj P M) (e : ℕ) : |P.coeff e| ≤ M.eval 1 :=
  le_trans (h e) (NN.coeff_le_eval_one (fun e => h.nonneg e) e)

/-- Coefficient bound for a determinant with nonnegative-coefficient entries. -/
theorem abs_coeff_det_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ[X])
    (hM : ∀ i j, NN (M i j)) (e : ℕ) :
    |M.det.coeff e| ≤ ∏ j, ∑ i, (M i j).eval 1 := by
  rw [Matrix.det_apply', finset_sum_coeff]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hNN : ∀ σ : Equiv.Perm ι, NN (∏ i, M (σ i) i) :=
    fun σ => NN.prod _ _ (fun i _ => hM _ _)
  have h1 : ∀ σ : Equiv.Perm ι,
      |(((Equiv.Perm.sign σ : ℤ) : ℤ[X]) * ∏ i, M (σ i) i).coeff e| ≤
        ∏ i, (M (σ i) i).eval 1 := by
    intro σ
    rw [coeff_intCast_mul, Int.cast_id, abs_mul, ← eval_prod]
    have hs : |((Equiv.Perm.sign σ : ℤ) : ℤ)| = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [hs, one_mul, abs_of_nonneg (hNN σ e)]
    exact (hNN σ).coeff_le_eval_one e
  refine le_trans (Finset.sum_le_sum fun σ _ => h1 σ) ?_
  rw [Finset.prod_univ_sum]
  have hinj : Function.Injective (fun σ : Equiv.Perm ι => (fun i => σ i : ∀ _ : ι, ι)) :=
    fun a b h => Equiv.ext fun i => congrFun h i
  have hnn : ∀ p : ∀ _ : ι, ι, 0 ≤ ∏ i, (M (p i) i).eval 1 := by
    intro p
    exact Finset.prod_nonneg fun i _ => by
      simpa using (NN.coeff_le_eval_one (hM (p i) i) 0).trans' (hM (p i) i 0)
  calc ∑ σ : Equiv.Perm ι, ∏ i, (M (σ i) i).eval 1
      = ∑ p ∈ (Finset.univ : Finset (Equiv.Perm ι)).map ⟨_, hinj⟩, ∏ i, (M (p i) i).eval 1 := by
        rw [Finset.sum_map]; rfl
    _ ≤ ∑ p ∈ Fintype.piFinset fun _ : ι => (Finset.univ : Finset ι), ∏ i, (M (p i) i).eval 1 :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun p _ => by simp) (fun p _ _ => hnn p)

/-! ## Kronecker substitution -/

theorem eq_zero_of_eval_eq_zero (t : ℤ) (ht : 0 < t) (P : ℤ[X])
    (hb : ∀ e, 2 * |P.coeff e| < t) (h : P.eval t = 0) : P = 0 := by
  induction hn : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    have hX := X_mul_divX_add P
    have he := congrArg (eval t) hX
    rw [eval_add, eval_mul, eval_X, eval_C, h] at he
    have h0 : P.coeff 0 = 0 := by
      have hd : t ∣ P.coeff 0 := ⟨-(eval t (divX P)), by linarith⟩
      obtain ⟨c, hc⟩ := hd
      rcases eq_or_ne c 0 with hc0 | hc0
      · rw [hc, hc0, mul_zero]
      · exfalso
        have h1 := hb 0
        rw [hc, abs_mul, abs_of_pos ht] at h1
        have : 1 ≤ |c| := Int.one_le_abs hc0
        nlinarith
    have hdiv : divX P = 0 := by
      by_cases hP : P = 0
      · rw [hP, divX_zero]
      have hpos : 0 < P.natDegree := by
        by_contra hz
        push_neg at hz
        have : P = C (P.coeff 0) := eq_C_of_natDegree_le_zero hz
        rw [h0, C_0] at this
        exact hP this
      refine ih (divX P).natDegree ?_ (divX P) ?_ ?_ rfl
      · rw [natDegree_divX_eq_natDegree_tsub_one]; omega
      · intro e; rw [coeff_divX]; exact hb (e + 1)
      · rw [h0] at he
        have : t * eval t (divX P) = 0 := by linarith
        exact (mul_eq_zero.mp this).resolve_left (ne_of_gt ht)
    rw [← X_mul_divX_add P, hdiv, h0]
    simp

/-- **Kronecker substitution.** Integer polynomials with coefficients bounded by `B_P`, `B_Q`
that agree at an integer `t > 2(B_P + B_Q)` are equal. -/
theorem eq_of_eval_of_bound (P Q : ℤ[X]) (t BP BQ : ℤ) (hP : ∀ e, |P.coeff e| ≤ BP)
    (hQ : ∀ e, |Q.coeff e| ≤ BQ) (ht : 2 * (BP + BQ) < t) (h : P.eval t = Q.eval t) :
    P = Q := by
  have hBP : 0 ≤ BP := le_trans (abs_nonneg _) (hP 0)
  have hBQ : 0 ≤ BQ := le_trans (abs_nonneg _) (hQ 0)
  rw [← sub_eq_zero]
  apply eq_zero_of_eval_eq_zero t (by linarith) (P - Q)
  · intro e
    rw [coeff_sub]
    have := abs_sub (P.coeff e) (Q.coeff e)
    linarith [hP e, hQ e]
  · rw [eval_sub, h, sub_self]

/-! ## Integer matrices as lists -/

theorem getD_map_of_lt {α β : Type*} (l : List α) (f : α → β) (d : β) (i : ℕ)
    (hi : i < l.length) : (l.map f).getD i d = f l[i] := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- Entry `(i, j)` of a list-of-rows matrix (zero outside). -/
def getE (M : List (List ℤ)) (i j : ℕ) : ℤ := (M.getD i []).getD j 0

/-- The `N × N` matrix of a list of rows. -/
def ofLL (N : ℕ) (M : List (List ℤ)) : Matrix (Fin N) (Fin N) ℤ := Matrix.of fun i j => getE M i j

def dotL : List ℤ → List ℤ → ℤ
  | a :: as, b :: bs => a * b + dotL as bs
  | _, _ => 0

/-- Column `j`. -/
def colL (B : List (List ℤ)) (j : ℕ) : List ℤ := B.map fun r => r.getD j 0

/-- Product of list matrices (`N` columns). -/
def mulLL (N : ℕ) (A B : List (List ℤ)) : List (List ℤ) :=
  A.map fun r => (List.range N).map fun j => dotL r (colL B j)

theorem dotL_eq (N : ℕ) (a b : List ℤ) (ha : a.length = N) (hb : b.length = N) :
    dotL a b = ∑ k : Fin N, a.getD k 0 * b.getD k 0 := by
  induction N generalizing a b with
  | zero =>
    rw [List.length_eq_zero_iff] at ha
    subst ha
    simp [dotL]
  | succ N ih =>
    cases a with
    | nil => simp at ha
    | cons x a =>
      cases b with
      | nil => simp at hb
      | cons y b =>
        simp only [List.length_cons, add_left_inj] at ha hb
        rw [dotL, ih a b ha hb, Fin.sum_univ_succ]
        simp

/-- `N` rows of length `N`. -/
def shapeOK (N : ℕ) (M : List (List ℤ)) : Bool :=
  M.length == N && M.all fun r => r.length == N

theorem shapeOK_spec {N : ℕ} {M : List (List ℤ)} (h : shapeOK N M = true) :
    M.length = N ∧ ∀ r ∈ M, r.length = N := by
  simp only [shapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1, h.2⟩

theorem getE_mulLL (N : ℕ) (A B : List (List ℤ)) (hA : shapeOK N A = true)
    (hB : shapeOK N B = true) (i j : Fin N) :
    getE (mulLL N A B) i j = ∑ k : Fin N, getE A i k * getE B k j := by
  obtain ⟨hAl, hAr⟩ := shapeOK_spec hA
  obtain ⟨hBl, -⟩ := shapeOK_spec hB
  have hi : (i : ℕ) < A.length := by omega
  simp only [getE, mulLL]
  rw [getD_map_of_lt _ _ _ _ hi, getD_map_of_lt _ _ _ _ (by simp), List.getElem_range,
    dotL_eq N _ _ (hAr _ (List.getElem_mem hi)) (by simp [colL, hBl])]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (k : ℕ) < B.length := by omega
  rw [List.getD_eq_getElem _ _ hi, colL, getD_map_of_lt _ _ _ _ hk, List.getD_eq_getElem _ _ hk]

theorem ofLL_mulLL (N : ℕ) (A B : List (List ℤ)) (hA : shapeOK N A = true)
    (hB : shapeOK N B = true) : ofLL N (mulLL N A B) = ofLL N A * ofLL N B := by
  ext i j
  rw [ofLL, Matrix.of_apply, getE_mulLL N A B hA hB, Matrix.mul_apply]
  rfl

theorem shapeOK_mulLL (N : ℕ) (A B : List (List ℤ)) (hA : shapeOK N A = true) :
    shapeOK N (mulLL N A B) = true := by
  obtain ⟨hAl, -⟩ := shapeOK_spec hA
  simp [shapeOK, mulLL, hAl]

/-- Lower triangular (entries above the diagonal vanish). -/
def lowerOK (N : ℕ) (M : List (List ℤ)) : Bool :=
  (List.range N).all fun i => (List.range N).all fun j => decide (j ≤ i) || getE M i j == 0

/-- Upper triangular (entries below the diagonal vanish). -/
def upperOK (N : ℕ) (M : List (List ℤ)) : Bool :=
  (List.range N).all fun i => (List.range N).all fun j => decide (i ≤ j) || getE M i j == 0

def diagProd (N : ℕ) (M : List (List ℤ)) : ℤ := ((List.range N).map fun i => getE M i i).prod

theorem prod_range_eq (N : ℕ) (f : ℕ → ℤ) :
    ((List.range N).map f).prod = ∏ i : Fin N, f i := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Fin.prod_univ_castSucc]
    simp

theorem det_ofLL_lower {N : ℕ} {M : List (List ℤ)} (h : lowerOK N M = true) :
    (ofLL N M).det = diagProd N M := by
  rw [Matrix.det_of_lowerTriangular, diagProd, prod_range_eq]
  · rfl
  · intro i j hij
    simp only [lowerOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    have hij' : (i : ℕ) < j := hij
    exact (h i i.isLt j j.isLt).resolve_left (by omega)

theorem det_ofLL_upper {N : ℕ} {M : List (List ℤ)} (h : upperOK N M = true) :
    (ofLL N M).det = diagProd N M := by
  rw [Matrix.det_of_upperTriangular, diagProd, prod_range_eq]
  · rfl
  · intro i j hij
    simp only [upperOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
      beq_iff_eq] at h
    have hij' : (j : ℕ) < i := hij
    exact (h i i.isLt j j.isLt).resolve_left (by omega)

/-- The determinant certificate: `L` lower triangular, `L·A` upper triangular, and
`∏ (L·A)ᵢᵢ = (∏ Lᵢᵢ) · v` with `∏ Lᵢᵢ ≠ 0`. -/
def certCheck (N : ℕ) (A L : List (List ℤ)) (v : ℤ) : Bool :=
  shapeOK N A && shapeOK N L && lowerOK N L && upperOK N (mulLL N L A) &&
    !(diagProd N L == 0) && diagProd N (mulLL N L A) == diagProd N L * v

theorem det_of_cert (N : ℕ) (A L : List (List ℤ)) (v : ℤ) (h : certCheck N A L v = true) :
    (ofLL N A).det = v := by
  simp only [certCheck, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hA, hL⟩, hlow⟩, hup⟩, hne⟩, heq⟩ := h
  have hmul := congrArg Matrix.det (ofLL_mulLL N L A hL hA)
  rw [Matrix.det_mul, det_ofLL_upper hup, det_ofLL_lower hlow, heq] at hmul
  exact (mul_left_cancel₀ hne hmul).symm

/-! ## Fraction-free elimination (the certificate generator; its output is checked) -/

/-- One elimination step on a row pair `(A-part, L-part)` with pivot row `(a :: as, lp)`. -/
def bRow (prev p r : ℤ) (ps rs : List ℤ) : List ℤ :=
  List.zipWith (fun pj rj => (p * rj - r * pj) / prev) ps rs

def bareissAux : ℕ → ℤ → List (List ℤ × List ℤ) → List (List ℤ)
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, prev, (a, lp) :: rest =>
    match a with
    | [] => lp :: bareissAux fuel prev rest
    | p :: ps => lp :: bareissAux fuel p (rest.map fun row =>
        match row.1 with
        | [] => row
        | r :: rs => (bRow prev p r ps rs, bRow prev p r lp row.2))

/-- The multiplier matrix `L` of fraction-free elimination on `A` (no pivoting). -/
def bareissL (N : ℕ) (A : List (List ℤ)) : List (List ℤ) :=
  bareissAux N 1 (A.zip ((List.range N).map fun i => (List.range N).map fun j =>
    if i = j then 1 else 0))

/-! ## Enumerating compositions -/

def compsAux : ℕ → ℕ → List (List ℕ)
  | 0, n => if n = 0 then [[]] else []
  | fuel + 1, n => if n = 0 then [[]] else
      (List.range n).flatMap fun f => (compsAux fuel (n - (f + 1))).map ((f + 1) :: ·)

/-- The compositions of `n`, listed by first part. -/
def compsL (n : ℕ) : List (List ℕ) := compsAux n n

/-- `L` lists every composition of `n` exactly once. -/
def CompsOK (n : ℕ) (L : List (List ℕ)) : Prop :=
  (∀ l ∈ L, (∀ a ∈ l, 0 < a) ∧ l.sum = n) ∧ L.Nodup ∧ L.length = 2 ^ (n - 1)

instance (n : ℕ) (L : List (List ℕ)) : Decidable (CompsOK n L) := by
  unfold CompsOK; infer_instance

def compOf {n : ℕ} {L : List (List ℕ)} (h : CompsOK n L) (i : Fin L.length) : Composition n :=
  ⟨L.get i, fun hi => (h.1 _ (List.get_mem L i)).1 _ hi, (h.1 _ (List.get_mem L i)).2⟩

theorem compOf_bijective {n : ℕ} {L : List (List ℕ)} (h : CompsOK n L) :
    Function.Bijective (compOf h) := by
  have hinj : Function.Injective (compOf h) := by
    intro i j hij
    have : L.get i = L.get j := congrArg Composition.blocks hij
    exact (List.nodup_iff_injective_get.mp h.2.1) this
  exact (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj, by rw [Fintype.card_fin, composition_card, h.2.2]⟩

/-- The enumeration as an equivalence. -/
def compEquiv {n : ℕ} {L : List (List ℕ)} (h : CompsOK n L) : Fin L.length ≃ Composition n :=
  Equiv.ofBijective _ (compOf_bijective h)

/-- The Gram matrix at `q = t` as a list matrix, in the order of `L`. -/
def gramLL (t : ℤ) (L : List (List ℕ)) : List (List ℤ) :=
  L.map fun b => L.map fun a => fastQ t b a

theorem det_gram_eq (t : ℤ) {n : ℕ} {L : List (List ℕ)} (h : CompsOK n L) :
    (gram t n).det = (ofLL L.length (gramLL t L)).det := by
  rw [← Matrix.det_submatrix_equiv_self (compEquiv h)]
  congr 1
  ext i j
  rw [Matrix.submatrix_apply, gram_fastQ, ofLL, Matrix.of_apply, getE, gramLL,
    getD_map_of_lt _ _ _ _ i.isLt, getD_map_of_lt _ _ _ _ j.isLt]
  rfl

/-- The a priori bound `∏_α Σ_β G(1)_{βα}` in list form. -/
def boundL (L : List (List ℕ)) : ℤ := (L.map fun a => (L.map fun b => fastQ 1 b a).sum).prod

theorem gram_NN (n : ℕ) (β α : Composition n) : NN (gram (X : ℤ[X]) n β α) := by
  intro e
  rw [coeff_gram]
  exact Nat.cast_nonneg _

theorem eval_gram (t : ℤ) (n : ℕ) (β α : Composition n) :
    (gram (X : ℤ[X]) n β α).eval t = gram t n β α := by
  have := map_gram (evalRingHom t) (X : ℤ[X]) n
  rw [coe_evalRingHom, eval_X] at this
  rw [← this]
  rfl

theorem abs_coeff_gram_det_le {n : ℕ} {L : List (List ℕ)} (h : CompsOK n L) (e : ℕ) :
    |(gram (X : ℤ[X]) n).det.coeff e| ≤ boundL L := by
  refine le_trans (abs_coeff_det_le _ (gram_NN n) e) (le_of_eq ?_)
  simp only [eval_gram, gram_fastQ]
  rw [boundL, ← Fin.prod_univ_fun_getElem, ← (compEquiv h).prod_comp]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Fin.sum_univ_fun_getElem, ← (compEquiv h).sum_comp]
  rfl

theorem eval_gram_det (t : ℤ) (n : ℕ) : (gram (X : ℤ[X]) n).det.eval t = (gram t n).det := by
  have h1 := RingHom.map_det (evalRingHom t) (gram (X : ℤ[X]) n)
  rw [map_gram, coe_evalRingHom, eval_X] at h1
  exact h1

/-- The absolute-value majorant list of a factor list. -/
def absFs (fs : List (List ℤ × ℕ)) : List (List ℤ × ℕ) := fs.map fun f => (f.1.map abs, f.2)

/-- The combined check: the certificate for `det G_n(2^K)` against the value of the
comparison polynomial, and `2^K` exceeding twice the sum of the coefficient bounds. -/
def gramCheck (K : ℕ) (L : List (List ℕ)) (fs : List (List ℤ × ℕ)) : Bool :=
  certCheck L.length (gramLL (2 ^ K) L) (bareissL L.length (gramLL (2 ^ K) L))
      (prodPowEval (2 ^ K) fs) &&
    decide (2 * (boundL L + prodPowEval 1 (absFs fs)) < 2 ^ K)

/-- **Certified Gram determinant.** -/
theorem gram_det_eq_of_check {n : ℕ} {L : List (List ℕ)} (hL : CompsOK n L) (K : ℕ)
    (fs : List (List ℤ × ℕ)) (h : gramCheck K L fs = true) :
    (gram (X : ℤ[X]) n).det = prodPow fs := by
  simp only [gramCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hc, hb⟩ := h
  apply eq_of_eval_of_bound _ _ (2 ^ K) (boundL L) (prodPowEval 1 (absFs fs))
    (abs_coeff_gram_det_le hL)
  · intro e
    have := (maj_prodPow fs).le_eval_one e
    rwa [eval_prodPow] at this
  · exact hb
  · rw [eval_gram_det, det_gram_eq _ hL, det_of_cert _ _ _ _ hc, eval_prodPow]

end OddMath.Frontier.EKFinal
