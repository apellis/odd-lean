import OddMath.Frontier.EKRestRibbon
import OddMath.Frontier.EKRestEval
import OddMath.Frontier.EKRestDet4

/-!
# EK §2.4: `Λ′` is the graded dual `NΛ_q` of the quantum quasi-symmetric functions `QΛ_q`

Source: Ellis–Khovanov, arXiv:1107.5610v2, §2.4, pp. 21–22, at arbitrary `q` in an arbitrary
commutative ring `k`.

EK recall `QΛ_q` from Thibon–Ung [30] and Aguiar–Mahajan [1] and define `NΛ_q` as its graded
dual; they do not restate the structure maps.  Here `QΛ_q` is made precise as follows.

* As a `k`-module `QΛ_q` is free on the compositions `α` (basis `M_α`, the monomial
  quasi-symmetric functions); compositions are encoded as words `w : W` (letter `i` is the part
  `i + 1`).
* Its product is the **quantum quasi-shuffle** `M_I · M_J = Σ_K c_q(I, J; K) M_K`
  (`qsh`, `qMul`): recursively, for `I = a·I'`, `J = b·J'`,
  `a·I' ∗ b·J' = a·(I' ∗ b·J') + q^{b(a+|I'|)} b·(a·I' ∗ J') + q^{b|I'|} (a+b)·(I' ∗ J')`,
  `∅ ∗ J = J`, `I ∗ ∅ = I`: a part of `J` placed before a part of `I` contributes
  `q^{product of the two parts}`.  (This is the rule for monomial quasi-symmetric functions in
  variables with `x_j x_i = q x_i x_j` for `i < j`; that realization is not formalized here.)
* Its coproduct is deconcatenation of compositions, its unit `M_∅`, its counit `M_α ↦ δ_{α∅}`.
* The ribbon (fundamental) basis is `R_β = Σ_{γ refines β} M_γ` (`Rfund`).

`NΛ_q` is the graded dual of `QΛ_q`.  The pairing `⟨h_α, M_β⟩ = δ_{αβ}` (`pair`) identifies
each graded piece of `Λ′` with the `k`-dual of the corresponding (finite free) graded piece of
`QΛ_q`, so it identifies `Λ′` with `NΛ_q` as graded modules, `h_α ↦ M̂_α`.  The statements
below say that this identification is an isomorphism of `q`-bialgebras and sends `h̃_α ↦ R̂_α`:

* `pair_coproduct` (coproduct of `Λ′` = transpose of the quantum quasi-shuffle):
  `⟨Δx, M_I ⊗ M_J⟩ = ⟨x, M_I · M_J⟩`;
* `pair_mul` (product of `Λ′` = transpose of deconcatenation):
  `⟨xy, M_K⟩ = Σ_{K = K₁K₂} ⟨x, M_{K₁}⟩⟨y, M_{K₂}⟩`;
* `pair_one`, `pair_M_one` (unit and counit);
* `pair_hT_Rfund` (**the isomorphism `h̃_α ↦ R̂_α`**): `⟨h̃_α, R_β⟩ = δ_{αβ}`, where
  `h̃_α` is (2.31) (`EKRest.hT`);
* `eq_2_33` (in `EKRest`) and the determinant identity `EKRest.mobU_mul_zeta` give (2.33) and
  the unitriangularity of (2.31);
* `eq_2_32`: `e_n = (-1)^{n(n-1)/2} h̃_{(1ⁿ)}` in `Λ′` at `q = -1` over `ℤ`;
* `ek_sec_2_4` collects these statements.

Only the transposition identities above are formalized; the `q`-bialgebra axioms of `QΛ_q`
itself (for instance associativity of the quantum quasi-shuffle) are not restated here.
-/

noncomputable section
open scoped BigOperators TensorProduct

namespace OddMath.Frontier.EKFinal
open EKGeneralQ
open EKFreeCoproduct (W partWord)

variable {k : Type*} [CommRing k] (q : k)

/-! ## The quantum quasi-shuffle on compositions -/

/-- The quantum quasi-shuffle of two compositions (lists of positive parts): the list of
pairs `(K, e)` contributing `q^e M_K` to `M_I · M_J`. -/
def qsh : List ℕ → List ℕ → List (List ℕ × ℕ)
  | [], J => [(J, 0)]
  | a :: I, [] => [(a :: I, 0)]
  | a :: I, b :: J =>
    (qsh I (b :: J)).map (fun p => (a :: p.1, p.2)) ++
    (qsh (a :: I) J).map (fun p => (b :: p.1, p.2 + b * (a + I.sum))) ++
    (qsh I J).map (fun p => ((a + b) :: p.1, p.2 + b * I.sum))
termination_by I J => I.length + J.length

/-- The structure constant `c_q(I, J; K)`. -/
def qcoef (I J K : List ℕ) : k := ((qsh I J).map fun p => if p.1 = K then q ^ p.2 else 0).sum

theorem qcoef_nil_left (J K : List ℕ) : qcoef q [] J K = if J = K then 1 else 0 := by
  simp [qcoef, qsh]

theorem qcoef_nil_right (a : ℕ) (I K : List ℕ) :
    qcoef q (a :: I) [] K = if a :: I = K then 1 else 0 := by
  simp [qcoef, qsh]

theorem qcoef_cons_cons (a b : ℕ) (I J : List ℕ) (c : ℕ) (K : List ℕ) :
    qcoef q (a :: I) (b :: J) (c :: K) =
      (if a = c then qcoef q I (b :: J) K else 0) +
      (if b = c then q ^ (b * (a + I.sum)) * qcoef q (a :: I) J K else 0) +
      (if a + b = c then q ^ (b * I.sum) * qcoef q I J K else 0) := by
  rw [qcoef, qsh]
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def,
    List.cons.injEq]
  congr 1
  congr 1
  · split_ifs with h
    · simp only [h, true_and]; rfl
    · rw [List.sum_eq_zero]; intro x hx; simp only [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx; simp [h]
  · split_ifs with h
    · rw [qcoef, ← List.sum_map_mul_left]
      congr 1; apply List.map_congr_left; intro p _
      simp only [h, true_and]; split_ifs <;> simp [pow_add, mul_comm]
    · rw [List.sum_eq_zero]; intro x hx; simp only [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx; simp [h]
  · split_ifs with h
    · rw [qcoef, ← List.sum_map_mul_left]
      congr 1; apply List.map_congr_left; intro p _
      simp only [h, true_and]; split_ifs <;> simp [pow_add, mul_comm]
    · rw [List.sum_eq_zero]; intro x hx; simp only [List.mem_map] at hx
      obtain ⟨p, _, rfl⟩ := hx; simp [h]

theorem qsh_sum (I J : List ℕ) : ∀ p ∈ qsh I J, p.1.sum = I.sum + J.sum := by
  induction I, J using qsh.induct with
  | case1 J => intro p hp; simp [qsh] at hp; simp [hp]
  | case2 a I => intro p hp; simp [qsh] at hp; simp [hp]
  | case3 a I b J ih1 ih2 ih3 =>
    intro p hp
    rw [qsh] at hp
    simp only [List.mem_append, List.mem_map] at hp
    rcases hp with (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩
    · simp [ih1 r hr]; ring
    · simp [ih2 r hr]; ring
    · simp [ih3 r hr]; ring

theorem qcoef_nil_target (I J : List ℕ) (hI : ∀ a ∈ I, 0 < a) (hJ : ∀ a ∈ J, 0 < a) :
    qcoef q I J [] = if I = [] ∧ J = [] then 1 else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h; simp [qcoef, qsh]
  · rw [qcoef, List.sum_eq_zero]
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    rw [if_neg]
    intro hp0
    have hs := qsh_sum I J p hp
    rw [hp0, List.sum_nil] at hs
    apply h
    constructor
    · cases I with
      | nil => rfl
      | cons a I => have := hI a (by simp); simp at hs; omega
    · cases J with
      | nil => rfl
      | cons a J => have := hJ a (by simp); simp at hs; omega

/-! ## Splits of a composition -/

/-- All coordinatewise splits `0 ≤ u ≤ K`. -/
def splitsAll : List ℕ → List (List ℕ)
  | [] => [[]]
  | c :: K => (List.range (c + 1)).flatMap fun i => (splitsAll K).map (i :: ·)

/-- Coordinatewise difference. -/
def subL (K u : List ℕ) : List ℕ := List.zipWith (· - ·) K u

/-- Deleting zero parts. -/
def compress (u : List ℕ) : List ℕ := u.filter (fun a => 0 < a)

theorem compress_cons_zero (u : List ℕ) : compress (0 :: u) = compress u := by
  simp [compress]

theorem compress_cons_pos {i : ℕ} (hi : 0 < i) (u : List ℕ) :
    compress (i :: u) = i :: compress u := by
  simp [compress, hi]

theorem sum_compress (u : List ℕ) : (compress u).sum = u.sum := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [compress_cons_zero, ih]; simp
    · rw [compress_cons_pos ha]; simp [ih]

/-- The coefficient side: `Σ_{u ≤ K, compress u = I, compress (K-u) = J} q^{cross(u, K-u)}`. -/
def splitCoef (K I J : List ℕ) : k :=
  ((splitsAll K).map fun u =>
    if compress u = I ∧ compress (subL K u) = J then q ^ EKRest.crossL u (subL K u) else 0).sum

theorem sum_range_split (c : ℕ) (hc : 0 < c) (f : ℕ → k) :
    ((List.range (c + 1)).map f).sum =
      f 0 + f c + ∑ i ∈ Finset.Ioo 0 c, f i := by
  rw [EKAppendixData.list_sum_range, Finset.sum_range_succ, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot hc]
  rw [show Finset.Ico (0 + 1) c = Finset.Ioo 0 c by ext; simp; omega]
  ring

theorem list_sum_flatMap_gen {α M : Type*} [AddCommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem list_map_sum_gen {α M N : Type*} [AddCommMonoid M] [AddCommMonoid N] (g : M →+ N)
    (l : List α) (f : α → M) : g ((l.map f).sum) = (l.map fun a => g (f a)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem list_sum_flatMap {α : Type*} (l : List α) (f : α → List k) :
    (l.flatMap f).sum = (l.map fun a => (f a).sum).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

theorem splitCoef_cons (c : ℕ) (K I J : List ℕ) :
    splitCoef q (c :: K) I J = ((List.range (c + 1)).map fun i =>
      ((splitsAll K).map fun u =>
        if compress (i :: u) = I ∧ compress ((c - i) :: subL K u) = J then
          q ^ ((c - i) * u.sum + EKRest.crossL u (subL K u)) else 0).sum).sum := by
  simp only [splitCoef, splitsAll, List.map_flatMap, list_sum_flatMap, List.map_map,
    Function.comp_def, subL, List.zipWith_cons_cons, EKRest.crossL]

theorem sum_ite_mul (l : List (List ℕ)) (P : List ℕ → Prop) [DecidablePred P] (f : List ℕ → k)
    (r : k) : (l.map fun u => if P u then r * f u else 0).sum =
      r * (l.map fun u => if P u then f u else 0).sum := by
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro u _
  split_ifs <;> simp

theorem T_zero (c : ℕ) (hc : 0 < c) (K I J : List ℕ) :
    ((splitsAll K).map fun u =>
      if compress (0 :: u) = I ∧ compress ((c - 0) :: subL K u) = J then
        q ^ ((c - 0) * u.sum + EKRest.crossL u (subL K u)) else 0).sum =
    match J with
    | [] => 0
    | b :: J' => if b = c then q ^ (c * I.sum) * splitCoef q K I J' else 0 := by
  cases J with
  | nil =>
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨u, _, rfl⟩ := hx
    rw [if_neg]
    rintro ⟨-, h⟩
    rw [Nat.sub_zero, compress_cons_pos hc] at h
    exact List.cons_ne_nil _ _ h
  | cons b J' =>
    simp only [Nat.sub_zero, compress_cons_zero, compress_cons_pos hc, List.cons.injEq]
    by_cases hb : b = c
    · subst hb
      rw [if_pos rfl, splitCoef, ← sum_ite_mul]
      congr 1
      apply List.map_congr_left
      intro u _
      by_cases h1 : compress u = I
      · simp only [h1, true_and, true_and]
        split_ifs
        · rw [← sum_compress u, h1, pow_add]
        · rfl
      · simp [h1]
    · rw [if_neg hb]
      apply List.sum_eq_zero
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨u, _, rfl⟩ := hx
      rw [if_neg]
      rintro ⟨-, h, -⟩
      exact hb h.symm

theorem T_top (c : ℕ) (hc : 0 < c) (K I J : List ℕ) :
    ((splitsAll K).map fun u =>
      if compress (c :: u) = I ∧ compress ((c - c) :: subL K u) = J then
        q ^ ((c - c) * u.sum + EKRest.crossL u (subL K u)) else 0).sum =
    match I with
    | [] => 0
    | a :: I' => if a = c then splitCoef q K I' J else 0 := by
  cases I with
  | nil =>
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨u, _, rfl⟩ := hx
    rw [if_neg]
    rintro ⟨h, -⟩
    rw [compress_cons_pos hc] at h
    exact List.cons_ne_nil _ _ h
  | cons a I' =>
    simp only [Nat.sub_self, compress_cons_zero, compress_cons_pos hc, List.cons.injEq,
      zero_mul, zero_add]
    by_cases ha : a = c
    · subst ha
      rw [if_pos rfl, splitCoef]
      congr 1
      apply List.map_congr_left
      intro u _
      simp
    · rw [if_neg ha]
      apply List.sum_eq_zero
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨u, _, rfl⟩ := hx
      rw [if_neg]
      rintro ⟨⟨h, -⟩, -⟩
      exact ha h.symm

theorem T_mid (c i : ℕ) (hi : 0 < i) (hic : i < c) (K I J : List ℕ) :
    ((splitsAll K).map fun u =>
      if compress (i :: u) = I ∧ compress ((c - i) :: subL K u) = J then
        q ^ ((c - i) * u.sum + EKRest.crossL u (subL K u)) else 0).sum =
    match I, J with
    | a :: I', b :: J' =>
        if a = i ∧ b = c - i then q ^ ((c - i) * I'.sum) * splitCoef q K I' J' else 0
    | _, _ => 0 := by
  have hci : 0 < c - i := by omega
  rcases I with _ | ⟨a, I'⟩
  · apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨u, _, rfl⟩ := hx
    rw [if_neg]
    rintro ⟨h, -⟩
    rw [compress_cons_pos hi] at h
    exact List.cons_ne_nil _ _ h
  rcases J with _ | ⟨b, J'⟩
  · apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨u, _, rfl⟩ := hx
    rw [if_neg]
    rintro ⟨-, h⟩
    rw [compress_cons_pos hci] at h
    exact List.cons_ne_nil _ _ h
  simp only [compress_cons_pos hi, compress_cons_pos hci, List.cons.injEq]
  by_cases hab : a = i ∧ b = c - i
  · obtain ⟨rfl, rfl⟩ := hab
    rw [if_pos ⟨rfl, rfl⟩, splitCoef, ← sum_ite_mul]
    congr 1
    apply List.map_congr_left
    intro u _
    by_cases h1 : compress u = I'
    · simp only [h1, true_and]
      split_ifs
      · rw [← sum_compress u, h1, pow_add]
      · rfl
    · simp [h1]
  · rw [if_neg hab]
    apply List.sum_eq_zero
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨u, _, rfl⟩ := hx
    rw [if_neg]
    rintro ⟨⟨h1, -⟩, ⟨h2, -⟩⟩
    exact hab ⟨h1.symm, h2.symm⟩

theorem T_mid_sum (c : ℕ) (K I J : List ℕ) (hI : ∀ a ∈ I, 0 < a) (hJ : ∀ a ∈ J, 0 < a) :
    ∑ i ∈ Finset.Ioo 0 c, ((splitsAll K).map fun u =>
      if compress (i :: u) = I ∧ compress ((c - i) :: subL K u) = J then
        q ^ ((c - i) * u.sum + EKRest.crossL u (subL K u)) else 0).sum =
    match I, J with
    | a :: I', b :: J' => if a + b = c then q ^ (b * I'.sum) * splitCoef q K I' J' else 0
    | _, _ => 0 := by
  rw [Finset.sum_congr rfl (fun i hi =>
    T_mid q c i (Finset.mem_Ioo.mp hi).1 (Finset.mem_Ioo.mp hi).2 K I J)]
  rcases I with _ | ⟨a, I'⟩
  · simp
  rcases J with _ | ⟨b, J'⟩
  · simp
  have ha := hI a (by simp)
  have hb := hJ b (by simp)
  simp only
  by_cases habc : a + b = c
  · rw [if_pos habc, Finset.sum_eq_single a]
    · rw [if_pos ⟨rfl, by omega⟩, show c - a = b by omega]
    · intro i _ hia; rw [if_neg]; rintro ⟨h, -⟩; exact hia h.symm
    · intro h; exact absurd (Finset.mem_Ioo.mpr ⟨ha, by omega⟩) h
  · rw [if_neg habc]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_Ioo] at hi
    rw [if_neg]; rintro ⟨rfl, h⟩; omega

/-- **The combinatorial core of §2.4:** the coefficient of `h_I ⊗ h_J` in `Δ(h_K)` is the
quantum quasi-shuffle structure constant `c_q(I, J; K)`. -/
theorem splitCoef_eq_qcoef (K I J : List ℕ) (hK : ∀ a ∈ K, 0 < a) (hI : ∀ a ∈ I, 0 < a)
    (hJ : ∀ a ∈ J, 0 < a) : splitCoef q K I J = qcoef q I J K := by
  induction K generalizing I J with
  | nil =>
    rw [qcoef_nil_target q I J hI hJ]
    simp only [splitCoef, splitsAll, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero, compress, List.filter_nil, subL, List.zipWith_nil_left]
    split_ifs with h1 h2 h2
    · simp [EKRest.crossL]
    · exact absurd ⟨h1.1.symm, h1.2.symm⟩ h2
    · exact absurd ⟨h2.1.symm, h2.2.symm⟩ h1
    · rfl
  | cons c K ih =>
    have hc : 0 < c := hK c (by simp)
    have hK' : ∀ a ∈ K, 0 < a := fun a ha => hK a (by simp [ha])
    rw [splitCoef_cons, sum_range_split c hc, T_zero q c hc, T_top q c hc,
      T_mid_sum q c K I J hI hJ]
    rcases I with _ | ⟨a, I'⟩ <;> rcases J with _ | ⟨b, J'⟩
    · simp [qcoef, qsh]
    · have hb := hJ b (by simp)
      simp only [add_zero, Finset.sum_const_zero, List.sum_nil, mul_zero, zero_mul]
      rw [qcoef_nil_left]
      by_cases hbc : b = c
      · subst hbc
        rw [if_pos rfl, ih [] J' hK' (by simp) (fun x hx => hJ x (by simp [hx])),
          qcoef_nil_left]
        simp
      · rw [if_neg hbc, if_neg]; intro h; exact hbc (List.cons.inj h).1
    · have ha := hI a (by simp)
      simp only [zero_add, Finset.sum_const_zero, add_zero]
      rw [qcoef_nil_right]
      by_cases hac : a = c
      · subst hac
        rw [if_pos rfl, ih I' [] hK' (fun x hx => hI x (by simp [hx])) (by simp)]
        cases I' with
        | nil => rw [qcoef_nil_left]; simp
        | cons a' I'' => rw [qcoef_nil_right]; simp
      · rw [if_neg hac, if_neg]; intro h; exact hac (List.cons.inj h).1
    · have ha := hI a (by simp)
      have hb := hJ b (by simp)
      have hI' : ∀ x ∈ I', 0 < x := fun x hx => hI x (by simp [hx])
      have hJ' : ∀ x ∈ J', 0 < x := fun x hx => hJ x (by simp [hx])
      dsimp only
      rw [qcoef_cons_cons, ih I' (b :: J') hK' hI' hJ, ih (a :: I') J' hK' hI hJ',
        ih I' J' hK' hI' hJ']
      simp only [List.sum_cons]
      split_ifs <;> subst_vars <;> ring

/-! ## The coproduct of `Λ′` on an arbitrary word -/

theorem coproduct_hWord_list (K : List ℕ) :
    coproduct q (hWord k K) = ((splitsAll K).map fun u =>
      q ^ EKRest.crossL u (subL K u) • (hWord k u ⊗ₜ[k] hWord k (subL K u))).sum := by
  induction K with
  | nil =>
    simp [splitsAll, subL, EKRest.crossL, hWord, coproduct_one, tensorOne]
  | cons c K ih =>
    have hw : hWord k (c :: K) = h k c * hWord k K := by simp [hWord]
    rw [hw, coproduct_mul, coproduct_h, ih, splitsAll, List.map_flatMap, list_sum_flatMap_gen,
      EKAppendixData.list_sum_range, ← Fin.sum_univ_eq_sum_range]
    simp only [tensorMul, map_sum, LinearMap.sum_apply, list_map_sum_gen]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_list_sum, List.map_map, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u _
    change tensorMul q _ _ = _
    rw [tensorMul_smul_right]
    have hm := tensorMul_hWords q (k := k) [i.val] [c - i.val] u (subL K u)
    simp only [hWord, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      List.sum_cons, List.sum_nil, add_zero] at hm
    simp only [hWord] at hm ⊢
    rw [hm, smul_smul]
    simp only [Function.comp_apply, subL, List.zipWith_cons_cons, EKRest.crossL, List.map_cons,
      List.prod_cons, pow_add]
    congr 1
    ring

/-! ## Words and compositions -/

/-- The composition of a word (letter `i` is the part `i + 1`). -/
def wl (w : W) : List ℕ := w.toList.map (· + 1)

theorem wl_pos (w : W) : ∀ a ∈ wl w, 0 < a := by
  intro a ha
  simp only [wl, List.mem_map] at ha
  obtain ⟨b, _, rfl⟩ := ha
  omega

theorem toList_partWord_pos (l : List ℕ) (hl : ∀ a ∈ l, 0 < a) :
    (partWord l).toList = l.map Nat.pred := EKPairingAdjoint.partWord_positive l hl

theorem partWord_wl (w : W) : partWord (wl w) = w := by
  apply FreeMonoid.toList.injective
  rw [toList_partWord_pos _ (wl_pos w), wl, List.map_map]
  conv_rhs => rw [← List.map_id w.toList]
  apply List.map_congr_left
  intro a _
  simp

theorem wl_partWord (l : List ℕ) (hl : ∀ a ∈ l, 0 < a) : wl (partWord l) = l := by
  rw [wl, toList_partWord_pos l hl, List.map_map]
  conv_rhs => rw [← List.map_id l]
  apply List.map_congr_left
  intro a ha
  have := hl a ha
  simp only [Function.comp_apply, id]
  exact Nat.succ_pred_eq_of_pos this

theorem compress_pos (u : List ℕ) : ∀ a ∈ compress u, 0 < a := by
  intro a ha
  simp only [compress, List.mem_filter, decide_eq_true_eq] at ha
  exact ha.2

theorem partWord_compress (u : List ℕ) : partWord (compress u) = partWord u := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rw [compress_cons_zero, ih]; rfl
    · rw [compress_cons_pos ha]
      obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
      simp only [partWord, ih]

theorem partWord_eq_iff (u : List ℕ) (w : W) : partWord u = w ↔ compress u = wl w := by
  constructor
  · intro h
    rw [← h, ← partWord_compress, wl_partWord _ (compress_pos u)]
  · intro h
    rw [← partWord_compress, h, partWord_wl]

theorem hWord_wl (w : W) : hWord k (wl w) = wordBasis k w := by
  rw [← partWord_value, partWord_wl]

theorem qsh_pos (I J : List ℕ) (hI : ∀ a ∈ I, 0 < a) (hJ : ∀ a ∈ J, 0 < a) :
    ∀ p ∈ qsh I J, ∀ a ∈ p.1, 0 < a := by
  induction I, J using qsh.induct with
  | case1 J => intro p hp; simp [qsh] at hp; rw [hp]; exact hJ
  | case2 a I => intro p hp; simp [qsh] at hp; rw [hp]; exact hI
  | case3 a I b J ih1 ih2 ih3 =>
    have ha := hI a (by simp)
    have hb := hJ b (by simp)
    have hI' : ∀ x ∈ I, 0 < x := fun x hx => hI x (by simp [hx])
    have hJ' : ∀ x ∈ J, 0 < x := fun x hx => hJ x (by simp [hx])
    intro p hp
    rw [qsh] at hp
    simp only [List.mem_append, List.mem_map] at hp
    rcases hp with (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨r, hr, rfl⟩
    · intro x hx; simp only [List.mem_cons] at hx
      rcases hx with rfl | hx; exact ha; exact ih1 hI' hJ r hr x hx
    · intro x hx; simp only [List.mem_cons] at hx
      rcases hx with rfl | hx; exact hb; exact ih2 hI hJ' r hr x hx
    · intro x hx; simp only [List.mem_cons] at hx
      rcases hx with rfl | hx; omega; exact ih3 hI' hJ' r hr x hx

/-! ## `QΛ_q`, its product, and the pairing with `Λ′` -/

instance : DecidableEq W := inferInstanceAs (DecidableEq (List ℕ))

variable (k) in
/-- `QΛ_q` as a `k`-module: free on compositions (words), basis `M_α`. -/
abbrev QSym := W →₀ k

variable (k) in
/-- The monomial quasi-symmetric function `M_α`. -/
def M (w : W) : QSym k := Finsupp.single w 1

/-- The quantum quasi-shuffle product on the basis. -/
def qMulB (v₁ v₂ : W) : QSym k :=
  ((qsh (wl v₁) (wl v₂)).map fun p => q ^ p.2 • M k (partWord p.1)).sum

/-- The product of `QΛ_q` (the quantum quasi-shuffle), extended bilinearly. -/
def qMul : QSym k →ₗ[k] QSym k →ₗ[k] QSym k :=
  (Finsupp.basisSingleOne).constr k fun v₁ => (Finsupp.basisSingleOne).constr k fun v₂ =>
    qMulB q v₁ v₂

theorem qMul_M (v₁ v₂ : W) : qMul q (M k v₁) (M k v₂) = qMulB q v₁ v₂ := by
  have h1 : ∀ v : W, M k v = Finsupp.basisSingleOne v := fun v => by simp [M]
  rw [qMul, h1, h1, Basis.constr_basis, Basis.constr_basis]

variable (k) in
/-- The pairing `Λ′ × QΛ_q → k`, `⟨h_α, M_β⟩ = δ_{αβ}`. -/
def pair : L k →ₗ[k] QSym k →ₗ[k] k :=
  (wordBasis k).constr k fun v => Finsupp.lapply v

theorem pair_wordBasis (v : W) (f : QSym k) : pair k (wordBasis k v) f = f v := by
  simp [pair, Basis.constr_basis]

theorem pair_wordBasis_M (v w : W) : pair k (wordBasis k v) (M k w) = if w = v then 1 else 0 := by
  rw [pair_wordBasis, M, Finsupp.single_apply]

/-- **§2.4, coproduct:** the coproduct of `Λ′` is the transpose of the quantum quasi-shuffle
product of `QΛ_q`: the coefficient of `h_{v₁} ⊗ h_{v₂}` in `Δx` is `⟨x, M_{v₁} · M_{v₂}⟩`. -/
theorem pair_coproduct (x : L k) (v₁ v₂ : W) :
    (tensorBasis k).repr (coproduct q x) (v₁, v₂) = pair k x (qMul q (M k v₁) (M k v₂)) := by
  have hlin : (Finsupp.lapply (v₁, v₂)).comp ((tensorBasis k).repr.toLinearMap.comp
      (coproduct q)) = (pair k).flip (qMul q (M k v₁) (M k v₂)) := by
    apply (wordBasis k).ext
    intro w
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      Finsupp.lapply_apply, LinearMap.flip_apply, pair_wordBasis, qMul_M, qMulB]
    rw [← hWord_wl, coproduct_hWord_list, map_list_sum, List.map_map,
      ← Finsupp.applyAddHom_apply, map_list_sum, List.map_map, ← Finsupp.applyAddHom_apply,
      map_list_sum, List.map_map]
    have hl : ((splitsAll (wl w)).map ((Finsupp.applyAddHom (v₁, v₂)) ∘ ⇑(tensorBasis k).repr ∘
        fun u => q ^ EKRest.crossL u (subL (wl w) u) • hWord k u ⊗ₜ[k] hWord k (subL (wl w) u))).sum
        = splitCoef q (wl w) (wl v₁) (wl v₂) := by
      rw [splitCoef]
      congr 1
      apply List.map_congr_left
      intro u _
      simp only [Function.comp_apply, Finsupp.applyAddHom_apply, map_smul]
      rw [← partWord_value, ← partWord_value, ← Basis.tensorProduct_apply,
        show (wordBasis k).tensorProduct (wordBasis k) = tensorBasis k from rfl, Basis.repr_self,
        Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
      by_cases h : compress u = wl v₁ ∧ compress (subL (wl w) u) = wl v₂
      · rw [if_pos h, if_pos (by rw [Prod.mk.injEq, partWord_eq_iff, partWord_eq_iff]; exact h),
          mul_one]
      · rw [if_neg h, if_neg (by rw [Prod.mk.injEq, partWord_eq_iff, partWord_eq_iff]; exact h),
          mul_zero]
    have hr : ((qsh (wl v₁) (wl v₂)).map ((Finsupp.applyAddHom w) ∘
        fun p => q ^ p.2 • M k (partWord p.1))).sum = qcoef q (wl v₁) (wl v₂) (wl w) := by
      rw [qcoef]
      congr 1
      apply List.map_congr_left
      intro p hp
      simp only [Function.comp_apply, Finsupp.applyAddHom_apply, Finsupp.smul_apply, M,
        Finsupp.single_apply, smul_eq_mul]
      have hpos := qsh_pos _ _ (wl_pos v₁) (wl_pos v₂) p hp
      have : partWord p.1 = w ↔ p.1 = wl w := by
        constructor
        · intro h; rw [← h, wl_partWord _ hpos]
        · intro h; rw [h, partWord_wl]
      by_cases h : p.1 = wl w
      · rw [if_pos (this.mpr h), if_pos h, mul_one]
      · rw [if_neg (fun h' => h (this.mp h')), if_neg h, mul_zero]
    rw [hl, hr, splitCoef_eq_qcoef q _ _ _ (wl_pos w) (wl_pos v₁) (wl_pos v₂)]
  exact LinearMap.congr_fun hlin x

/-- Deconcatenations `w = w₁ w₂` of a word. -/
def splitsW (w : W) : List (W × W) :=
  (List.range (w.toList.length + 1)).map fun i =>
    (FreeMonoid.ofList (w.toList.take i), FreeMonoid.ofList (w.toList.drop i))

theorem sum_splitsW (a b w : W) :
    ((splitsW w).map fun p => (if a = p.1 then (1 : k) else 0) * if b = p.2 then 1 else 0).sum =
      if a * b = w then 1 else 0 := by
  rw [splitsW, List.map_map, EKAppendixData.list_sum_range]
  by_cases hw : a * b = w
  · rw [if_pos hw, Finset.sum_eq_single a.toList.length]
    · subst hw
      simp [FreeMonoid.toList_mul]
    · intro i hi hia
      simp only [Function.comp_apply]
      rw [if_neg, zero_mul]
      intro h
      apply hia
      have := congrArg (fun v : W => v.toList.length) h
      simp only [FreeMonoid.toList_ofList, List.length_take] at this
      rw [Finset.mem_range] at hi
      omega
    · intro h
      exfalso; apply h
      rw [Finset.mem_range, ← hw, FreeMonoid.toList_mul, List.length_append]
      omega
  · rw [if_neg hw]
    apply Finset.sum_eq_zero
    intro i _
    simp only [Function.comp_apply]
    by_cases h1 : a = FreeMonoid.ofList (w.toList.take i)
    · by_cases h2 : b = FreeMonoid.ofList (w.toList.drop i)
      · exfalso; apply hw
        apply FreeMonoid.toList.injective
        rw [FreeMonoid.toList_mul, h1, h2, FreeMonoid.toList_ofList, FreeMonoid.toList_ofList,
          List.take_append_drop]
      · rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]

/-- **§2.4, product:** the product of `Λ′` is the transpose of the deconcatenation coproduct
of `QΛ_q`: `⟨xy, M_w⟩ = Σ_{w = w₁w₂} ⟨x, M_{w₁}⟩⟨y, M_{w₂}⟩`. -/
theorem pair_mul (x y : L k) (w : W) :
    pair k (x * y) (M k w) = ((splitsW w).map fun p => pair k x (M k p.1) * pair k y (M k p.2)).sum := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x z hx hz =>
    rw [add_mul, map_add, LinearMap.add_apply, hx, hz, ← List.sum_map_add]
    congr 1
    apply List.map_congr_left
    intro p _
    rw [map_add, LinearMap.add_apply, add_mul]
  | hb a r =>
    induction y using basis_induction k (wordBasis k) with
    | hz => simp
    | ha y z hy hz =>
      rw [mul_add, map_add, LinearMap.add_apply, hy, hz, ← List.sum_map_add]
      congr 1
      apply List.map_congr_left
      intro p _
      rw [map_add, LinearMap.add_apply, mul_add]
    | hb b t =>
      rw [smul_mul_smul_comm, ← wordBasis_mul, map_smul, LinearMap.smul_apply, pair_wordBasis_M]
      simp only [map_smul, LinearMap.smul_apply, pair_wordBasis_M, smul_eq_mul]
      rw [show ((splitsW w).map fun p => r * (if p.1 = a then (1 : k) else 0) *
          (t * if p.2 = b then 1 else 0)) =
          (splitsW w).map fun p => (r * t) * ((if a = p.1 then (1 : k) else 0) *
            if b = p.2 then 1 else 0) by
        apply List.map_congr_left; intro p _
        simp only [eq_comm (a := p.1), eq_comm (a := p.2)]; ring]
      rw [List.sum_map_mul_left, sum_splitsW]
      simp only [eq_comm (a := w)]

/-- **§2.4, unit and counit.** -/
theorem pair_one (w : W) : pair k (1 : L k) (M k w) = if w = 1 then 1 else 0 := by
  rw [← wordBasis_one, pair_wordBasis_M]

theorem pair_M_one (x : L k) : pair k x (M k 1) = counit k x := by
  induction x using basis_induction k (wordBasis k) with
  | hz => simp
  | ha x z hx hz => rw [map_add, LinearMap.add_apply, hx, hz, map_add]
  | hb v r =>
    rw [map_smul, LinearMap.smul_apply, pair_wordBasis_M, map_smul, counit_word]
    by_cases h : v = 1
    · simp [h]
    · simp [h, Ne.symm h]

/-! ## The ribbon basis: `h̃_α ↦ R̂_α` -/

section Ribbon
open EKRest

theorem blk_zero {n : ℕ} (S : Finset (Fin n)) (a : Fin n) (ha : a.val = 0) : blk S a = 0 := by
  unfold blk
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro s _ ⟨h1, h2⟩
  rw [Fin.le_def] at h2
  omega

theorem blk_step {n : ℕ} (S : Finset (Fin n)) (a b : Fin n) (hb : b.val = a.val + 1) :
    blk S b ≤ blk S a + 1 := by
  unfold blk
  calc (S.filter (fun s => 0 < s.val ∧ s ≤ b)).card
      ≤ (insert b (S.filter (fun s => 0 < s.val ∧ s ≤ a))).card := by
        apply Finset.card_le_card
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_insert] at hs ⊢
        by_cases hsb : s = b
        · left; exact hsb
        · right
          refine ⟨hs.1, hs.2.1, ?_⟩
          have h2 := hs.2.2
          rw [Fin.le_def] at h2 ⊢
          have : s.val ≠ b.val := fun e => hsb (Fin.ext e)
          omega
    _ ≤ _ := Finset.card_insert_le _ _

theorem blk_last {n : ℕ} (S : Finset (Fin n)) (a : Fin n) (ha : a.val + 1 = n) :
    blk S a = ncut S := by
  unfold blk ncut
  congr 1
  apply Finset.filter_congr
  intro s _
  have : s ≤ a := by rw [Fin.le_def]; omega
  simp [this]

theorem exists_blk {n : ℕ} (S : Finset (Fin n)) :
    ∀ (m : ℕ) (hm : m < n) (i : ℕ), i ≤ blk S ⟨m, hm⟩ → ∃ a : Fin n, blk S a = i := by
  intro m
  induction m with
  | zero =>
    intro hm i hi
    rw [blk_zero S _ rfl] at hi
    exact ⟨⟨0, hm⟩, by rw [blk_zero S _ rfl]; omega⟩
  | succ m ih =>
    intro hm i hi
    by_cases h : i ≤ blk S ⟨m, by omega⟩
    · exact ih (by omega) i h
    · have := blk_step S ⟨m, by omega⟩ ⟨m + 1, hm⟩ rfl
      exact ⟨⟨m + 1, hm⟩, by omega⟩

theorem parts_pos {n : ℕ} (hn : 0 < n) (S : Finset (Fin n)) (i : Fin (ncut S + 1)) :
    0 < EKRest.parts S i := by
  obtain ⟨a, ha⟩ := exists_blk S (n - 1) (by omega) i.val
    (by rw [blk_last S _ (by simp; omega)]; exact Nat.lt_succ_iff.mp i.isLt)
  unfold EKRest.parts
  have hb : blockMap S a = i := Fin.ext ha
  calc 0 < (if blockMap S a = i then 1 else 0) := by rw [if_pos hb]; norm_num
    _ ≤ _ := Finset.single_le_sum (f := fun a => if blockMap S a = i then 1 else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem blk_eq_of_parts {n : ℕ} (S T : Finset (Fin n))
    (h : List.ofFn (EKRest.parts S) = List.ofFn (EKRest.parts T)) (a : Fin n) : blk S a = blk T a := by
  have hs := List.ofFn_inj'.mp h
  have e1 : blk S a = (EKPlatformBijection.endpoint (EKRest.parts S) (EKRest.parts_sum S) a).val := by
    rw [endpoint_parts]; rfl
  have e2 : blk T a = (EKPlatformBijection.endpoint (EKRest.parts T) (EKRest.parts_sum T) a).val := by
    rw [endpoint_parts]; rfl
  rw [e1, e2]
  have key : ∀ (x y : Σ r, Fin r → ℕ) (hx : (∑ i, x.2 i) = n) (hy : (∑ i, y.2 i) = n),
      x = y → (EKPlatformBijection.endpoint x.2 hx a).val =
        (EKPlatformBijection.endpoint y.2 hy a).val := by
    rintro x y hx hy rfl; rfl
  exact key ⟨_, EKRest.parts S⟩ ⟨_, EKRest.parts T⟩ (EKRest.parts_sum S) (EKRest.parts_sum T) hs

theorem cut_eq_of_parts {n : ℕ} (S T : Finset (Fin n)) (hS : ∀ s ∈ S, 0 < s.val)
    (hT : ∀ s ∈ T, 0 < s.val) (h : List.ofFn (EKRest.parts S) = List.ofFn (EKRest.parts T)) : S = T := by
  ext k
  by_cases hk : k.val = 0
  · constructor
    · intro hm; have := hS k hm; omega
    · intro hm; have := hT k hm; omega
  · have hk0 : 0 < k.val := by omega
    rw [← not_iff_not, ← blockMap_pred S hk0, ← blockMap_pred T hk0]
    simp only [blockMap, Fin.mk.injEq]
    rw [blk_eq_of_parts S T h, blk_eq_of_parts S T h]

/-- The word of the composition with cut set `S`. -/
def wordOfCut {n : ℕ} (S : Finset (Fin n)) : W := partWord (List.ofFn (EKRest.parts S))

theorem hS_eq {n : ℕ} (S : Finset (Fin n)) : hS (k := k) S = wordBasis k (wordOfCut S) := by
  rw [hS, vWord, wordOfCut, partWord_value]

theorem wordOfCut_inj {n : ℕ} (S T : Finset (Fin n)) (hS : ∀ s ∈ S, 0 < s.val)
    (hT : ∀ s ∈ T, 0 < s.val) (h : wordOfCut S = wordOfCut T) : S = T := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  apply cut_eq_of_parts S T hS hT
  have hpS : ∀ a ∈ List.ofFn (EKRest.parts S), 0 < a := by
    intro a ha; rw [List.mem_ofFn] at ha; obtain ⟨i, rfl⟩ := ha; exact parts_pos hn S i
  have hpT : ∀ a ∈ List.ofFn (EKRest.parts T), 0 < a := by
    intro a ha; rw [List.mem_ofFn] at ha; obtain ⟨i, rfl⟩ := ha; exact parts_pos hn T i
  have := congrArg wl h
  rwa [wordOfCut, wordOfCut, wl_partWord _ hpS, wl_partWord _ hpT] at this

variable (k) in
/-- The ribbon (fundamental) quasi-symmetric function `R_β = Σ_{γ refines β} M_γ`, for the
composition `β` of `n` with cut set `S`. -/
def Rfund {n : ℕ} (S : Cut n) : QSym k :=
  ∑ U : Cut n, if S.1 ⊆ U.1 then M k (wordOfCut U.1) else 0

theorem pair_hS_Rfund {n : ℕ} (T : Finset (Fin n)) (hT : ∀ s ∈ T, 0 < s.val) (S' : Cut n) :
    pair k (hS (k := k) T) (Rfund k S') = if S'.1 ⊆ T then 1 else 0 := by
  rw [hS_eq, Rfund, map_sum, Finset.sum_eq_single ⟨T, hT⟩]
  · split_ifs <;> simp [pair_wordBasis_M]
  · intro U _ hU
    split_ifs
    · rw [pair_wordBasis_M, if_neg]
      intro h
      exact hU (Subtype.ext (wordOfCut_inj _ _ U.2 hT h))
    · simp
  · simp

/-- **EK §2.4: `h̃_α ↦ R̂_α`.** The basis `h̃_α` of (2.31) is dual, under `⟨·,·⟩`, to the
ribbon basis `R_β` of `QΛ_q`: `⟨h̃_α, R_β⟩ = δ_{αβ}` (compositions `α, β` of `n`, given by
their cut sets). -/
theorem pair_hT_Rfund {n : ℕ} (S S' : Cut n) :
    pair k (hT (k := k) S.1) (Rfund k S') = if S = S' then 1 else 0 := by
  rw [hT, map_sum, LinearMap.sum_apply]
  have h1 : ∀ T ∈ S.1.powerset, pair k (((-1 : ℤ) ^ (S.1.card - T.card)) • hS (k := k) T)
      (Rfund k S') = (((-1 : ℤ) ^ (S.1.card - T.card) * (if S'.1 ⊆ T then 1 else 0) : ℤ) : k) := by
    intro T hT
    rw [map_zsmul, LinearMap.smul_apply,
      pair_hS_Rfund T (fun s hs => S.2 s (Finset.mem_powerset.mp hT hs))]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl h1, ← Int.cast_sum, incl_excl]
  have : (S'.1 = S.1) ↔ (S = S') := ⟨fun h => (Subtype.ext h).symm, fun h => by rw [h]⟩
  by_cases h : S = S'
  · rw [if_pos (this.mpr h), if_pos h]; simp
  · rw [if_neg (fun h' => h (this.mp h')), if_neg h]; simp

end Ribbon

/-! ## (2.32) -/

theorem length_le_sum (β : List ℕ) (hpos : ∀ a ∈ β, 0 < a) : β.length ≤ β.sum := by
  induction β with
  | nil => simp
  | cons a β ih =>
    have h1 := hpos a (by simp)
    have h2 := ih (fun x hx => hpos x (by simp [hx]))
    simp only [List.length_cons, List.sum_cons]
    omega

/-- **EK (2.32)** (`q = -1`, in `Λ′` over `ℤ`): `e_n = (-1)^{n(n-1)/2} h̃_{(1ⁿ)}`, where by
(2.31) `h̃_{(1ⁿ)} = Σ_{β ⊨ n} (-1)^{ℓ(1ⁿ) - ℓ(β)} h_β` (every composition `β` of `n` satisfies
`β ≤ (1ⁿ)`). -/
theorem eq_2_32 (n : ℕ) :
    CompleteElementary.elementary n = (-1 : CompleteElementary.A) ^ (n.choose 2) *
      ∑ β ∈ CompleteElementary.compositions n,
        (-1 : CompleteElementary.A) ^ (n - β.length) * CompleteElementary.hWord β := by
  rw [CompleteElementary.elementary_composition_expansion, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β hβ
  have hlen : β.length ≤ n := by
    obtain ⟨hpos, hsum⟩ := (CompleteElementary.mem_compositions_iff n β).mp hβ
    rw [← hsum]
    exact length_le_sum β hpos
  rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add, Nat.choose_succ_succ', Nat.choose_one_right]
  have : n + n.choose 2 + β.length = (n.choose 2 + (n - β.length)) + 2 * β.length := by omega
  rw [this, pow_add, pow_mul]
  simp

/-! ## Summary -/

open Classical in
/-- **EK §2.4, `Λ′ ≅ NΛ_q`**, at arbitrary `q` in any commutative ring `k`.  The pairing
`⟨h_α, M_β⟩ = δ_{αβ}` between `Λ′` and `QΛ_q` is perfect on the monomial bases and
identifies `Λ′` with the graded dual `NΛ_q` of `QΛ_q` compatibly with all the structure:
1. the coproduct of `Λ′` is dual to the quantum quasi-shuffle product of `QΛ_q`;
2. the product of `Λ′` is dual to deconcatenation;
3. unit and counit correspond;
4. `h̃_α ↦ R̂_α`, the basis dual to the ribbon basis `R_α` of `QΛ_q`;
5. (2.33): `(h̃_β, h̃_α) = Σ_{C(σ) = α, C(σ⁻¹) = β} q^{ℓ(σ)}` (the form (2.30) on ribbons). -/
theorem ek_sec_2_4 :
    (∀ v w : W, pair k (wordBasis k v) (M k w) = if w = v then 1 else 0) ∧
    (∀ (x : L k) (v₁ v₂ : W),
      (tensorBasis k).repr (coproduct q x) (v₁, v₂) = pair k x (qMul q (M k v₁) (M k v₂))) ∧
    (∀ (x y : L k) (w : W), pair k (x * y) (M k w) =
      ((splitsW w).map fun p => pair k x (M k p.1) * pair k y (M k p.2)).sum) ∧
    (∀ w : W, pair k (1 : L k) (M k w) = if w = 1 then 1 else 0) ∧
    (∀ x : L k, pair k x (M k 1) = counit k x) ∧
    (∀ (n : ℕ) (S S' : EKRest.Cut n),
      pair k (EKRest.hT (k := k) S.1) (Rfund k S') = if S = S' then 1 else 0) ∧
    (∀ (n : ℕ) (S R : Finset (Fin n)), form q (EKRest.hT (k := k) S) (EKRest.hT R) =
      ∑ σ : Equiv.Perm (Fin n), if EKRest.Des σ = R ∧ EKRest.Des σ⁻¹ = S then
        q ^ EKPlatformBijection.inversions σ else 0) :=
  ⟨pair_wordBasis_M, pair_coproduct q, pair_mul, pair_one, pair_M_one,
    fun _ S S' => pair_hT_Rfund S S', fun _ S R => EKRest.eq_2_33 q S R⟩

end OddMath.Frontier.EKFinal
