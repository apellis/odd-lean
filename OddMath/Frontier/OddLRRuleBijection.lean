import OddMath.Frontier.OddLRRulePieri

/-!
# The Littlewood–Richardson correspondence with odd signs

Ellis, arXiv:1111.3932v1, proof of Theorem 4.8, pp.14–15 (after Fulton, *Young Tableaux*, §5.2).
For a skew tableau `S` of shape `λ/μ` (letters `≤ r`), let `A` be the matrix with
`RSK(A) = (T_λ, T_S)`, split into its first `ℓ(μ)` rows `U` and its last `r` rows `V`
(E: `(Tλ, TS) ↔ (x t / u v)`, `(U, U₀) ↔ (x/t)`). We prove:

* `nrows_QV`: the recording tableau of `V` is the insertion tableau of `w_r(S)`
  (Fulton §5.1; by the Symmetry Theorem);
* `sign_eq_kappa`: `(-1)^{N^<(Ŝ)} = κ(U, P(V)) · sign(Q(V))`, from the odd RSK sign
  (EK Thm 3.7 (3.8); E (4.8)–(4.9));
* `key_inj`, `key_replace`: `S ↦ (U, P(V), Q(V))` is injective, and `Q(V)` may be replaced by any
  tableau of the same shape;
* `isLR_iff_QV`: `S` is a Littlewood–Richardson tableau iff `Q(V) = T_ν`.
-/

namespace OddMath.Frontier.OddLRRule

open TableauSign TableauEvaluation TableauContent OddLRTableau EKClassicalPlactic
open EKRskBijection (Pairs Tab rskRec)
open scoped BigOperators

/-! ## Column words of stacked and transposed matrices -/

theorem colword_join {m C : ℕ} (U : Fin m → Fin C → ℕ) : ∀ (r : ℕ) (V : Fin r → Fin C → ℕ),
    colword (EKPairingMatrices.join U V) = colword U ++ colword V
  | 0, V => by rw [join_zero, colword_zero, List.append_nil]
  | r + 1, V => by
    rw [colword_succ (R := m + r) (EKPairingMatrices.join (r := m) (s := r + 1) U V), join_init,
      join_last, colword_join U r (Fin.init V), colword_succ V, List.append_assoc]

theorem word_congr' {B B' : ℕ → ℕ → ℕ} {i j : ℕ}
    (h : ∀ p, 0 < p → p ≤ i → ∀ q, 0 < q → q ≤ j → B p q = B' p q) :
    word B i j = word B' i j := by
  unfold word
  apply List.flatMap_congr
  intro p hp
  have hp' := List.mem_range.mp hp
  unfold rowW
  apply List.flatMap_congr
  intro q hq
  rw [h (p + 1) (by omega) (by omega) (q + 1) (by omega) (by have := List.mem_range.mp hq; omega)]

theorem rowW_filter_gt (X : ℕ → ℕ → ℕ) (m p : ℕ) : ∀ r,
    (rowW X p (m + r)).filter (fun a => decide (m < a)) =
      (rowW (fun p q => X p (q + m)) p r).map (· + m)
  | 0 => by
    rw [List.filter_eq_nil_iff.mpr (fun a ha => by have := (mem_rowW ha).2; simp; omega)]
    simp [rowW]
  | r + 1 => by
    rw [show m + (r + 1) = (m + r) + 1 by omega, rowW_succ, List.filter_append,
      rowW_filter_gt X m p r, rowW_succ, List.map_append,
      List.filter_eq_self.mpr (fun a ha => by rw [List.eq_of_mem_replicate ha]; simp; omega),
      List.map_replicate, show r + 1 + m = m + r + 1 by omega]

theorem word_filter_gt (X : ℕ → ℕ → ℕ) (m i r : ℕ) :
    (word X i (m + r)).filter (fun a => decide (m < a)) =
      (word (fun p q => X p (q + m)) i r).map (· + m) := by
  unfold word
  rw [List.filter_flatMap, List.map_flatMap]
  apply List.flatMap_congr
  intro p _
  exact rowW_filter_gt X m (p + 1) r

theorem colword_transpose_filter {m r C : ℕ} (U : Fin m → Fin C → ℕ) (V : Fin r → Fin C → ℕ) :
    (colword (fun j i => EKPairingMatrices.join U V i j)).filter (fun a => decide (m < a)) =
      (colword (fun j i => V i j)).map (· + m) := by
  rw [colword_eq_word, colword_eq_word, word_filter_gt]
  congr 1
  apply word_congr'
  intro p hp hpC q hq hqr
  simp only [ext_transpose]
  simp only [ext]
  rw [dif_pos (by omega), dif_pos (by omega)]
  have : (⟨q + m - 1, by omega⟩ : Fin (m + r)) = Fin.natAdd m ⟨q - 1, by omega⟩ := by
    ext; simp; omega
  rw [this, EKPairingMatrices.join_right]

/-! ## The objects attached to a skew tableau -/

variable (lam mu : YoungDiagram) (r : ℕ)

/-- Skew tableaux of shape `λ/μ` with letters `≤ r`. -/
abbrev SkR := {S : SkewTableau lam mu // ∀ i j, S.entry i j ≤ r}

theorem canonical_inAlphabet (lam : YoungDiagram) :
    InAlphabet (lam.colLen 0) (TableauDominance.canonicalTableau lam) := by
  intro p hp
  rw [TableauDominance.canonical_entry hp]
  exact row_lt_colLen (show (p.1, p.2) ∈ lam from by simpa using hp)

variable {lam mu r}

/-- `(T_λ, T_S)` as an RSK pair. -/
noncomputable def pairOf (S : SkR lam mu r) : Pairs (lam.colLen 0) (mu.colLen 0 + r) :=
  ⟨lam, ⟨TableauDominance.canonicalTableau lam, canonical_inAlphabet lam⟩,
    ⟨toFull S.1, inAlphabet_toFull S.1 S.2⟩⟩

/-- RSK as an equivalence. -/
noncomputable def rskE (C R : ℕ) : (Fin R → Fin C → ℕ) ≃ Pairs C R :=
  Equiv.ofBijective _ (EKRskBijection.rskRec_bijective C R)

/-- The matrix `A` with `RSK(A) = (T_λ, T_S)`. -/
noncomputable def matA (S : SkR lam mu r) : Fin (mu.colLen 0 + r) → Fin (lam.colLen 0) → ℕ :=
  (rskE _ _).symm (pairOf S)

theorem rsk_matA (S : SkR lam mu r) :
    rskRec (lam.colLen 0) (mu.colLen 0 + r) (matA S) = pairOf S :=
  (rskE _ _).apply_symm_apply _

/-- Upper block `U` (labels of `T_μ`). -/
noncomputable def matU (S : SkR lam mu r) : Fin (mu.colLen 0) → Fin (lam.colLen 0) → ℕ :=
  fun i => matA S (Fin.castAdd r i)

/-- Lower block `V` (labels of `S`). -/
noncomputable def matV (S : SkR lam mu r) : Fin r → Fin (lam.colLen 0) → ℕ :=
  fun i => matA S (Fin.natAdd (mu.colLen 0) i)

theorem join_UV (S : SkR lam mu r) : EKPairingMatrices.join (matU S) (matV S) = matA S := by
  funext i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · rw [EKPairingMatrices.join_left]; rfl
  · rw [EKPairingMatrices.join_right]; rfl

/-- RSK of `V`. -/
noncomputable def zV (S : SkR lam mu r) : Pairs (lam.colLen 0) r := rskRec _ r (matV S)

/-- Recording tableau `Q(V)` (as a sigma-tableau). -/
noncomputable def QV (S : SkR lam mu r) : Σ ν : YoungDiagram, PositiveTableau ν :=
  ⟨(zV S).1, (zV S).2.2.1⟩

/-- The key `(U, P(V))`. -/
noncomputable def key (S : SkR lam mu r) :
    (Fin (mu.colLen 0) → Fin (lam.colLen 0) → ℕ) × (Σ ν : YoungDiagram, PositiveTableau ν) :=
  (matU S, ⟨(zV S).1, (zV S).2.1.1⟩)

/-! ## `Q(V) = P(w_r(S))` -/

theorem nrows_QV (S : SkR lam mu r) : nrows (zV S).2.2.1 = P S.1.rowWord := by
  have hA := rsk_matA S
  have hsym := nrows_rskP_transpose (matA S)
  rw [hA] at hsym
  change nrows (rskRec _ _ fun j i => matA S i j).2.1.1 = nrows (toFull S.1) at hsym
  rw [nrows_rskP] at hsym
  have hk := knuth_readR_P (colword fun j i => matA S i j)
  rw [hsym, ← rowWord_eq_readR_nrows] at hk
  have hf := knuth_filter_gt (mu.colLen 0) hk
  rw [rowWord_toFull_filter] at hf
  have e := colword_transpose_filter (matU S) (matV S)
  rw [join_UV S] at e
  rw [e] at hf
  have hP := P_eq_of_map_add (P_eq_of_knuth hf)
  rw [← hP, ← nrows_rskP r (lam.colLen 0) (fun j i => matV S i j)]
  exact (nrows_rskP_transpose (matV S)).symm

/-! ## Signs -/

theorem crossL_perm (xs : List ℕ) {ys ys' : List ℕ} (h : ys.Perm ys') :
    EKRskSign.crossL xs ys = EKRskSign.crossL xs ys' := by
  unfold EKRskSign.crossL
  congr 1
  apply List.map_congr_left
  intro x _
  exact (h.filter _).length_eq

variable (lam mu) in
/-- The sign factor `κ(U, P(V))`. -/
noncomputable def kappa
    (k : (Fin (mu.colLen 0) → Fin (lam.colLen 0) → ℕ) × (Σ ν : YoungDiagram, PositiveTableau ν)) :
    ℤ :=
  (-1 : ℤ) ^ (TableauStripSigns.north mu + TableauRowWord.inversions (colword k.1) +
    EKRskSign.crossL (colword k.1) (readR (nrows k.2.2)) + EKRskSign.shapeExp k.2.1 +
    EKRskSign.shapeExp lam) *
    TableauDominance.tableauSign (TableauDominance.canonicalTableau lam) *
    TableauDominance.tableauSign k.2.2

/-- `(-1)^{N^<(Ŝ)} = κ(U, P(V)) sign(Q(V))` (E (4.8)–(4.9)). -/
theorem sign_eq_kappa (S : SkR lam mu r) :
    S.1.sign = kappa lam mu (key S) * TableauDominance.tableauSign (zV S).2.2.1 := by
  have hA := rsk_sign (matA S)
  rw [rsk_matA] at hA
  change _ = _ * TableauDominance.tableauSign (TableauDominance.canonicalTableau lam) *
    TableauDominance.tableauSign (toFull S.1) at hA
  rw [tableauSign_toFull, ← join_UV S, colword_join, EKRskSign.inversions_append] at hA
  have hV := rsk_sign (matV S)
  have hcl : EKRskSign.crossL (colword (matU S)) (colword (matV S)) =
      EKRskSign.crossL (colword (matU S)) (readR (nrows (zV S).2.1.1)) := by
    apply crossL_perm
    rw [show zV S = rskRec _ r (matV S) from rfl, nrows_rskP]
    exact perm_of_knuth (knuth_readR_P _)
  rw [hcl, show (pairOf S).1 = lam from rfl] at hA
  unfold kappa key
  dsimp only
  unfold SkewTableau.sign TableauDominance.tableauSign at *
  change (-1 : ℤ) ^ _ = _ * (-1 : ℤ) ^ _ * (-1 : ℤ) ^ _ * (-1 : ℤ) ^ _
  simp only [← pow_add] at hA hV ⊢
  rw [EKRskSign.neg_one_pow_eq_iff] at hA hV ⊢
  rw [show zV S = rskRec _ r (matV S) from rfl] at hA ⊢
  omega

/-! ## Injectivity and replacement -/

theorem state_eq_of_sigma {n : ℕ} {μ μ' : YoungDiagram} {T : PositiveTableau μ}
    {T' : PositiveTableau μ'} (hT : InAlphabet n T) (hT' : InAlphabet n T')
    (h : (⟨μ, T⟩ : Σ μ : YoungDiagram, PositiveTableau μ) = ⟨μ', T'⟩) :
    (⟨μ, ⟨T, hT⟩⟩ : TableauWordInsertion.State n) = ⟨μ', ⟨T', hT'⟩⟩ := by
  cases h; rfl

theorem pairs_eq {n m : ℕ} {z w : Pairs n m}
    (hp : (⟨z.1, z.2.1.1⟩ : Σ μ : YoungDiagram, PositiveTableau μ) = ⟨w.1, w.2.1.1⟩)
    (hq : (⟨z.1, z.2.2.1⟩ : Σ μ : YoungDiagram, PositiveTableau μ) = ⟨w.1, w.2.2.1⟩) : z = w :=
  EKRskBijection.pairs_ext (state_eq_of_sigma z.2.1.2 w.2.1.2 hp)
    (state_eq_of_sigma z.2.2.2 w.2.2.2 hq)

theorem toFull_eq_of_pairOf {S S' : SkR lam mu r} (h : pairOf S = pairOf S') :
    toFull S.1 = toFull S'.1 := by
  unfold pairOf at h
  simp only [Sigma.mk.injEq, heq_eq_eq, Prod.mk.injEq, true_and] at h
  exact congrArg Subtype.val h

theorem key_inj {S S' : SkR lam mu r} (hk : key S = key S') (hq : QV S = QV S') : S = S' := by
  simp only [key, Prod.mk.injEq] at hk
  obtain ⟨hU, hP⟩ := hk
  have hz : zV S = zV S' := pairs_eq hP hq
  have hV : matV S = matV S' := (EKRskBijection.rskRec_bijective _ r).1 hz
  have hA : matA S = matA S' := by rw [← join_UV S, ← join_UV S', hU, hV]
  have hp : pairOf S = pairOf S' := by rw [← rsk_matA S, ← rsk_matA S', hA]
  exact Subtype.ext (toFull_injective (toFull_eq_of_pairOf hp))

theorem insW_congr {X : List (List ℕ)} (hX : Valid X) {w w' : List ℕ} (h : P w = P w') :
    insW X w = insW X w' := by
  rw [← P_readR X hX, ← P_append, ← P_append]
  apply P_eq_of_knuth
  have hk : KnuthEquiv w w' :=
    knuth_trans (knuth_readR_P w) (by rw [h]; exact knuth_symm (knuth_readR_P w'))
  simpa using knuth_context hk (readR X) []

/-- The upper block records `T_μ`. -/
theorem rskU_shape (S : SkR lam mu r) :
    (rskRec (lam.colLen 0) (mu.colLen 0) (matU S)).1 = mu ∧
      ∀ p ∈ mu.cells, (rskRec (lam.colLen 0) (mu.colLen 0) (matU S)).2.2.1.entry p.1 p.2 = p.1 + 1 := by
  set z0 := rskRec (lam.colLen 0) (mu.colLen 0) (matU S)
  have hj := rskRec_join (matU S) r (matV S)
  rw [join_UV S, rsk_matA] at hj
  obtain ⟨h1, h2, h3⟩ := rskFrom_Q (lam.colLen 0) (mu.colLen 0) z0 r (matV S)
  rw [← hj] at h1 h2 h3
  change z0.1.cells ⊆ lam.cells at h1
  change ∀ p ∈ z0.1.cells, (toFull S.1).entry p.1 p.2 = z0.2.2.1.entry p.1 p.2 at h2
  change ∀ p ∈ lam.cells, p ∉ z0.1.cells → mu.colLen 0 < (toFull S.1).entry p.1 p.2 at h3
  have hb := z0.2.2.2
  have hcells : z0.1.cells = mu.cells := by
    ext p
    constructor
    · intro hp
      by_contra hm
      have := toFull_entry_skew S.1 (by simpa using h1 hp) (by simpa using hm)
      have h2p := h2 p hp
      have hbp := hb p hp
      have := S.1.positive (by simpa using h1 hp) (by simpa using hm)
      omega
    · intro hp
      by_contra hz
      have hpl : p ∈ lam.cells := by simpa using mem_of_le S.1.sub (by simpa using hp)
      have := h3 p hpl hz
      rw [toFull_entry_mu S.1 (by simpa using hp)] at this
      have := row_lt_colLen (show (p.1, p.2) ∈ mu from by simpa using hp)
      omega
  refine ⟨YoungDiagram.ext hcells, fun p hp => ?_⟩
  rw [← h2 p (by rw [hcells]; exact hp), toFull_entry_mu S.1 (by simpa using hp)]

theorem key_replace (S : SkR lam mu r) (Q : PositiveTableau (zV S).1) (hQ : InAlphabet r Q) :
    ∃ S' : SkR lam mu r, key S' = key S ∧ QV S' = ⟨(zV S).1, Q⟩ := by
  set L := lam.colLen 0
  set m := mu.colLen 0
  set z0 := rskRec L m (matU S)
  let z' : Pairs L r := ⟨(zV S).1, (zV S).2.1, ⟨Q, hQ⟩⟩
  let V' := (rskE L r).symm z'
  have hV' : rskRec L r V' = z' := (rskE L r).apply_symm_apply z'
  let A' := EKPairingMatrices.join (matU S) V'
  have hj' := rskRec_join (matU S) r V'
  have hj := rskRec_join (matU S) r (matV S)
  rw [join_UV S, rsk_matA] at hj
  obtain ⟨hz0, hz0e⟩ := rskU_shape S
  -- the insertion tableau is unchanged
  have hPw : P (colword V') = P (colword (matV S)) := by
    rw [← nrows_rskP, ← nrows_rskP, hV']
    rfl
  have hP : nrows (rskRec L (m + r) A').2.1.1 = nrows (TableauDominance.canonicalTableau lam) := by
    rw [hj', nrows_rskFrom, insW_congr (nrows_valid _) hPw, ← nrows_rskFrom, ← hj]
    rfl
  have hsig := sigma_eq_of_nrows _ _ hP
  have hsh : (rskRec L (m + r) A').1 = lam := congrArg Sigma.fst hsig
  -- the recording tableau restricts to `T_μ`
  obtain ⟨h1, h2, h3⟩ := rskFrom_Q L m z0 r V'
  rw [← hj'] at h1 h2 h3
  have hbd := (rskRec L (m + r) A').2.2.2
  generalize hy : rskRec L (m + r) A' = y at hsig hsh h1 h2 h3 hbd
  obtain ⟨la, ⟨P', hP'⟩, ⟨Q', hQ'⟩⟩ := y
  dsimp only at hsig hsh h1 h2 h3 hbd
  subst hsh
  have hPeq : P' = TableauDominance.canonicalTableau la := by
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hsig
    exact hsig
  subst hPeq
  rw [hz0] at h1 h3
  have hfull : FullCond mu Q' := by
    refine ⟨YoungDiagram.cells_subset_iff.mp h1, fun i j h => ?_, fun i j h h' => ?_⟩
    · have hm : (i, j) ∈ z0.1.cells := by
        change (i, j) ∈ (rskRec (la.colLen 0) (mu.colLen 0) (matU S)).1.cells
        rw [hz0]; simpa using h
      have := h2 (i, j) hm
      rw [hz0e (i, j) (by simpa using h)] at this
      exact this
    · exact h3 (i, j) (by simpa using h) (by simpa using h')
  let S' : SkR la mu r := ⟨fromFull Q' hfull, fun i j => by
    change (if (i, j) ∈ la ∧ (i, j) ∉ mu then Q'.entry i j - m else 0) ≤ r
    split_ifs with hc
    · have h' : Q'.entry i j ≤ m + r := hbd (i, j) (by simpa using hc.1)
      omega
    · omega⟩
  have hpair : pairOf S' = rskRec L (m + r) A' := by
    rw [hy]
    unfold pairOf
    congr 3
    exact toFull_fromFull Q' hfull
  have hAeq : matA S' = A' := (rskE L (m + r)).injective (by
    change rskRec _ _ (matA S') = rskRec _ _ A'
    rw [rsk_matA, hpair])
  have hU : matU S' = matU S := by
    funext i
    change matA S' (Fin.castAdd r i) = _
    rw [hAeq]
    exact EKPairingMatrices.join_left _ _ _
  have hV : matV S' = V' := by
    funext i
    change matA S' (Fin.natAdd m i) = _
    rw [hAeq]
    exact EKPairingMatrices.join_right _ _ _
  have hz : zV S' = z' := by
    change rskRec _ r (matV S') = z'
    rw [hV, hV']
  refine ⟨S', ?_, ?_⟩
  · rw [show key S' = (matU S', ⟨(zV S').1, (zV S').2.1.1⟩) from rfl, hU, hz]
    rfl
  · rw [show QV S' = ⟨(zV S').1, (zV S').2.2.1⟩ from rfl, hz]

/-! ## Contents and the Littlewood–Richardson condition -/

theorem skew_content_eq_count (S : SkewTableau lam mu) (k : ℕ) :
    S.content k = S.rowWord.count k := by
  classical
  rw [SkewTableau.content_apply]
  simp only [SkewTableau.rowWord, List.count_eq_countP, List.countP_map,
    List.countP_eq_length_filter]
  let l := ((TableauRowWord.rowCells lam).filter (fun p => p ∉ mu.cells)).filter
    (fun p => S.entry p.1 p.2 == k)
  have hn : l.Nodup := ((TableauRowWord.rowCells_nodup lam).filter _).filter _
  have he : l.toFinset = (skewCells lam mu).filter (fun p => S.entry p.1 p.2 = k) := by
    ext p
    simp only [l, List.mem_toFinset, List.mem_filter, TableauRowWord.mem_rowCells,
      Finset.mem_filter, mem_skewCells, YoungDiagram.mem_cells, decide_eq_true_eq, beq_iff_eq]
  rw [List.filter_map, List.length_map]
  change _ = l.length
  rw [← List.toFinset_card_of_nodup hn, he]

theorem content_QV (S : SkR lam mu r) : content (zV S).2.2.1 = S.1.content := by
  ext k
  rw [← TableauRowWord.rowWord_count, rowWord_eq_readR_nrows, nrows_QV,
    skew_content_eq_count, (perm_of_knuth (knuth_readR_P S.1.rowWord)).symm.count_eq]

theorem shapeContent_succ (ν : YoungDiagram) (i : ℕ) :
    TableauDominance.shapeContent ν (i + 1) = ν.rowLen i := by
  classical
  simp only [TableauDominance.shapeContent, Finsupp.finset_sum_apply, Finsupp.single_apply,
    Finset.sum_boole, Nat.cast_id]
  have : ν.cells.filter (fun p => p.1 + 1 = i + 1) =
      (Finset.range (ν.rowLen i)).image (fun j => (i, j)) := by
    ext p
    simp only [Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hp, he⟩
      have hi : p.1 = i := by omega
      refine ⟨p.2, YoungDiagram.mem_iff_lt_rowLen.mp ?_, by ext <;> simp [hi]⟩
      rw [← hi]; exact hp
    · rintro ⟨j, hj, rfl⟩
      exact ⟨YoungDiagram.mem_iff_lt_rowLen.mpr hj, rfl⟩
  rw [this, Finset.card_image_of_injective _ (fun a b h => by simpa using h), Finset.card_range]

theorem shapeContent_injective {κ ν : YoungDiagram}
    (h : TableauDominance.shapeContent κ = TableauDominance.shapeContent ν) : κ = ν := by
  apply YoungDiagram.ext
  ext p
  have := congrArg (fun f => f (p.1 + 1)) h
  simp only [shapeContent_succ] at this
  simp only [YoungDiagram.mem_cells]
  rw [YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_rowLen, this]

/-- `S` is a Littlewood–Richardson tableau iff `Q(V) = T_ν` (Fulton §5.2). -/
theorem isLR_iff_QV (S : SkR lam mu r) (ν : YoungDiagram)
    (hc : S.1.content = TableauDominance.shapeContent ν) :
    IsLR S.1 ↔ QV S = ⟨ν, TableauDominance.canonicalTableau ν⟩ := by
  unfold IsLR
  rw [yamanouchi_iff_yamR, yamR_of_knuth (knuth_readR_P _), ← nrows_QV, yamR_nrows_iff]
  constructor
  · intro h
    have hsh : (zV S).1 = ν := by
      apply shapeContent_injective
      rw [← TableauDominance.content_canonical, ← h, content_QV, hc]
    unfold QV
    generalize (zV S).2.2.1 = Q at h
    subst hsh
    rw [h]
  · intro h
    unfold QV at h
    have hsh : (zV S).1 = ν := congrArg Sigma.fst h
    generalize (zV S).2.2.1 = Q at h
    subst hsh
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
    exact h

end OddMath.Frontier.OddLRRule
