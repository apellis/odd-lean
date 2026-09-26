import OddMath.Frontier.OddLRRuleRSK
import OddMath.Frontier.OddLRTableau

/-!
# Knuth equivalence: restriction, translation, and Yamanouchi words

* `knuth_filter_gt`: Knuth equivalence survives deleting all letters `≤ m`;
* `P_map_add`: insertion commutes with translating the alphabet;
* `yamanouchi_of_knuth`: the Yamanouchi property is invariant under Knuth moves
  (Fulton, *Young Tableaux*, §5.2, Lemma 1);
* `yamanouchi_readR_iff`: the row word of a tableau is Yamanouchi iff row `k` is filled
  with `k + 1` (Fulton §5.2).

Yamanouchi words are those of Ellis, arXiv:1111.3932v1, §4.1, p.12
(`OddLRTableau.Yamanouchi`).
-/

namespace OddMath.Frontier.OddLRRule

open EKClassicalPlactic OddLRTableau TableauSign

/-! ## Deleting small letters -/

theorem filter_gt_triple (m y z x : ℕ) :
    [y, z, x].filter (fun a => decide (m < a)) =
      (if m < y then [y] else []) ++ (if m < z then [z] else []) ++ (if m < x then [x] else []) := by
  simp only [List.filter_cons, List.filter_nil]
  split_ifs <;> simp_all

theorem kstep_filter_gt (m : ℕ) {w w' : List ℕ} (h : KStep w w') :
    KnuthEquiv (w.filter (fun a => decide (m < a))) (w'.filter (fun a => decide (m < a))) := by
  obtain ⟨u, v, x, y, z, ⟨h1, h2, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩⟩ := h
  · simp only [List.filter_append, filter_gt_triple]
    by_cases hx : m < x
    · refine Relation.EqvGen.rel _ _ ⟨u.filter (fun a => decide (m < a)), v.filter (fun a => decide (m < a)), x, y, z, Or.inl ⟨h1, h2, ?_, ?_⟩⟩
      · simp [hx, show m < y by omega, show m < z by omega]
      · simp [hx, show m < y by omega, show m < z by omega]
    · simp only [if_neg hx, List.append_nil, List.nil_append]
      exact knuth_refl _
  · simp only [List.filter_append, filter_gt_triple]
    by_cases hx : m < x
    · refine Relation.EqvGen.rel _ _ ⟨u.filter (fun a => decide (m < a)), v.filter (fun a => decide (m < a)), x, y, z, Or.inr ⟨h1, h2, ?_, ?_⟩⟩
      · simp [hx, show m < y by omega, show m < z by omega]
      · simp [hx, show m < y by omega, show m < z by omega]
    · simp only [if_neg hx, List.append_nil, List.nil_append]
      exact knuth_refl _

theorem knuth_filter_gt (m : ℕ) {w w' : List ℕ} (h : KnuthEquiv w w') :
    KnuthEquiv (w.filter (fun a => decide (m < a))) (w'.filter (fun a => decide (m < a))) := by
  induction h with
  | rel a b hab => exact kstep_filter_gt m hab
  | refl => exact knuth_refl _
  | symm _ _ _ ih => exact knuth_symm ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact knuth_trans ih₁ ih₂

/-! ## Translating the alphabet -/

theorem bump1_map_add (m : ℕ) : ∀ (R : List ℕ) (a : ℕ),
    bump1 (R.map (· + m)) (a + m) = ((bump1 R a).1.map (· + m), (bump1 R a).2.map (· + m))
  | [], a => rfl
  | x :: R, a => by
    by_cases h : a < x
    · simp [bump1, h]
    · have h' : ¬ a + m < x + m := by omega
      simp only [List.map_cons, bump1, h, h', if_false]
      rw [bump1_map_add m R a]

theorem ins_map_add (m : ℕ) : ∀ (rs : List (List ℕ)) (a : ℕ),
    ins (rs.map (List.map (· + m))) (a + m) = (ins rs a).map (List.map (· + m))
  | [], a => rfl
  | R :: rs, a => by
    simp only [List.map_cons, ins, bump1_map_add]
    rcases hb : (bump1 R a).2 with _ | b
    · simp
    · rw [show Option.map (fun x => x + m) (some b) = some (b + m) from rfl]
      dsimp only
      rw [ins_map_add m rs b]

theorem insW_map_add (m : ℕ) (w : List ℕ) : ∀ rs : List (List ℕ),
    insW (rs.map (List.map (· + m))) (w.map (· + m)) = (insW rs w).map (List.map (· + m)) := by
  induction w with
  | nil => intro rs; rfl
  | cons a w ih =>
    intro rs
    simp only [List.map_cons, insW_cons, ins_map_add, ih]

theorem P_map_add (m : ℕ) (w : List ℕ) : P (w.map (· + m)) = (P w).map (List.map (· + m)) :=
  insW_map_add m w []

theorem P_eq_of_map_add {m : ℕ} {w w' : List ℕ} (h : P (w.map (· + m)) = P (w'.map (· + m))) :
    P w = P w' := by
  rw [P_map_add, P_map_add] at h
  have hi : Function.Injective (List.map (List.map (· + m))) :=
    List.map_injective_iff.mpr (List.map_injective_iff.mpr (fun a b h => by simpa using h))
  exact hi h

/-! ## Yamanouchi words -/

/-- The lattice condition for one suffix. -/
def Good (t : List ℕ) : Prop := ∀ a, 0 < a → t.count (a + 1) ≤ t.count a

/-- Yamanouchi, recursively over suffixes. -/
def YamR : List ℕ → Prop
  | [] => True
  | a :: w => Good (a :: w) ∧ YamR w

theorem yamR_iff_suffix : ∀ w : List ℕ, YamR w ↔ ∀ t, t <:+ w → Good t
  | [] => by
    simp only [YamR, true_iff, List.suffix_nil]
    rintro t rfl a _
    simp
  | a :: w => by
    simp only [YamR, yamR_iff_suffix w, List.suffix_cons_iff]
    constructor
    · rintro ⟨h1, h2⟩ t (rfl | ht)
      · exact h1
      · exact h2 t ht
    · intro h
      exact ⟨h _ (Or.inl rfl), fun t ht => h t (Or.inr ht)⟩

theorem good_of_yamR : ∀ {v : List ℕ}, YamR v → Good v
  | [], _ => fun a _ => by simp
  | _ :: _, h => h.1

theorem good_iff (t : List ℕ) : Good t ↔ ∀ a b, 0 < a → a < b → t.count b ≤ t.count a := by
  constructor
  · intro h a b ha hab
    obtain ⟨d, rfl⟩ : ∃ d, b = a + 1 + d := ⟨b - (a + 1), by omega⟩
    induction d with
    | zero => exact h a ha
    | succ d ih => exact le_trans (h (a + 1 + d) (by omega)) (ih (by omega))
  · intro h a ha
    exact h a (a + 1) ha (by omega)

theorem yamanouchi_iff_yamR (w : List ℕ) : Yamanouchi w ↔ YamR w := by
  rw [yamR_iff_suffix]
  simp only [Yamanouchi, good_iff]

theorem good_perm {t t' : List ℕ} (h : t.Perm t') : Good t ↔ Good t' := by
  simp only [Good, h.count_eq]

theorem yamR_append (u v : List ℕ) :
    YamR (u ++ v) ↔ YamR v ∧ ∀ u' , u' <:+ u → u' ≠ [] → Good (u' ++ v) := by
  induction u with
  | nil =>
    simp only [List.nil_append, List.suffix_nil]
    constructor
    · intro h; exact ⟨h, fun u' hu hne => absurd hu hne⟩
    · exact fun h => h.1
  | cons a u ih =>
    simp only [List.cons_append, YamR, ih, List.suffix_cons_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h2, fun u' hu hne => ?_⟩
      rcases hu with rfl | hu
      · exact h1
      · exact h3 u' hu hne
    · rintro ⟨h2, h3⟩
      exact ⟨h3 _ (Or.inl rfl) (by simp), h2, fun u' hu hne => h3 u' (Or.inr hu) hne⟩

theorem count_cons' (a b : ℕ) (l : List ℕ) : (b :: l).count a = l.count a + if b = a then 1 else 0 := by
  rw [List.count_cons]; simp [beq_iff_eq]

/-- The three-letter core of Knuth invariance. -/
theorem yamR_core {L L' v : List ℕ} (hp : L.Perm L')
    (h3 : YamR (L ++ v) → YamR (L' ++ v)) (h3' : YamR (L' ++ v) → YamR (L ++ v)) (u : List ℕ) :
    YamR (u ++ L ++ v) ↔ YamR (u ++ L' ++ v) := by
  rw [List.append_assoc, List.append_assoc, yamR_append u (L ++ v), yamR_append u (L' ++ v)]
  have hg : ∀ u', Good (u' ++ (L ++ v)) ↔ Good (u' ++ (L' ++ v)) :=
    fun u' => good_perm ((hp.append_right v).append_left u')
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h3 h1, fun u' hu hne => (hg u').mp (h2 u' hu hne)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h3' h1, fun u' hu hne => (hg u').mpr (h2 u' hu hne)⟩

theorem kstep_yamR {w w' : List ℕ} (h : KStep w w') : YamR w ↔ YamR w' := by
  obtain ⟨u, v, x, y, z, ⟨h1, h2, rfl, rfl⟩ | ⟨h1, h2, rfl, rfl⟩⟩ := h
  · apply yamR_core (List.Perm.cons y (List.Perm.swap x z []))
    · simp only [List.cons_append, List.nil_append, YamR]
      rintro ⟨hy, hz, hx, hv⟩
      refine ⟨(good_perm (List.Perm.cons y (List.Perm.swap x z v))).mp hy,
        (good_perm (List.Perm.swap x z v)).mp hz, ?_, hv⟩
      intro a ha
      have hva := good_of_yamR hv a ha
      have hza := hz a ha
      have hya := hy a ha
      simp only [count_cons'] at hza hya ⊢
      split_ifs at hza hya ⊢ <;> omega
    · simp only [List.cons_append, List.nil_append, YamR]
      rintro ⟨hy, hx, hz, hv⟩
      refine ⟨(good_perm (List.Perm.cons y (List.Perm.swap z x v))).mp hy,
        (good_perm (List.Perm.swap z x v)).mp hx, ?_, hv⟩
      intro a ha
      have hva := good_of_yamR hv a ha
      have hxa := hx a ha
      simp only [count_cons'] at hxa ⊢
      split_ifs at hxa ⊢ <;> omega
  · apply yamR_core (List.Perm.swap z x [y])
    · simp only [List.cons_append, List.nil_append, YamR]
      rintro ⟨hx, hz, hy, hv⟩
      refine ⟨(good_perm (List.Perm.swap z x (y :: v))).mp hx, ?_, hy, hv⟩
      intro a ha
      have hxa := hx a ha
      have hya := hy a ha
      simp only [count_cons'] at hxa hya ⊢
      split_ifs at hxa hya ⊢ <;> omega
    · simp only [List.cons_append, List.nil_append, YamR]
      rintro ⟨hz, hx, hy, hv⟩
      refine ⟨(good_perm (List.Perm.swap x z (y :: v))).mp hz, ?_, hy, hv⟩
      intro a ha
      have hza := hz a ha
      have hya := hy a ha
      have hva := good_of_yamR hv a ha
      simp only [count_cons'] at hza hya hva ⊢
      split_ifs at hza hya hva ⊢ <;> omega

theorem yamR_of_knuth {w w' : List ℕ} (h : KnuthEquiv w w') : YamR w ↔ YamR w' := by
  induction h with
  | rel a b hab => exact kstep_yamR hab
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- Knuth equivalent words are simultaneously Yamanouchi (Fulton §5.2). -/
theorem yamanouchi_of_knuth {w w' : List ℕ} (h : KnuthEquiv w w') :
    Yamanouchi w ↔ Yamanouchi w' := by
  rw [yamanouchi_iff_yamR, yamanouchi_iff_yamR]
  exact yamR_of_knuth h

/-! ## Yamanouchi row words of tableaux -/

theorem readR_suffix (rs : List (List ℕ)) (k j : ℕ) (hk : k < rs.length) :
    (rowAt rs k).drop j ++ readR (rs.take k) <:+ readR rs := by
  have hsplit : rs = rs.take k ++ rowAt rs k :: rs.drop (k + 1) := by
    have h1 : rowAt rs k = rs[k] := by simp [rowAt, List.getD_eq_getElem?_getD, hk]
    rw [h1, ← List.drop_eq_getElem_cons hk, List.take_append_drop]
  have hr : readR rs = (readR (rs.drop (k + 1)) ++ (rowAt rs k).take j) ++
      ((rowAt rs k).drop j ++ readR (rs.take k)) := by
    conv_lhs => rw [hsplit]
    simp only [readR, List.reverse_append, List.reverse_cons, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
    rw [← List.append_assoc ((rowAt rs k).take j), List.take_append_drop]
  rw [hr]
  exact List.suffix_append _ _

theorem mem_readR_take {rs : List (List ℕ)} {k y : ℕ} (h : y ∈ readR (rs.take k)) :
    ∃ k' < k, y ∈ rowAt rs k' := by
  simp only [readR, List.mem_flatten, List.mem_reverse] at h
  obtain ⟨R, hR, hy⟩ := h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hR
  simp only [List.length_take] at hi
  refine ⟨i, by omega, ?_⟩
  have : i < rs.length := by omega
  simpa [rowAt, List.getD_eq_getElem?_getD, this] using hy

theorem mem_rowAt_nrows {μ : YoungDiagram} (T : PositiveTableau μ) {k y : ℕ}
    (h : y ∈ rowAt (nrows T) k) : ∃ c, (k, c) ∈ μ ∧ y = T.entry k c := by
  rw [rowAt_nrows] at h
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
  exact ⟨c, YoungDiagram.mem_iff_lt_rowLen.mpr (List.mem_range.mp hc), rfl⟩

theorem length_nrows {μ : YoungDiagram} (T : PositiveTableau μ) : (nrows T).length = μ.colLen 0 := by
  simp [nrows]

/-- A tableau with Yamanouchi row word has row `i` filled with `i + 1` (Fulton §5.2). -/
theorem canon_of_yamR {μ : YoungDiagram} (T : PositiveTableau μ) (h : YamR (readR (nrows T))) :
    ∀ i j, (i, j) ∈ μ → T.entry i j = i + 1 := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro j hij
  by_contra hne
  have hge := TableauDominance.entry_ge_row T hij
  set b := T.entry i j with hb
  have hi : i < (nrows T).length := by
    rw [length_nrows]
    exact YoungDiagram.mem_iff_lt_colLen.mp (μ.up_left_mem le_rfl (Nat.zero_le j) hij)
  have hsuf := readR_suffix (nrows T) i j hi
  have hg := (yamR_iff_suffix _).mp h _ hsuf (b - 1) (by omega)
  have hj : j < μ.rowLen i := YoungDiagram.mem_iff_lt_rowLen.mp hij
  have hzero : ((rowAt (nrows T) i).drop j ++ readR ((nrows T).take i)).count (b - 1) = 0 := by
    apply List.count_eq_zero_of_not_mem
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · rw [rowAt_nrows, List.mem_drop_iff_getElem] at hm
      obtain ⟨c, hc, hce⟩ := hm
      simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range] at hc hce
      have hw : T.entry i j ≤ T.entry i (j + c) := by
        rcases Nat.eq_zero_or_pos c with rfl | hc0
        · simp
        · exact T.row_weak' (by omega) (YoungDiagram.mem_iff_lt_rowLen.mpr (by omega))
      omega
    · obtain ⟨k', hk', hmk⟩ := mem_readR_take hm
      obtain ⟨c, hc, he⟩ := mem_rowAt_nrows T hmk
      have := ih k' hk' c hc
      omega
  have hpos : 0 < ((rowAt (nrows T) i).drop j ++ readR ((nrows T).take i)).count b := by
    apply List.count_pos_iff.mpr
    apply List.mem_append_left
    rw [rowAt_nrows, List.mem_drop_iff_getElem]
    exact ⟨0, by simp; omega, by simp [hb]⟩
  rw [show b - 1 + 1 = b by omega] at hg
  omega

/-- Rows of lengths `ℓ 0, ℓ 1, …`, row `k` filled with `k + 1`. -/
def canonRows (ℓ : ℕ → ℕ) (n : ℕ) : List (List ℕ) :=
  (List.range n).map (fun k => List.replicate (ℓ k) (k + 1))

theorem readR_canonRows_succ (ℓ : ℕ → ℕ) (n : ℕ) :
    readR (canonRows ℓ (n + 1)) = List.replicate (ℓ n) (n + 1) ++ readR (canonRows ℓ n) := by
  simp [canonRows, readR, List.range_succ]

theorem count_readR_canonRows (ℓ : ℕ → ℕ) (a : ℕ) : ∀ n,
    (readR (canonRows ℓ n)).count a = if 0 < a ∧ a ≤ n then ℓ (a - 1) else 0
  | 0 => by
    rw [if_neg (by omega)]
    simp [canonRows, readR]
  | n + 1 => by
    have hc : (List.replicate (ℓ n) (n + 1)).count a = if a = n + 1 then ℓ n else 0 := by
      split_ifs with h
      · subst h; simp
      · exact List.count_eq_zero_of_not_mem (fun hm => h (List.eq_of_mem_replicate hm))
    rw [readR_canonRows_succ, List.count_append, count_readR_canonRows ℓ a n, hc]
    split_ifs <;> first | omega | (subst_vars; simp)

theorem yamR_canonRows (ℓ : ℕ → ℕ) (hℓ : Antitone ℓ) : ∀ n, YamR (readR (canonRows ℓ n))
  | 0 => by simp [canonRows, readR, YamR]
  | n + 1 => by
    rw [readR_canonRows_succ, yamR_append]
    refine ⟨yamR_canonRows ℓ hℓ n, fun u' hu _ a ha => ?_⟩
    have hsub := hu.subset
    have hlen := hu.length_le
    have hcu : ∀ b, u'.count b = if b = n + 1 then u'.length else 0 := by
      intro b
      split_ifs with hb
      · subst hb
        exact List.count_eq_length.mpr (fun y hy => by
          have := hsub hy; rw [List.eq_of_mem_replicate this])
      · exact List.count_eq_zero_of_not_mem (fun hm => hb (by
          have := hsub hm; rw [List.eq_of_mem_replicate this]))
    simp only [List.length_replicate] at hlen
    rw [List.count_append, List.count_append, hcu, hcu, count_readR_canonRows,
      count_readR_canonRows, Nat.add_sub_cancel]
    have h1 := hℓ (show a - 1 ≤ a from by omega)
    rcases le_or_lt (a - 1) n with h2 | h2
    · have h3 := hℓ h2
      split_ifs <;> omega
    · split_ifs <;> omega

theorem nrows_canonical (μ : YoungDiagram) :
    nrows (TableauDominance.canonicalTableau μ) = canonRows μ.rowLen (μ.colLen 0) := by
  unfold nrows canonRows
  apply List.map_congr_left
  intro k _
  rw [List.eq_replicate_iff]
  refine ⟨by simp, fun y hy => ?_⟩
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
  exact TableauDominance.canonical_entry (p := (k, c))
    (by simpa using YoungDiagram.mem_iff_lt_rowLen.mpr (List.mem_range.mp hc))

theorem yamR_nrows_iff {μ : YoungDiagram} (T : PositiveTableau μ) :
    YamR (readR (nrows T)) ↔ T = TableauDominance.canonicalTableau μ := by
  constructor
  · intro h
    apply TableauContent.ext_cells
    intro p hp
    rw [canon_of_yamR T h p.1 p.2 (by simpa using hp), TableauDominance.canonical_entry hp]
  · rintro rfl
    rw [nrows_canonical]
    exact yamR_canonRows _ (fun a b h => μ.rowLen_anti a b h) _

end OddMath.Frontier.OddLRRule
