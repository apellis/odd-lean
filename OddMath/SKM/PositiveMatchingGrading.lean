import OddMath.SKM.PositiveMatchingLayers
import OddMath.SKM.Grading

/-!
# Degree and parity of positive reduced matchings

The crossing contribution in [BE2, arXiv:1701.04133v2, Theorem 10.3, proof of Claim 1],
using reducedness from §8 and the generator degree table after (1.31).
`positive_matching_degree_parity` computes the existing diagram degree and extended-layer
parity, not a separately defined inversion grading. Its representative has exactly `tLay` as
its extended layers.

Crossings are enumerated by unordered strand ids, retaining their bottom colours, and then
by inversions of the physical left-to-right bottom-to-top endpoint permutation. This uses
neither finiteness nor decidable equality of the colour type. Repeated colours remain distinct
strands. All auxiliary weighted sums are internal to this computation.

The statement is about syntactic diagram degrees. It does not assert a quotient grading
without the usual homogeneity hypotheses, nor prove dot-series or algebraic-form identities.
-/

namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators

private theorem crossing_prefix {I : Type*} {k : ℕ} (R : List (TMove (Letter I)))
    (T : TState (Letter I)) (hf : TFits flipL k T R)
    (hc : ∀ m ∈ R, ∃ p, m = TMove.mv (Move.cross p)) :
    ∀ i < k, idAt (tRun flipL k T R).st i = idAt T.st i := by
  induction R generalizing T with
  | nil => intro i hi; rfl
  | cons m R ih =>
    obtain ⟨p, rfl⟩ := hc m List.mem_cons_self
    intro i hi
    rw [show tRun flipL k T (.mv (.cross p) :: R) =
      tRun flipL k (tStep flipL k T (.mv (.cross p))) R from rfl]
    rw [ih _ hf.2 (fun m hm => hc m (List.mem_cons_of_mem _ hm)) i hi]
    exact (idAt_swapAt hf.1 i).trans (by rw [tau_of_ne (by omega) (by omega)])

private def strandId {n : ℕ} (r : Fin n) : ℕ := 2 * (n - 1 - r.val)

private theorem strandId_injective {n : ℕ} : Function.Injective (@strandId n) := by
  intro r s h
  apply Fin.ext
  have := r.isLt
  have := s.isLt
  dsimp [strandId] at h
  omega

private theorem start_bottom_id {I : Type*} {n : ℕ} (a : Fin n → I) (r : Fin n) :
    idAt (tStart (List.ofFn fun r => (true, a r))).st (n - 1 - r.val) =
      some (strandId r) := by
  have hi : n - 1 - r.val < n := by omega
  simp only [tStart, run_cupMoves, idAt]
  rw [List.getElem?_append_left (by simpa [length_dualW] using hi)]
  simp [cupLeft, hi, strandId, dualW]
  omega

private theorem crossing_mem_iff {α : Type*} {T : TState α} (ht : TInv T)
    (hn : T.xs.Nodup) {x y : ℕ} (hxy : x ≠ y) :
    s(x, y) ∈ T.xs ↔ Ilv2 T.st x y := by
  rw [ht.parity x y hxy]
  constructor
  · intro h
    rw [List.count_eq_one_of_mem hn h]
    decide
  · intro h
    by_contra hh
    rw [List.count_eq_zero.mpr hh] at h
    exact (by decide : ¬ Odd (0 : ℕ)) h

private theorem endpoint_inversion {α : Type*} {n : ℕ} {T : TState α}
    (e : Equiv.Perm (Fin n))
    (ha : ∀ r, ArcAt T.st (strandId r) (n - 1 - r.val) (n + (e r).val))
    {r s : Fin n} (hrs : r < s) :
    Ilv2 T.st (strandId r) (strandId s) ↔ e s < e r := by
  rw [ilv2_iff_btw (ha r) (ha s) (fun h => (ne_of_lt hrs) (strandId_injective h))]
  have hr := r.isLt
  have hs := s.isLt
  have he := (e r).isLt
  have he' := (e s).isLt
  have hne := e.injective.ne (ne_of_lt hrs)
  change r.val < s.val at hrs
  change (Btw (n - 1 - r.val) (n + (e r).val) (n - 1 - s.val) ↔
    ¬ Btw (n - 1 - r.val) (n + (e r).val) (n + (e s).val)) ↔
      (e s).val < (e r).val
  have hne' : (e r).val ≠ (e s).val := fun h => hne (Fin.ext h)
  simp only [Btw]
  omega

private theorem endpoint_id_coverage {α : Type*} {n : ℕ} {T : TState α}
    (e : Equiv.Perm (Fin n)) (hlen : T.st.length = n + n)
    (ha : ∀ r, ArcAt T.st (strandId r) (n - 1 - r.val) (n + (e r).val)) :
    ∀ i < T.st.length, ∃ r : Fin n, idAt T.st i = some (strandId r) := by
  intro i hi
  by_cases hin : i < n
  · let r : Fin n := ⟨n - 1 - i, by omega⟩
    refine ⟨r, ?_⟩
    have h := (ha r).id
    have he : n - 1 - r.val = i := by dsimp [r]; omega
    rwa [he] at h
  · let s : Fin n := ⟨i - n, by omega⟩
    refine ⟨e.symm s, ?_⟩
    have h := (ha (e.symm s)).id'
    simpa [s, Nat.add_sub_of_le (by omega : n ≤ i)] using h

private theorem weighted_crossings {α M : Type*} [AddCommMonoid M]
    {n : ℕ} {T : TState α} (ht : TInv T) (hn : T.xs.Nodup)
    (hd : ∀ z ∈ T.xs, ¬ z.IsDiag) (hlen : T.st.length = n + n)
    (e : Equiv.Perm (Fin n))
    (ha : ∀ r, ArcAt T.st (strandId r) (n - 1 - r.val) (n + (e r).val))
    (f : Sym2 ℕ → M) :
    (T.xs.map f).sum = ∑ r, ∑ s with r < s ∧ e s < e r,
      f s(strandId r, strandId s) := by
  classical
  let S : Finset (Fin n × Fin n) := Finset.univ.filter fun rs =>
    rs.1 < rs.2 ∧ e rs.2 < e rs.1
  have hm (r s : Fin n) (hrs : r < s) :
      s(strandId r, strandId s) ∈ T.xs ↔ e s < e r :=
    (crossing_mem_iff ht hn (fun h => (ne_of_lt hrs) (strandId_injective h))).trans
      (endpoint_inversion e ha hrs)
  have hs : (∑ rs ∈ S, f s(strandId rs.1, strandId rs.2)) =
      ∑ z ∈ T.xs.toFinset, f z := by
    apply Finset.sum_bij (fun rs _ => s(strandId rs.1, strandId rs.2))
    · intro rs h
      obtain ⟨h₁, h₂⟩ := (Finset.mem_filter.mp h).2
      exact List.mem_toFinset.mpr ((hm _ _ h₁).mpr h₂)
    · intro rs h ss hh he
      obtain ⟨h₁, _⟩ := (Finset.mem_filter.mp h).2
      obtain ⟨h₂, _⟩ := (Finset.mem_filter.mp hh).2
      rcases Sym2.eq_iff.mp he with h | h
      · exact Prod.ext (strandId_injective h.1) (strandId_injective h.2)
      · have h3 := strandId_injective h.1
        have h4 := strandId_injective h.2
        exact False.elim (lt_asymm h₁ (by simpa only [h3, h4] using h₂))
    · intro z hz
      have hz' := List.mem_toFinset.mp hz
      have hnd := hd z hz'
      induction z using Sym2.ind with
      | _ x y =>
        have hxy : x ≠ y := fun h => hnd (by simp [h])
        have hil := (crossing_mem_iff ht hn hxy).mp hz'
        have hcover := endpoint_id_coverage e hlen ha
        have hx : ∃ r : Fin n, x = strandId r := by
          rcases hil with ⟨i, j, k, l, hq, hi, _⟩ | ⟨i, j, k, l, hq, _, hj⟩
          · obtain ⟨r, hr⟩ := hcover i hq.2.2.2.1.lt_left
            exact ⟨r, Option.some.inj (hi.symm.trans hr)⟩
          · obtain ⟨r, hr⟩ := hcover j hq.2.2.2.2.lt_left
            exact ⟨r, Option.some.inj (hj.symm.trans hr)⟩
        have hy : ∃ s : Fin n, y = strandId s := by
          rcases hil with ⟨i, j, k, l, hq, _, hj⟩ | ⟨i, j, k, l, hq, hi, _⟩
          · obtain ⟨s, hs⟩ := hcover j hq.2.2.2.2.lt_left
            exact ⟨s, Option.some.inj (hj.symm.trans hs)⟩
          · obtain ⟨s, hs⟩ := hcover i hq.2.2.2.1.lt_left
            exact ⟨s, Option.some.inj (hi.symm.trans hs)⟩
        obtain ⟨r, rfl⟩ := hx
        obtain ⟨s, rfl⟩ := hy
        have hrs : r ≠ s := fun h => hxy (congrArg strandId h)
        rcases lt_or_gt_of_ne hrs with hrs | hrs
        · refine ⟨(r, s), ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrs, (hm _ _ hrs).mp hz'⟩
        · refine ⟨(s, r), ?_, Sym2.eq_swap⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrs,
            (hm _ _ hrs).mp (by simpa only [Sym2.eq_swap] using hz')⟩
    · intro rs h; rfl
  rw [← List.sum_toFinset f hn, ← hs]
  simp only [S, Finset.sum_filter, Fintype.sum_prod_type]

private theorem mem_swap {β : Type*} {l : List β} {p : ℕ}
    (hp : p + 1 < l.length) {x : β} (hx : x ∈ swapAt l p) : x ∈ l := by
  obtain ⟨u, a, b, v, rfl, rfl⟩ := exists_split_cross hp
  rw [swapAt_mid] at hx
  simpa only [List.mem_append, List.mem_cons, or_left_comm, or_assoc] using hx

private theorem weighted_layers {I M : Type*} [AddCommMonoid M]
    (f : Sym2 ℕ → M) (wgt : Shape I → M) {k : ℕ} {u : List (Letter I)}
    (hu : u.length = k) (R : List (TMove (Letter I))) (T : TState (Letter I))
    (l : List (Letter I)) (hl : T.st.map Prod.snd = u ++ l) (hf : TFits flipL k T R)
    (hp : ∀ x ∈ l, x.1 = true)
    (hc : ∀ m ∈ R, ∃ p, m = TMove.mv (Move.cross p))
    (hw : ∀ X ∈ T.st, ∀ Y ∈ T.st, f s(X.1, Y.1) = wgt (.cross X.2.2 Y.2.2)) :
    ∃ L : List (LayerData I), SChain l L (R.foldl tLet l) ∧ L.map ofL = tLay l R ∧
      (∀ x ∈ L, ∃ i j, x.2.1 = Shape.cross i j) ∧
      ((tRun flipL k T R).xs.map f).sum =
        (T.xs.map f).sum + (L.map fun x => wgt x.2.1).sum := by
  induction R generalizing T l with
  | nil => exact ⟨[], rfl, rfl, by simp, (add_zero _).symm⟩
  | cons m R ih =>
    obtain ⟨p, rfl⟩ := hc m List.mem_cons_self
    obtain ⟨hm, hf⟩ := hf
    have hlen : T.st.length = k + l.length := by
      have h := congrArg List.length hl
      simpa [hu] using h
    have hpos : p + 1 < l.length := by change k + p + 1 < T.st.length at hm; omega
    have hnext := letters_tRun hu [TMove.mv (Move.cross p)] T l hl ⟨hm, trivial⟩
    simp only [tRun, List.foldl_cons, List.foldl_nil] at hnext
    obtain ⟨U, X, Y, W, v, x, y, z, hT, hU, rfl, rfl, hX, hY, _, _⟩ := split_state hl hpos
    have hx := hp x (by simp)
    have hy := hp y (by simp)
    obtain ⟨sx, i⟩ := x
    obtain ⟨sy, j⟩ := y
    dsimp only at hx hy
    subst sx sy
    have hstep : tLet (v ++ (true, i) :: (true, j) :: z) (.mv (.cross v.length)) =
        v ++ (true, j) :: (true, i) :: z := chStep_cross v z _ _
    rw [hstep] at hnext
    have hw' : ∀ X' ∈ (tStep flipL k T (.mv (.cross v.length))).st,
        ∀ Y' ∈ (tStep flipL k T (.mv (.cross v.length))).st,
        f s(X'.1, Y'.1) = wgt (.cross X'.2.2 Y'.2.2) := by
      intro X' hX' Y' hY'
      exact hw X' (mem_swap hm hX') Y' (mem_swap hm hY')
    obtain ⟨L, hL, he, hsh, hs⟩ := ih _ _ hnext hf
      (by simpa only [List.mem_append, List.mem_cons, or_left_comm, or_assoc] using hp)
      (fun m hm => hc m (List.mem_cons_of_mem _ hm)) hw'
    have hwXY := hw X (by rw [hT]; simp) Y (by rw [hT]; simp)
    rw [hX, hY] at hwXY
    have hwid : f s(idD T.st (k + v.length), idD T.st (k + v.length + 1)) =
        wgt (.cross i j) := by
      rw [← hu, ← hU, hT]
      simpa [idD, idAt] using hwXY
    refine ⟨(v, Shape.cross i j, z) :: L, ?_, ?_, ?_, ?_⟩
    · simp only [List.foldl_cons, hstep, sChain_cons, Shape.dom, Shape.cod,
        List.append_assoc, List.cons_append, List.nil_append]
      exact ⟨trivial, hL⟩
    · simp only [List.map_cons, tLay, tmLay, moveLay_cross, hstep, ← he]
      simp [show (true, i) = up i from rfl, show (true, j) = up j from rfl,
        xCrL_up_up, xwhL, ofL]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨i, j, rfl⟩
      · exact hsh x hx
    · change ((tRun flipL k (tStep flipL k T (.mv (.cross v.length))) R).xs.map f).sum = _
      rw [hs]
      simp only [tStep, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, hwid]
      exact add_assoc _ _ _

private theorem start_colours {I : Type*} {n : ℕ} (a : Fin n → I)
    {X : ℕ × Letter I} (hX : X ∈ (tStart (List.ofFn fun r => (true, a r))).st) :
    ∃ r : Fin n, X.1 = strandId r ∧ X.2.2 = a r := by
  have hleft {Y : ℕ × Letter I}
      (hY : Y ∈ cupLeft (dualW (List.ofFn fun r => (true, a r)))) :
      ∃ r : Fin n, Y.1 = strandId r ∧ Y.2.2 = a r := by
    obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hY
    have hin : i < n := by simpa [length_dualW] using hi
    let r : Fin n := ⟨n - 1 - i, by omega⟩
    refine ⟨r, ?_, ?_⟩
    · dsimp [strandId, r]
      omega
    · simp [dualW, flipL, r, Nat.sub_sub, Nat.add_comm]
  simp only [tStart, run_cupMoves, List.mem_append] at hX
  rcases hX with hX | hX
  · exact hleft hX
  · obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
    obtain ⟨r, hr, hc⟩ := hleft (List.mem_reverse.mp hY)
    exact ⟨r, hr, hc⟩

private theorem strandPair_injective {n : ℕ} :
    Function.Injective (Sym2.map (@strandId n)) := by
  intro x y h
  induction x using Sym2.ind with
  | _ a b =>
    induction y using Sym2.ind with
    | _ c d =>
      simp only [Sym2.map_mk, Sym2.eq_iff] at h ⊢
      exact h.elim (fun h => Or.inl ⟨strandId_injective h.1, strandId_injective h.2⟩)
        (fun h => Or.inr ⟨strandId_injective h.1, strandId_injective h.2⟩)

private theorem positive_weighted_layers {I M : Type*} [AddCommMonoid M]
    {n : ℕ} (a b : Fin n → I) {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R)
    (hred : StrictReduced₂ (List.ofFn fun r => (true, a r)) R)
    (e : Equiv.Perm (Fin n))
    (he : ∀ r, Same (pairing₂ (List.ofFn fun r => (true, a r)) R)
      (n - 1 - r.val) (n + (e r).val))
    (wgt : Shape I → M) (hw : ∀ i j, wgt (.cross i j) = wgt (.cross j i)) :
    ∃ L : List (LayerData I),
      SChain (List.ofFn fun r => (true, a r)) L (List.ofFn fun r => (true, b r)) ∧
      L.map ofL = tLay (List.ofFn fun r => (true, a r)) R ∧
      (∀ x ∈ L, ∃ i j, x.2.1 = Shape.cross i j) ∧
      (L.map fun x => wgt x.2.1).sum =
        ∑ r, ∑ s with r < s ∧ e s < e r, wgt (.cross (a r) (a s)) := by
  classical
  let A := List.ofFn fun r => (true, a r)
  let T := tRun flipL A.length (tStart A) R
  let g : Sym2 (Fin n) → M := Sym2.lift ⟨fun r s => wgt (.cross (a r) (a s)),
    fun r s => hw (a r) (a s)⟩
  let f : Sym2 ℕ → M := Function.extend (Sym2.map strandId) g (fun _ => 0)
  have hf (r s : Fin n) : f s(strandId r, strandId s) = wgt (.cross (a r) (a s)) := by
    exact strandPair_injective.extend_apply g (fun _ => 0) s(r, s)
  have hc := hR.positive_crossing_moves a b hred
  obtain ⟨L, hL, hmap, hsh, hs⟩ := weighted_layers f wgt (length_dualW A) R (tStart A) A
    (tStart_letters A) hR.1 (by intro x hx; obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hx; rfl) hc
    (by
      intro X hX Y hY
      obtain ⟨r, hr, ha⟩ := start_colours a hX
      obtain ⟨s, hs, hb⟩ := start_colours a hY
      rw [hr, hs, ha, hb]
      exact hf r s)
  refine ⟨L, hR.2 ▸ hL, hmap, hsh, ?_⟩
  have ht : TInv T := (tInv_tStart A).run hR.1
  have hlen : T.st.length = n + n := by
    have h := congrArg List.length (hR.pairing_properties).2.2
    simpa [T, pairing₂, length_dualW, A] using h
  have ha : ∀ r, ArcAt T.st (strandId r) (n - 1 - r.val) (n + (e r).val) := by
    intro r
    apply arcAt_of_valid ht.valid (he r)
    have hp := crossing_prefix R (tStart A) hR.1 hc (n - 1 - r.val)
      (by simp only [List.length_ofFn]; omega)
    exact hp.trans (start_bottom_id a r)
  have hsum := weighted_crossings ht hred.1.1 hred.1.2 hlen e ha f
  simp only [tStart, List.map_nil, List.sum_nil, zero_add] at hs
  rw [← hs]
  simpa only [hf, T, tStart] using hsum

/-- The degree and parity contribution of a positive strictly reduced matching in
[BE2, arXiv:1701.04133v2, Theorem 10.3, proof of Claim 1]. The permutation sends physical
left-to-right bottom positions to top positions; `he` records their existing endpoint pairing.
No grading, crossing enumeration or absence of critical points is assumed. -/
theorem positive_matching_degree_parity {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {n : ℕ} (a b : Fin n → I) {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R)
    (hred : StrictReduced₂ (List.ofFn fun r => (true, a r)) R)
    (e : Equiv.Perm (Fin n))
    (he : ∀ r, Same (pairing₂ (List.ofFn fun r => (true, a r)) R)
      (n - 1 - r.val) (n + (e r).val)) :
    ∃ (L : List (LayerData I))
      (hL : SChain (List.ofFn fun r => (true, a r)) L (List.ofFn fun r => (true, b r))),
      L.map ofL = tLay (List.ofFn fun r => (true, a r)) R ∧
      Diagram.degree (gdeg D sy) (mkD D μ L hL) =
        ∑ r, ∑ s with r < s ∧ e s < e r, sy.d (a r) * D.d (a r) (a s) ∧
      xpar D μ (tLay (List.ofFn fun r => (true, a r)) R) =
        ∑ r, ∑ s with r < s ∧ e s < e r, D.parity (a r) * D.parity (a s) := by
  classical
  let wgt : Shape I → ℤ × ZMod 2 := fun s => (gdeg D sy (s, μ), s.parity D)
  have hw (i j : I) : wgt (.cross i j) = wgt (.cross j i) :=
    Prod.ext (sy.symm i j) (mul_comm _ _)
  obtain ⟨L, hL, hmap, hsh, hs⟩ := positive_weighted_layers a b hR hred e he wgt hw
  refine ⟨L, hL, hmap, ?_, ?_⟩
  · rw [degree_gdeg_mkD]
    have h := congrArg Prod.fst hs
    have hfst (xs : List (ℤ × ZMod 2)) : xs.sum.1 = (xs.map Prod.fst).sum := by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        simpa only [List.sum_cons, List.map_cons, Prod.fst_add] using congrArg (x.1 + ·) ih
    simp only [Prod.fst_sum, hfst, List.map_map] at h
    change (L.map fun x => gdeg D sy (x.2.1, μ)).sum = _ at h
    simp only [wgt, gdeg] at h
    rw [← h]
    congr 1
    apply List.map_congr_left
    intro x hx
    obtain ⟨i, j, hij⟩ := hsh x hx
    simp only [hij, gdeg]
  · rw [← hmap, xpar_map_ofL]
    have h := congrArg Prod.snd hs
    have hsnd (xs : List (ℤ × ZMod 2)) : xs.sum.2 = (xs.map Prod.snd).sum := by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        simpa only [List.sum_cons, List.map_cons, Prod.snd_add] using congrArg (x.2 + ·) ih
    simp only [Prod.snd_sum, hsnd, List.map_map] at h
    change (L.map fun x => Shape.parity D x.2.1).sum = _ at h
    simpa only [wgt, Shape.parity, parsum] using h

end OddMath.SKM
