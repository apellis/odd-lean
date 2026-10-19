import OddMath.SKM.PositiveDecoratedGrading

/-!
# Degree and parity at arbitrary positive strand points

The positive distinguished-point and dot-order invariance step in
[BE2, arXiv:1701.04133v2, §8 and Theorem 10.3, proof preceding Claim 1].
Every existing valid decoration of a positive strictly reduced matching has ordinary
layers realizing exactly its extended layers, with the existing diagram degree and
parity given by the crossing inversion weights and top-indexed strand counts.

Crossing-only strand-id renaming is trivial, but physical positions and colours are
permuted. The proof transports colours through the full labelled states; it does not
assume colour preservation or an ordinary decorated realization. No finite colour
type, distinct-colour hypothesis, or default colour is required.

`OnStrand₂` alone does not bound the height: the theorem quantifies over existing
valid decorations, not their existence for every point function. Numeric invariance
does not assert arbitrary-selector family enumeration, quotient injectivity, mixed
cup/cap invariance, or the algebraic-form comparison of Claim 1.
-/

namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
open scoped BigOperators

private theorem fits_take {I : Type*} (k : ℕ) (T : TState (Letter I))
    (R : List (TMove (Letter I))) (h : TFits flipL k T R) (n : ℕ) :
    TFits flipL k T (R.take n) := by
  induction R generalizing T n with
  | nil => simpa using h
  | cons m R ih =>
    cases n with
    | zero => trivial
    | succ n => exact ⟨h.1, ih _ h.2 n⟩

private theorem ren_crossings {I : Type*} (k : ℕ) (T : TState (Letter I))
    (R : List (TMove (Letter I)))
    (hc : ∀ m ∈ R, ∃ p, m = TMove.mv (Move.cross p)) (x : ℕ) :
    tRen k T R x = x := by
  induction R generalizing T with
  | nil => rfl
  | cons m R ih =>
    obtain ⟨p, rfl⟩ := hc m List.mem_cons_self
    exact ih _ (fun m hm => hc m (List.mem_cons_of_mem _ hm))

private theorem run_mem {I : Type*} (k : ℕ) (T : TState (Letter I))
    (R : List (TMove (Letter I))) (hf : TFits flipL k T R)
    (hc : ∀ m ∈ R, ∃ p, m = TMove.mv (Move.cross p))
    {x : ℕ × Letter I} (hx : x ∈ (tRun flipL k T R).st) : x ∈ T.st := by
  induction R generalizing T with
  | nil => exact hx
  | cons m R ih =>
    obtain ⟨p, rfl⟩ := hc m List.mem_cons_self
    have hh := ih _ hf.2 (fun m hm => hc m (List.mem_cons_of_mem _ hm)) hx
    change x ∈ swapAt T.st (k + p) at hh
    obtain ⟨u, a, b, v, he, hp⟩ := exists_split_cross hf.1
    rw [← hp, he, swapAt_mid] at hh
    rw [he]
    simpa only [List.mem_append, List.mem_cons, or_left_comm, or_assoc] using hh

private theorem start_colour {I : Type*} {n : ℕ} (a : Fin n → I)
    {x : ℕ × Letter I} (hx : x ∈ (tStart (List.ofFn fun r => (true, a r))).st) :
    ∃ r : Fin n, x.1 = 2 * (n - 1 - r.val) ∧ x.2.2 = a r := by
  have left {y : ℕ × Letter I}
      (hy : y ∈ cupLeft (dualW (List.ofFn fun r => (true, a r)))) :
      ∃ r : Fin n, y.1 = 2 * (n - 1 - r.val) ∧ y.2.2 = a r := by
    obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.mp hy
    have hin : i < n := by simpa [length_dualW] using hi
    let r : Fin n := ⟨n - 1 - i, by omega⟩
    refine ⟨r, ?_, ?_⟩
    · dsimp [r]; omega
    · simp [dualW, flipL, r, Nat.sub_sub, Nat.add_comm]
  simp only [tStart, run_cupMoves, List.mem_append] at hx
  rcases hx with hx | hx
  · exact left hx
  · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨r, hr, hc⟩ := left (List.mem_reverse.mp hy)
    exact ⟨r, hr, hc⟩

private theorem positive_fold {I : Type*} {k : ℕ} {u : List (Letter I)}
    (hu : u.length = k) (R : List (TMove (Letter I))) (T : TState (Letter I))
    (l : List (Letter I)) (hl : T.st.map Prod.snd = u ++ l)
    (hf : TFits flipL k T R) (hp : ∀ x ∈ l, x.1 = true)
    (hc : ∀ m ∈ R, ∃ p, m = TMove.mv (Move.cross p)) :
    ∀ x ∈ R.foldl tLet l, x.1 = true := by
  induction R generalizing T l with
  | nil => exact hp
  | cons m R ih =>
    obtain ⟨p, rfl⟩ := hc m List.mem_cons_self
    have hlen : T.st.length = k + l.length := by
      have h := congrArg List.length hl
      simpa [hu] using h
    have hpos : p + 1 < l.length := by
      have hm := hf.1
      change k + p + 1 < T.st.length at hm
      omega
    have hn := letters_tRun hu [TMove.mv (Move.cross p)] T l hl ⟨hf.1, trivial⟩
    simp only [tRun, List.foldl_cons, List.foldl_nil] at hn
    obtain ⟨v, x, y, w, rfl, rfl⟩ := exists_split_cross hpos
    have hs := chStep_cross v w x y
    change tLet (v ++ x :: y :: w) (.mv (.cross v.length)) = _ at hs
    rw [hs] at hn
    simp only [List.foldl_cons, hs]
    exact ih _ _ hn hf.2
      (by simpa only [List.mem_append, List.mem_cons, or_left_comm, or_assoc] using hp)
      (fun m hm => hc m (List.mem_cons_of_mem _ hm))

private theorem point_entry {I : Type*} {n : ℕ} (a : Fin n → I)
    (R : List (TMove (Letter I)))
    (hf : TFits flipL (List.ofFn fun r => (true, a r)).length
      (tStart (List.ofFn fun r => (true, a r))) R)
    (hc : ∀ m ∈ R, ∃ p, m = TMove.mv (Move.cross p))
    (h k : ℕ) (hk : k < ((R.take h).foldl tLet (List.ofFn fun r => (true, a r))).length) :
    ∃ x : ℕ × Letter I,
      x ∈ (tStart (List.ofFn fun r => (true, a r))).st ∧
      x.1 = idD (tRun flipL n (tStart (List.ofFn fun r => (true, a r))) (R.take h)).st (n + k) ∧
      ((R.take h).foldl tLet (List.ofFn fun r => (true, a r)))[k]? = some x.2 ∧
      x.2.1 = true := by
  let A := List.ofFn fun r => (true, a r)
  let T := tRun flipL A.length (tStart A) (R.take h)
  have hf' := fits_take A.length (tStart A) R hf h
  have hc' : ∀ m ∈ R.take h, ∃ p, m = TMove.mv (Move.cross p) :=
    fun m hm => hc m (List.mem_of_mem_take hm)
  have hl := letters_tRun (length_dualW A) (R.take h) (tStart A) A (tStart_letters A) hf'
  have hlen : T.st.length = A.length + ((R.take h).foldl tLet A).length := by
    have hh := congrArg List.length hl
    simpa [T, length_dualW] using hh
  have hi : A.length + k < T.st.length := by change k < ((R.take h).foldl tLet A).length at hk; omega
  let x := T.st[A.length + k]
  have hx : T.st[A.length + k]? = some x := List.getElem?_eq_getElem hi
  have hxlet : ((R.take h).foldl tLet A)[k]? = some x.2 := by
    have hh := congrArg (fun l => l[A.length + k]?) hl
    rw [List.getElem?_map, hx] at hh
    simpa [List.getElem?_append_right, length_dualW] using hh.symm
  refine ⟨x, run_mem A.length (tStart A) (R.take h) hf' hc'
    (List.mem_of_getElem? hx), ?_, hxlet, ?_⟩
  · have hx' : (tRun flipL n (tStart (List.ofFn fun r => (true, a r)))
        (R.take h)).st[n + k]? = some x := by simpa [T, A] using hx
    simp only [idD, idAt, hx', Option.map_some, Option.getD_some]
  · exact positive_fold (length_dualW A) (R.take h) (tStart A) A
      (tStart_letters A) hf'
      (by intro x hx; obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hx; rfl) hc'
      x.2 (List.mem_of_getElem? hxlet)

private theorem point_colour {I : Type*} {n : ℕ} (a b : Fin n → I)
    {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R)
    (hc : ∀ m ∈ R, ∃ p, m = TMove.mv (Move.cross p))
    {j : ℕ} {q : ℕ × ℕ} {t : Fin n}
    (hq : OnStrand₂ (List.ofFn fun r => (true, a r)) R j q)
    (ht : OnStrand₂ (List.ofFn fun r => (true, a r)) R j (R.length, t.val)) :
    ((R.take q.1).foldl tLet (List.ofFn fun r => (true, a r)))[q.2]? =
      some (true, b t) := by
  obtain ⟨x, hx, hxi, hxq, hxp⟩ := point_entry a R hR.1 hc q.1 q.2 hq.1
  obtain ⟨y, hy, hyi, hyt, _⟩ := point_entry a R hR.1 hc R.length t.val ht.1
  have hxy : x.1 = y.1 := by
    have hq' := hq.2
    have ht' := ht.2
    rw [ren_crossings _ _ _ (fun m hm => hc m (List.mem_of_mem_drop hm))] at hq' ht'
    simpa only [List.length_ofFn, hxi, hyi] using hq'.trans ht'.symm
  obtain ⟨r, hr, hrc⟩ := start_colour a hx
  obtain ⟨s, hs, hsc⟩ := start_colour a hy
  have hrs : r = s := by
    apply Fin.ext
    have := r.isLt
    have := s.isLt
    omega
  have hyc : y.2 = (true, b t) := by
    simpa [hR.2] using hyt.symm
  rw [hxq]
  congr 1
  apply Prod.ext hxp
  rw [hrs] at hrc
  simpa [hyc] using hrc.trans hsc.symm

private def pointWeight {I M : Type*} [Zero M] (f : I → M)
    (l : List (Letter I)) (R : List (TMove (Letter I))) (x : ℕ × ℕ) : M :=
  (((R.take x.1).foldl tLet l)[x.2]?).elim 0 (fun a => f a.2)

private theorem decorated_layers {I M : Type*} [AddCommMonoid M]
    (wgt : LayerData I → M) (f : I → M)
    (hw : ∀ u i v, wgt (u, Shape.dot i, v) = f i)
    {k : ℕ} {u : List (Letter I)} (hu : u.length = k)
    (ds : List (DTMove I)) (T : TState (Letter I)) (l : List (Letter I))
    (hl : T.st.map Prod.snd = u ++ l) (hf : TFits flipL k T (tmoves ds))
    (hp : ∀ x ∈ l, x.1 = true)
    (hc : ∀ m ∈ tmoves ds, ∃ p, m = TMove.mv (Move.cross p)) (hd : DOk₂ l ds) :
    ∃ L L₀ : List (LayerData I), SChain l L ((tmoves ds).foldl tLet l) ∧
      L.map ofL = dLay l ds ∧ L₀.map ofL = tLay l (tmoves ds) ∧
      (L.map wgt).sum = (L₀.map wgt).sum +
        ((dotPts ds).map (pointWeight f l (tmoves ds))).sum := by
  induction ds generalizing T l with
  | nil => exact ⟨[], [], rfl, rfl, rfl, (zero_add _).symm⟩
  | cons d ds ih =>
    cases d with
    | tm m =>
      obtain ⟨p, rfl⟩ := hc m List.mem_cons_self
      have hlen : T.st.length = k + l.length := by
        have h := congrArg List.length hl
        simpa [hu] using h
      have hpos : p + 1 < l.length := by
        have hm := hf.1
        change k + p + 1 < T.st.length at hm
        omega
      have hn := letters_tRun hu [TMove.mv (Move.cross p)] T l hl ⟨hf.1, trivial⟩
      simp only [tRun, List.foldl_cons, List.foldl_nil] at hn
      obtain ⟨v, x, y, z, rfl, rfl⟩ := exists_split_cross hpos
      have hx := hp x (by simp)
      have hy := hp y (by simp)
      obtain ⟨sx, i⟩ := x
      obtain ⟨sy, j⟩ := y
      dsimp only at hx hy
      subst sx sy
      have hs : tLet (v ++ (true, i) :: (true, j) :: z) (.mv (.cross v.length)) =
          v ++ (true, j) :: (true, i) :: z := chStep_cross v z _ _
      rw [hs] at hn
      change DOk₂ (tLet _ _) ds at hd
      rw [hs] at hd
      obtain ⟨L, L₀, hL, he, he₀, hwgt⟩ := ih _ _ hn hf.2
        (by simpa only [List.mem_append, List.mem_cons, or_left_comm, or_assoc] using hp)
        (fun m hm => hc m (List.mem_cons_of_mem _ hm)) hd
      refine ⟨(v, Shape.cross i j, z) :: L, (v, Shape.cross i j, z) :: L₀, ?_, ?_, ?_, ?_⟩
      · simp only [tmoves, List.foldl_cons, hs, sChain_cons, Shape.dom, Shape.cod,
          List.append_assoc, List.cons_append, List.nil_append]
        exact ⟨trivial, hL⟩
      · simp only [List.map_cons, dLay, tmLay, moveLay_cross, hs, ← he]
        simp [show (true, i) = up i from rfl, show (true, j) = up j from rfl,
          xCrL_up_up, xwhL, ofL]
      · simp only [List.map_cons, tmoves, tLay, tmLay, moveLay_cross, hs, ← he₀]
        simp [show (true, i) = up i from rfl, show (true, j) = up j from rfl,
          xCrL_up_up, xwhL, ofL]
      · simp only [List.map_cons, List.sum_cons, hwgt, dotPts, List.map_map, tmoves]
        have hh : (fun x : ℕ × ℕ => pointWeight f (v ++ (true, i) :: (true, j) :: z)
            (.mv (.cross v.length) :: tmoves ds) (x.1 + 1, x.2)) =
            pointWeight f (v ++ (true, j) :: (true, i) :: z) (tmoves ds) := by
          funext x
          simp only [pointWeight, List.take_succ_cons, List.foldl_cons, hs]
        change _ = _ + ((dotPts ds).map (fun x => pointWeight f _ _ (x.1 + 1, x.2))).sum
        rw [hh, add_assoc]
    | dt i =>
      obtain ⟨v, x, z, rfl, rfl⟩ := exists_split_dot hd.1
      have hx := hp x (by simp)
      obtain ⟨sx, i⟩ := x
      dsimp only at hx
      subst sx
      obtain ⟨L, L₀, hL, he, he₀, hwgt⟩ := ih T _ hl hf hp hc hd.2
      refine ⟨(v, Shape.dot i, z) :: L, L₀, ?_, ?_, he₀, ?_⟩
      · simp only [tmoves, sChain_cons, Shape.dom, Shape.cod, List.append_assoc,
          List.cons_append, List.nil_append]
        exact ⟨trivial, hL⟩
      · simp only [List.map_cons, dLay, dotOn_eq, ← he]
        simp [show (true, i) = up i from rfl, xDotL_up, xwhL, ofL]
      · simp only [List.map_cons, List.sum_cons, hw, hwgt, dotPts, tmoves]
        have hh : pointWeight f (v ++ (true, i) :: z) (tmoves ds) (0, v.length) = f i := by
          simp [pointWeight]
        rw [hh]
        ac_rfl

private theorem decoration_ok {I : Type*} {a : List (Letter I)}
    {R : List (TMove (Letter I))} {q : ℕ → ℕ × ℕ} {c : ℕ → ℕ}
    {ds : List (DTMove I)} (hq : ∀ j ∈ leftEnds₂ a R, OnStrand₂ a R j (q j))
    (hds : Decorates₂ a R q c ds) : DOk₂ a ds := by
  apply dOk₂_of_dotPts
  intro x hx
  have hh := hds.2.mem_iff.mp hx
  obtain ⟨j, hj, hx⟩ := List.mem_flatMap.mp hh
  have he : x = q j := (List.mem_replicate.mp hx).2
  rw [he, hds.1]
  exact (hq j hj).1

private theorem dot_weights {I M : Type*} [AddCommMonoid M] {n : ℕ}
    (a b : Fin n → I) {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R)
    (hc : ∀ m ∈ R, ∃ p, m = TMove.mv (Move.cross p))
    (p : MatchingStrand (List.ofFn fun r => (true, a r)) R ≃ Fin n)
    (hp : ∀ j : MatchingStrand (List.ofFn fun r => (true, a r)) R,
      OnStrand₂ (List.ofFn fun r => (true, a r)) R j.val (R.length, (p j).val))
    (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ (List.ofFn fun r => (true, a r)) R,
      OnStrand₂ (List.ofFn fun r => (true, a r)) R j (q j))
    (c : Fin n → ℕ) (ds : List (DTMove I))
    (hds : Decorates₂ (List.ofFn fun r => (true, a r)) R q
      (strandCounts (fun j => c (p j))) ds) (f : I → M) :
    ((dotPts ds).map (pointWeight f (List.ofFn fun r => (true, a r)) R)).sum =
      ∑ t, c t • f (b t) := by
  classical
  let A := List.ofFn fun r => (true, a r)
  have ht (j : MatchingStrand A R) : pointWeight f A R (q j) = f (b (p j)) := by
    unfold pointWeight
    rw [point_colour a b hR hc (hq j j.property) (hp j)]
    rfl
  rw [(hds.2.map _).sum_eq]
  have sum_flat (s : List ℕ) (g : ℕ → List M) :
      (s.flatMap g).sum = (s.map fun x => (g x).sum).sum := by
    induction s with
    | nil => rfl
    | cons x s ih => simp only [List.flatMap_cons, List.sum_append, ih, List.map_cons,
        List.sum_cons]
  simp only [List.map_flatMap, List.map_replicate, sum_flat, List.sum_replicate]
  conv_lhs => rw [← List.attach_map_subtype_val (leftEnds₂ A R), List.map_map]
  change ((leftEnds₂ A R).attach.map fun j : MatchingStrand A R =>
    strandCounts (fun j => c (p j)) j.val • pointWeight f A R (q j.val)).sum = _
  simp only [strandCounts_apply, ht]
  have hu : (leftEnds₂ A R).attach.toFinset = Finset.univ := by ext j; simp
  rw [← List.sum_toFinset _ ((nodup_leftEnds₂ A R).attach), hu]
  exact Equiv.sum_comp p (fun t => c t • f (b t))

private theorem ofL_injective {I : Type*} : Function.Injective (@ofL I) := by
  rintro ⟨u, s, v⟩ ⟨u', s', v'⟩ h
  cases h
  rfl

private theorem pair_sum {α M N : Type*} [AddMonoid M] [AddMonoid N]
    (l : List α) (f : α → M) (g : α → N) :
    (l.map fun x => (f x, g x)).sum = ((l.map f).sum, (l.map g).sum) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, Prod.mk_add_mk]

/-- For every existing valid decoration at strand points, the positive matching's ordinary
layers have crossing inversion degree/parity plus top-indexed dot weights. Points and dot
orders may vary. The premise does not assert existence of a decoration at every height. -/
theorem positive_point_decorated_degree_parity {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {n : ℕ} (a b : Fin n → I) {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R)
    (hred : StrictReduced₂ (List.ofFn fun r => (true, a r)) R)
    (e : Equiv.Perm (Fin n))
    (he : ∀ r, Same (pairing₂ (List.ofFn fun r => (true, a r)) R)
      (n - 1 - r.val) (n + (e r).val))
    (p : MatchingStrand (List.ofFn fun r => (true, a r)) R ≃ Fin n)
    (hp : ∀ j : MatchingStrand (List.ofFn fun r => (true, a r)) R,
      OnStrand₂ (List.ofFn fun r => (true, a r)) R j.val (R.length, (p j).val))
    (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ (List.ofFn fun r => (true, a r)) R,
      OnStrand₂ (List.ofFn fun r => (true, a r)) R j (q j))
    (c : Fin n → ℕ) (ds : List (DTMove I))
    (hds : Decorates₂ (List.ofFn fun r => (true, a r)) R q
      (strandCounts (fun j => c (p j))) ds) :
    ∃ (L : List (LayerData I))
      (hL : SChain (List.ofFn fun r => (true, a r)) L (List.ofFn fun r => (true, b r))),
      L.map ofL = dLay (List.ofFn fun r => (true, a r)) ds ∧
      Diagram.degree (gdeg D sy) (mkD D μ L hL) =
        (∑ r, ∑ s with r < s ∧ e s < e r, sy.d (a r) * D.d (a r) (a s)) +
        ∑ t, (c t : ℤ) * (2 * sy.d (b t)) ∧
      xpar D μ (dLay (List.ofFn fun r => (true, a r)) ds) =
        (∑ r, ∑ s with r < s ∧ e s < e r, D.parity (a r) * D.parity (a s)) +
        ∑ t, (c t : ZMod 2) * D.parity (b t) := by
  classical
  let A := List.ofFn fun r => (true, a r)
  let wgt : LayerData I → ℤ × ZMod 2 :=
    fun x => (gdeg D sy (x.2.1, wt D μ x.2.2), x.2.1.parity D)
  let f : I → ℤ × ZMod 2 := fun i => (2 * sy.d i, D.parity i)
  have hc := hR.positive_crossing_moves a b hred
  have hd := decoration_ok hq hds
  obtain ⟨L, L₀, hL, hm, hm₀, hs⟩ := decorated_layers wgt f (by intros; rfl)
    (length_dualW A) ds (tStart A) A (tStart_letters A)
    (by rw [hds.1]; exact hR.1)
    (by intro x hx; obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hx; rfl)
    (by rw [hds.1]; exact hc) hd
  rw [hds.1, hR.2] at hL
  rw [hds.1] at hm₀ hs
  obtain ⟨K, hK, hKm, hKd, hKp⟩ := positive_matching_degree_parity D sy μ a b hR hred e he
  have hLK : L₀ = K := List.map_injective_iff.mpr ofL_injective (hm₀.trans hKm.symm)
  rw [hLK, dot_weights a b hR hc p hp q hq c ds hds f] at hs
  have hs₁ := congrArg Prod.fst hs
  have hs₂ := congrArg Prod.snd hs
  simp only [wgt, pair_sum, Prod.fst_add, Prod.fst_sum, f,
    nsmul_eq_mul] at hs₁
  simp only [wgt, pair_sum, Prod.snd_add, Prod.snd_sum, f,
    nsmul_eq_mul] at hs₂
  refine ⟨L, hL, hm, ?_, ?_⟩
  · rw [degree_gdeg_mkD] at hKd ⊢
    exact hs₁.trans (congrArg (· + _) hKd)
  · rw [← hm, xpar_map_ofL]
    rw [← hKm, xpar_map_ofL] at hKp
    exact hs₂.trans (congrArg (· + _) hKp)

end OddMath.SKM
