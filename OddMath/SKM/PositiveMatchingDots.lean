import OddMath.SKM.PositiveMatchings
import OddMath.SKM.Grading

/-!
# Finite strand counts for positive decorated matchings

Supporting results for [BE2, arXiv:1701.04133v2, Theorem 10.3, proof of Claim 1],
using the distinguished-point decorations of §8. Counts are indexed by the finite set
of strands, not by all natural numbers. The chosen points are just above the final
matching move. No independence of arbitrary distinguished points, uniqueness of
matching representatives, or graphical series identity is asserted.
-/

noncomputable section
namespace OddMath.SKM
open StringDiagrams.Chord DTMove
variable {I : Type*}

/-- Strands of the existing matching, indexed without unused natural-number entries. -/
abbrev MatchingStrand (a : List (Letter I)) (R : List (TMove (Letter I))) :=
  {j : ℕ // j ∈ leftEnds₂ a R}

instance (a : List (Letter I)) (R : List (TMove (Letter I))) :
    Fintype (MatchingStrand a R) := by
  classical
  exact Fintype.ofFinset (leftEnds₂ a R).toFinset (by intro j; exact List.mem_toFinset)

/-- Extend finite strand counts by zero only to interface with `Decorates₂`. -/
def strandCounts {a : List (Letter I)} {R : List (TMove (Letter I))}
    (n : MatchingStrand a R → ℕ) (j : ℕ) : ℕ :=
  if h : j ∈ leftEnds₂ a R then n ⟨j, h⟩ else 0

@[simp] theorem strandCounts_apply {a : List (Letter I)} {R : List (TMove (Letter I))}
    (n : MatchingStrand a R → ℕ) (j : MatchingStrand a R) :
    strandCounts n j = n j := by simp [strandCounts, j.property]

/-- The decoration relation ignores exactly the off-strand count entries. -/
theorem decorates₂_strandCounts_iff {a : List (Letter I)} {R : List (TMove (Letter I))}
    (q : ℕ → ℕ × ℕ) (n : ℕ → ℕ) (ds : List (DTMove I)) :
    Decorates₂ a R q (strandCounts fun j : MatchingStrand a R => n j) ds ↔ Decorates₂ a R q n ds := by
  have he : (leftEnds₂ a R).flatMap (fun j => List.replicate
      (strandCounts (fun j : MatchingStrand a R => n j) j) (q j)) =
      (leftEnds₂ a R).flatMap (fun j => List.replicate (n j) (q j)) := by
    apply List.flatMap_congr
    intro j hj
    simp [strandCounts, hj]
  simp only [Decorates₂, he]

/-- A top endpoint gives a valid distinguished point on its paired strand. -/
theorem onStrand₂_top_of_same {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a b R) {j p : ℕ} (hp : p < b.length)
    (h : Same (pairing₂ a R) j (a.length + p)) :
    OnStrand₂ a R j (R.length, p) := by
  constructor
  · simpa [hR.2] using hp
  · simp only [List.take_length, List.drop_length, tRen, id_eq]
    change idD (pairing₂ a R) (a.length + p) = idD (pairing₂ a R) j
    have hh := h.2.2
    rw [idAt_eq_idD h.lt_left, idAt_eq_idD h.lt_right] at hh
    exact Option.some.inj hh.symm

/-- For a positive matching every left endpoint is on the bent bottom boundary. -/
theorem positive_mem_leftEnds₂ {c d : ℕ} (a : Fin c → I) (b : Fin d → I)
    {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun t => (true, b t)) R) (j : ℕ) :
    j ∈ leftEnds₂ (List.ofFn fun r => (true, a r)) R ↔ j < c := by
  obtain ⟨hv, hl, hs⟩ := hR.pairing_properties
  obtain ⟨e, he, -⟩ := positive_pairing_equiv a b hv hl hs
  have hlen : (pairing₂ (List.ofFn fun r => (true, a r)) R).length = c + d := by
    have hh := congrArg List.length hs
    simpa [length_dualW] using hh
  rw [mem_leftEnds₂]
  constructor
  · intro hj
    by_contra hn
    have hjlen := hj.1
    rw [hlen] at hjlen
    have ht : j - c < d := by omega
    let r := e.symm ⟨j - c, ht⟩
    have hh := he.2 r
    have hh' : Same (pairing₂ (List.ofFn fun r => (true, a r)) R)
        (c - 1 - r.val) j := by
      simpa [r, Nat.add_sub_of_le (by omega : c ≤ j)] using hh
    exact hj.2 ⟨c - 1 - r.val, by omega, hh'.symm⟩
  · intro hj
    let r : Fin c := ⟨c - 1 - j, by omega⟩
    have hr : c - 1 - r.val = j := by dsimp [r]; omega
    have hh := he.2 r
    rw [hr] at hh
    refine ⟨by rw [hlen]; omega, ?_⟩
    rintro ⟨k, hk, hsame⟩
    have := hv.unique hsame hh
    omega

/-- Positive strands have distinct top endpoints, giving permitted distinguished points. -/
theorem positive_top_points {c d : ℕ} (a : Fin c → I) (b : Fin d → I)
    {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun t => (true, b t)) R) :
    ∃ p : MatchingStrand (List.ofFn fun r => (true, a r)) R → Fin d,
      Function.Bijective p ∧ ∀ j : MatchingStrand (List.ofFn fun r => (true, a r)) R,
      OnStrand₂ (List.ofFn fun r => (true, a r)) R j (R.length, (p j).val) := by
  obtain ⟨hv, hl, hs⟩ := hR.pairing_properties
  obtain ⟨e, he, -⟩ := positive_pairing_equiv a b hv hl hs
  let f : MatchingStrand (List.ofFn fun r => (true, a r)) R → Fin c :=
    fun j => ⟨c - 1 - j.val, by
      have := (positive_mem_leftEnds₂ a b hR j).mp j.property
      omega⟩
  have hf : Function.Bijective f := by
    constructor
    · intro j k h
      apply Subtype.ext
      have hj := (positive_mem_leftEnds₂ a b hR j).mp j.property
      have hk := (positive_mem_leftEnds₂ a b hR k).mp k.property
      have hh := congrArg Fin.val h
      dsimp [f] at hh
      omega
    · intro r
      refine ⟨⟨c - 1 - r.val, (positive_mem_leftEnds₂ a b hR _).mpr (by omega)⟩, ?_⟩
      apply Fin.ext
      dsimp [f]
      omega
  refine ⟨fun j => e (f j), e.bijective.comp hf, ?_⟩
  intro j
  apply onStrand₂_top_of_same hR (by simp)
  have hh := he.2 (f j)
  have hj := (positive_mem_leftEnds₂ a b hR j).mp j.property
  have hr : c - 1 - (f j).val = j.val := by dsimp [f]; omega
  simpa only [List.length_ofFn, hr] using hh

/-- Extend top positions only for the natural-number interface of `Decorates₂`. -/
def strandPosition {a : List (Letter I)} {R : List (TMove (Letter I))}
    (p : MatchingStrand a R → ℕ) (j : ℕ) : ℕ :=
  if h : j ∈ leftEnds₂ a R then p ⟨j, h⟩ else 0

@[simp] theorem strandPosition_apply {a : List (Letter I)} {R : List (TMove (Letter I))}
    (p : MatchingStrand a R → ℕ) (j : MatchingStrand a R) :
    strandPosition p j = p j := by simp [strandPosition, j.property]

/-- Ordered dots above the matching; evaluation is the existing `dLay`. -/
def topDotMoves (a : List (Letter I)) (R : List (TMove (Letter I)))
    (p n : MatchingStrand a R → ℕ) : List (DTMove I) :=
  R.map .tm ++ ((leftEnds₂ a R).flatMap fun j =>
    List.replicate (strandCounts n j) (DTMove.dt (strandPosition p j)))

private theorem tmoves_dots (js : List ℕ) :
    tmoves (js.map (DTMove.dt (I := I))) = [] := by
  induction js with
  | nil => rfl
  | cons j js ih => simpa only [List.map_cons, tmoves] using ih

private theorem dotPts_dots (js : List ℕ) :
    dotPts (js.map (DTMove.dt (I := I))) = js.map (fun j => (0, j)) := by
  induction js with
  | nil => rfl
  | cons j js ih => simp only [List.map_cons, dotPts, ih]

private theorem dotPts_top (R : List (TMove (Letter I))) (js : List ℕ) :
    dotPts (R.map .tm ++ js.map .dt) = js.map (fun j => (R.length, j)) := by
  induction R with
  | nil => simpa using dotPts_dots (I := I) js
  | cons m R ih => simp [dotPts, ih, List.map_map, Function.comp_def]

private theorem topDotMoves_eq (a : List (Letter I)) (R : List (TMove (Letter I)))
    (p n : MatchingStrand a R → ℕ) :
    topDotMoves a R p n = R.map .tm ++
      ((leftEnds₂ a R).flatMap fun j => List.replicate (strandCounts n j)
        (strandPosition p j)).map .dt := by
  simp [topDotMoves, List.map_flatMap]

/-- The canonical top decoration satisfies precisely the pre-existing decoration relation. -/
theorem topDotMoves_decorates (a : List (Letter I)) (R : List (TMove (Letter I)))
    (p n : MatchingStrand a R → ℕ) :
    Decorates₂ a R (fun j => (R.length, strandPosition p j)) (strandCounts n)
      (topDotMoves a R p n) := by
  rw [topDotMoves_eq]
  constructor
  · simp [tmoves_dots]
  · rw [dotPts_top]
    simp only [List.map_flatMap, List.map_replicate]
    exact List.Perm.refl _

/-- The selected top positions are in range, so none of the added dots disappears. -/
theorem topDotMoves_valid {a : List (Letter I)} {d : ℕ} (b : Fin d → I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (List.ofFn fun t => (true, b t)) R)
    (p : MatchingStrand a R → Fin d) (n : MatchingStrand a R → ℕ) :
    DOk₂ a (topDotMoves a R (fun j => (p j).val) n) := by
  have hd := topDotMoves_decorates a R (fun j => (p j).val) n
  apply dOk₂_of_dotPts
  intro q hq
  obtain ⟨j, hj, hq⟩ := List.mem_flatMap.mp (hd.2.subset hq)
  have hqe := List.eq_of_mem_replicate hq
  rw [hqe, hd.1, List.take_length, hR.2]
  simp [strandPosition, hj]

/-- The decorated layers have the matching's source and target. -/
theorem xChain_topDotMoves {a : List (Letter I)} {d : ℕ} (b : Fin d → I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (List.ofFn fun t => (true, b t)) R)
    (p : MatchingStrand a R → Fin d) (n : MatchingStrand a R → ℕ) :
    XChain a (dLay a (topDotMoves a R (fun j => (p j).val) n))
      (List.ofFn fun t => (true, b t)) := by
  have hd := topDotMoves_decorates a R (fun j => (p j).val) n
  have hf := (matching_bent_spec hR).1
  have hh := (shiftD_spec (dualW a) a.length (length_dualW a)
    (topDotMoves a R (fun j => (p j).val) n) (tStart_letters a)
    (by rw [tmoves_map_shiftD, hd.1]; exact hf)).2.1
  rwa [hd.1, hR.2] at hh

/-- A finite count assignment gives the same family of existing diagrams as the raw
natural-number interface; the canonical choice does not inspect off-strand entries. -/
theorem topDotMoves_family (a : List (Letter I)) (M : Set (List (TMove (Letter I))))
    (p : ∀ R, MatchingStrand a R → ℕ) :
    decoratedFamily₂ a M (fun R n => topDotMoves a R (p R) (fun j => n j)) =
      {L | ∃ R ∈ M, ∃ n : MatchingStrand a R → ℕ, L = dLay a (topDotMoves a R (p R) n)} := by
  ext L
  constructor
  · rintro ⟨R, hR, n, hn⟩
    exact ⟨R, hR, fun j => n j, hn⟩
  · rintro ⟨R, hR, n, rfl⟩
    refine ⟨R, hR, strandCounts n, ?_⟩
    simp

private theorem count_flatMap_replicate {α β : Type*} [BEq β] [LawfulBEq β]
    (s : List α) (hs : s.Nodup) (q : α → β) (n : α → ℕ)
    (hq : ∀ x ∈ s, ∀ y ∈ s, q x = q y → x = y) {j : α} (hj : j ∈ s) :
    (s.flatMap fun x => List.replicate (n x) (q x)).count (q j) = n j := by
  induction s with
  | nil => simp at hj
  | cons x s ih =>
    obtain ⟨hx, hs⟩ := List.nodup_cons.mp hs
    rcases List.mem_cons.mp hj with rfl | hj
    · have hz : (s.flatMap fun y => List.replicate (n y) (q y)).count (q j) = 0 := by
        apply List.count_eq_zero.mpr
        intro hm
        obtain ⟨y, hy, hyq⟩ := List.mem_flatMap.mp hm
        have hxy := hq j List.mem_cons_self y (List.mem_cons_of_mem _ hy)
          (List.eq_of_mem_replicate hyq)
        exact hx (hxy ▸ hy)
      simp [hz]
    · have hne : q j ≠ q x := by
        intro he
        have := hq j (List.mem_cons_of_mem _ hj) x List.mem_cons_self he
        exact hx (this ▸ hj)
      have hi := ih hs (fun y hy z hz => hq y (List.mem_cons_of_mem _ hy)
        z (List.mem_cons_of_mem _ hz)) hj
      simp [List.count_replicate, Ne.symm hne, hi]

/-- Distinct distinguished points recover the finite strand counts from `Decorates₂`.
This is uniqueness of dot multiplicities, not uniqueness of matching representatives. -/
theorem decorates₂_counts_unique {a : List (Letter I)} {R : List (TMove (Letter I))}
    (q : ℕ → ℕ × ℕ) (hq : ∀ j ∈ leftEnds₂ a R, ∀ k ∈ leftEnds₂ a R,
      q j = q k → j = k) {n m : MatchingStrand a R → ℕ} {ds : List (DTMove I)}
    (hn : Decorates₂ a R q (strandCounts n) ds)
    (hm : Decorates₂ a R q (strandCounts m) ds) : n = m := by
  funext j
  have hc := (hn.2.symm.trans hm.2).count_eq (q j)
  rw [count_flatMap_replicate _ (nodup_leftEnds₂ a R) q (strandCounts n) hq j.property,
    count_flatMap_replicate _ (nodup_leftEnds₂ a R) q (strandCounts m) hq j.property] at hc
  simpa using hc

/-- Canonically ordered top decorations retain the matching and finite dot counts. -/
theorem topDotMoves_injective (a : List (Letter I)) (R : List (TMove (Letter I)))
    (p : MatchingStrand a R → ℕ) (hp : Function.Injective p) :
    Function.Injective (topDotMoves a R p) := by
  intro n m he
  refine decorates₂_counts_unique (fun j => (R.length, strandPosition p j))
    (ds := topDotMoves a R p n) ?_ ?_ ?_
  · intro j hj k hk h
    have hh : p ⟨j, hj⟩ = p ⟨k, hk⟩ := by
      simpa [strandPosition, hj, hk] using congrArg Prod.snd h
    exact congrArg Subtype.val (hp hh)
  · exact topDotMoves_decorates a R p n
  · rw [he]
    exact topDotMoves_decorates a R p m

/-- Ordinary upward-dot layers at the chosen top endpoints. -/
def topDotLayers {a : List (Letter I)} {R : List (TMove (Letter I))} {d : ℕ}
    (b : Fin d → I) (p : MatchingStrand a R → Fin d) (n : MatchingStrand a R → ℕ) :
    List (LayerData I) :=
  (leftEnds₂ a R).attach.flatMap fun j =>
    dotsL ((List.ofFn fun t => (true, b t)).take (p j).val) (b (p j))
      ((List.ofFn fun t => (true, b t)).drop ((p j).val + 1)) (n j)

private theorem dLay_dots_top {d : ℕ} (b : Fin d → I) (p : Fin d) (n : ℕ) :
    dLay (List.ofFn fun t => (true, b t)) (List.replicate n (.dt p.val)) =
      (dotsL ((List.ofFn fun t => (true, b t)).take p.val) (b p)
        ((List.ofFn fun t => (true, b t)).drop (p.val + 1)) n).map ofL := by
  have hp : p.val < (List.ofFn fun t => (true, b t)).length := by simp
  have hd : dotOn (List.ofFn fun t => (true, b t)) p.val =
      [((List.ofFn fun t => (true, b t)).take p.val, XShape.gen (.dot (b p)),
        (List.ofFn fun t => (true, b t)).drop (p.val + 1))] := by
    simp [dotOn, List.drop_eq_getElem_cons hp, xDotL, xwhL]
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, dLay, hd, ih, dotsL, ofL]

private theorem dLay_dot_blocks (B : List (Letter I)) (s : List α) (p : α → ℕ)
    (n : α → ℕ) :
    dLay B (s.flatMap fun j => List.replicate (n j) (DTMove.dt (p j))) =
      s.flatMap (fun j => dLay B (List.replicate (n j) (.dt (p j)))) := by
  have ht (j : α) : tmoves (List.replicate (n j) (DTMove.dt (I := I) (p j))) = [] := by
    simpa using tmoves_dots (I := I) (List.replicate (n j) (p j))
  induction s with
  | nil => rfl
  | cons j s ih => simp only [List.flatMap_cons, dLay_append, ht, List.foldl_nil, ih]

/-- The finite top decoration evaluates to the original matching followed by ordinary dots. -/
theorem dLay_topDotMoves {a : List (Letter I)} {d : ℕ} (b : Fin d → I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (List.ofFn fun t => (true, b t)) R)
    (p : MatchingStrand a R → Fin d) (n : MatchingStrand a R → ℕ) :
    dLay a (topDotMoves a R (fun j => (p j).val) n) =
      tLay a R ++ (topDotLayers b p n).map ofL := by
  unfold topDotMoves
  rw [dLay_append, dLay_map_tm, tmoves_map_tm, hR.2, dLay_dot_blocks]
  congr 1
  unfold topDotLayers
  rw [List.map_flatMap]
  conv_lhs => rw [← List.attach_map_subtype_val (leftEnds₂ a R), List.flatMap_map]
  apply List.flatMap_congr
  intro j _
  simp only [strandCounts_apply, strandPosition_apply]
  exact dLay_dots_top b (p j) (n j)

private theorem topDotLayers_decode {a : List (Letter I)} {d : ℕ} (b : Fin d → I)
    {R : List (TMove (Letter I))} (p : MatchingStrand a R → Fin d)
    (n : MatchingStrand a R → ℕ) :
    R.map DTMove.tm ++ (topDotLayers b p n).map (fun x => DTMove.dt x.1.length) =
      topDotMoves a R (fun j => (p j).val) n := by
  unfold topDotMoves topDotLayers
  congr 1
  rw [List.map_flatMap]
  conv_rhs => rw [← List.attach_map_subtype_val (leftEnds₂ a R), List.flatMap_map]
  apply List.flatMap_congr
  intro j _
  simp only [strandCounts_apply, strandPosition_apply, dotsL, List.map_replicate,
    List.length_take, List.length_ofFn]
  rw [Nat.min_eq_left (p j).isLt.le]

/-- Distinct finite counts give distinct lists of decorated layers at the selected
positive top endpoints. This is syntactic injectivity, not independence in the quotient. -/
theorem dLay_topDotMoves_injective {a : List (Letter I)} {d : ℕ} (b : Fin d → I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (List.ofFn fun t => (true, b t)) R)
    (p : MatchingStrand a R → Fin d) (hp : Function.Injective p) :
    Function.Injective (fun n => dLay a (topDotMoves a R (fun j => (p j).val) n)) := by
  intro n m he
  dsimp only at he
  rw [dLay_topDotMoves b hR p n, dLay_topDotMoves b hR p m] at he
  have he' := List.append_cancel_left he
  have hd := congrArg (List.map fun x : XLayer I => DTMove.dt (I := I) x.1.length) he'
  simp only [List.map_map, ofL, Function.comp_def] at hd
  have hh := congrArg (fun L => R.map DTMove.tm ++ L) hd
  rw [topDotLayers_decode, topDotLayers_decode] at hh
  exact topDotMoves_injective a R (fun j => (p j).val)
    (fun _ _ h => hp (Fin.ext h)) hh

private theorem sum_flatMap_eq {α β : Type*} [AddMonoid β] (s : List α) (f : α → List β) :
    (s.flatMap f).sum = (s.map fun j => (f j).sum).sum := by
  induction s with
  | nil => rfl
  | cons j s ih => simp only [List.flatMap_cons, List.sum_append, List.map_cons, List.sum_cons, ih]

variable {X : Type*} [AddCommGroup X] (D : Datum I X) (sy : Symmetrizer D) (μ : X)

/-- The total dot-degree increment, computed by the existing generator grading. -/
theorem gsum_topDotLayers {a : List (Letter I)} {R : List (TMove (Letter I))} {d : ℕ}
    (b : Fin d → I) (p : MatchingStrand a R → Fin d) (n : MatchingStrand a R → ℕ) :
    gsum D sy μ (topDotLayers b p n) =
      ((leftEnds₂ a R).attach.map fun j => (n j : ℤ) * (2 * sy.d (b (p j)))).sum := by
  simp [topDotLayers, gsum, List.map_flatMap, sum_flatMap_eq, dotsL, gdeg,
    List.sum_replicate]

/-- The total dot-parity increment, computed by the existing extended-layer parity. -/
theorem xpar_topDotLayers {a : List (Letter I)} {R : List (TMove (Letter I))} {d : ℕ}
    (b : Fin d → I) (p : MatchingStrand a R → Fin d) (n : MatchingStrand a R → ℕ) :
    xpar D μ ((topDotLayers b p n).map ofL) =
      ((leftEnds₂ a R).attach.map fun j => (n j : ZMod 2) * D.parity (b (p j))).sum := by
  simp [topDotLayers, xpar, List.map_flatMap, sum_flatMap_eq, dotsL, ofL, xlpar,
    Shape.parity, List.sum_replicate, nsmul_eq_mul]

/-- Additive degree over any ordinary-layer realization of the undecorated matching.
The crossing-degree identification is a separate input, not redefined here. -/
theorem topDotMoves_degree {a : List (Letter I)} {d : ℕ} (b : Fin d → I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (List.ofFn fun t => (true, b t)) R)
    (p : MatchingStrand a R → Fin d) (n : MatchingStrand a R → ℕ)
    (L : List (LayerData I)) (hL : L.map ofL = tLay a R) :
    (L ++ topDotLayers b p n).map ofL = dLay a (topDotMoves a R (fun j => (p j).val) n) ∧
    gsum D sy μ (L ++ topDotLayers b p n) = gsum D sy μ L +
      ((leftEnds₂ a R).attach.map fun j => (n j : ℤ) * (2 * sy.d (b (p j)))).sum := by
  constructor
  · rw [List.map_append, hL, dLay_topDotMoves b hR]
  · rw [gsum_append, gsum_topDotLayers]

/-- Additive parity over the undecorated matching, for the canonical top-point choice. -/
theorem topDotMoves_parity {a : List (Letter I)} {d : ℕ} (b : Fin d → I)
    {R : List (TMove (Letter I))} (hR : IsMatching₂ a (List.ofFn fun t => (true, b t)) R)
    (p : MatchingStrand a R → Fin d) (n : MatchingStrand a R → ℕ) :
    xpar D μ (dLay a (topDotMoves a R (fun j => (p j).val) n)) = xpar D μ (tLay a R) +
      ((leftEnds₂ a R).attach.map fun j => (n j : ZMod 2) * D.parity (b (p j))).sum := by
  rw [dLay_topDotMoves b hR, xpar_append, xpar_topDotLayers]

end OddMath.SKM
