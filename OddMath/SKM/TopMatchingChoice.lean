import OddMath.SKM.WeakMatchingChoice
import OddMath.SKM.PositiveMatchingDots

/-!
# Top serializers for upward matching choices

The positive-point construction for BE2 §8 supplies one output position per
strand. Here it is assembled into a complete choice using the same skeletons
and literal top-dot serializers, for the closure independence argument.
-/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
/-- Finite natural dot multiplicities supported on the output positions. -/
def TopCounts (d : ℕ) := {n : ℕ →₀ ℕ // ∀ j ∈ n.support, j < d}

namespace TopCounts
variable {d : ℕ}

def ofFn (n : Fin d → ℕ) : TopCounts d := by
  classical
  let f : ℕ → ℕ := fun j => if h : j < d then n ⟨j, h⟩ else 0
  let v := Finsupp.onFinset (Finset.range d) f (by
    intro j hj
    by_contra hn
    have hnd : ¬ j < d := by simpa only [Finset.mem_range] using hn
    exact hj (by simp [f, hnd]))
  exact ⟨v, fun j hj => Finset.mem_range.mp (Finsupp.support_onFinset_subset hj)⟩

@[simp] theorem ofFn_apply (n : Fin d → ℕ) (j : Fin d) :
    (ofFn n).val j.val = n j := by
  simp only [ofFn, Finsupp.onFinset_apply, dite_eq_left j.isLt]

def equivFun : (Fin d → ℕ) ≃ TopCounts d where
  toFun := ofFn
  invFun n j := n.val j.val
  left_inv n := by funext j; exact ofFn_apply n j
  right_inv n := by
    apply Subtype.ext
    ext j
    by_cases hj : j < d
    · exact ofFn_apply _ ⟨j, hj⟩
    · have hn : n.val j = 0 := by
        by_contra hz
        exact hj (n.property j (Finsupp.mem_support_iff.mpr hz))
      simp [ofFn, hj, hn]

end TopCounts

variable {I : Type*} {c d : ℕ} (a : Fin c → I) (b : Fin d → I)
namespace MatchingBasisChoice
variable (F : MatchingBasisChoice (List.ofFn fun r : Fin c => (true, a r)) (List.ofFn fun r : Fin d => (true, b r)))

def topPosition (R : F.members) : MatchingStrand (List.ofFn fun r : Fin c => (true, a r)) R.val ≃ Fin d :=
  Equiv.ofBijective (positive_top_points a b (F.matching R.val R.property).1).choose
    (positive_top_points a b (F.matching R.val R.property).1).choose_spec.1

/-- All strand multiplicities, reindexed by actual top endpoint positions. -/
def topCountsEquiv (R : F.members) : (MatchingStrand (List.ofFn fun r : Fin c => (true, a r)) R.val → ℕ) ≃ TopCounts d :=
  (Equiv.arrowCongr (F.topPosition a b R) (Equiv.refl ℕ)).trans TopCounts.equivFun

@[simp] theorem topCountsEquiv_apply (R : F.members) (n : MatchingStrand (List.ofFn fun r : Fin c => (true, a r)) R.val → ℕ)
    (j : MatchingStrand (List.ofFn fun r : Fin c => (true, a r)) R.val) :
    (F.topCountsEquiv a b R n).val (F.topPosition a b R j).val = n j := by
  simp [topCountsEquiv, TopCounts.equivFun]

theorem topPosition_onStrand (R : F.members) (j : MatchingStrand (List.ofFn fun r : Fin c => (true, a r)) R.val) :
    OnStrand₂ (List.ofFn fun r : Fin c => (true, a r)) R.val j.val (R.val.length, (F.topPosition a b R j).val) :=
  (positive_top_points a b (F.matching R.val R.property).1).choose_spec.2 j

/-- Same representatives and matching classes, with all dots placed at the top. -/
def atTop : MatchingBasisChoice (List.ofFn fun r : Fin c => (true, a r)) (List.ofFn fun r : Fin d => (true, b r)) where
  members := F.members
  matching := F.matching
  unique := F.unique
  complete := F.complete
  points R j := (R.val.length, strandPosition (fun j => (F.topPosition a b R j).val) j)
  onStrand R j hj := by
    simpa only [strandPosition, dite_eq_left hj] using F.topPosition_onStrand a b R ⟨j, hj⟩
  serialize R n := topDotMoves (List.ofFn fun r : Fin c => (true, a r)) R.val (fun j => (F.topPosition a b R j).val) n
  decorates R n := topDotMoves_decorates (List.ofFn fun r : Fin c => (true, a r)) R.val _ n


theorem atTop_bounded (R : (F.atTop a b).members) (j : ℕ) :
    ((F.atTop a b).points R j).1 ≤ R.val.length := le_rfl

theorem atTop_valid (R : (F.atTop a b).members) (n : MatchingStrand (List.ofFn fun r : Fin c => (true, a r)) R.val → ℕ) :
    DOk₂ (List.ofFn fun r : Fin c => (true, a r)) ((F.atTop a b).serialize R n) :=
  topDotMoves_valid b (F.matching R.val R.property).1 (F.topPosition a b R) n

theorem atTop_layers (t : (F.atTop a b).Labels) :
    (F.atTop a b).layers t = tLay (List.ofFn fun r : Fin c => (true, a r)) t.1.val ++
      (topDotLayers b (F.topPosition a b t.1) t.2).map ofL :=
  dLay_topDotMoves b (F.matching t.1.val t.1.property).1 (F.topPosition a b t.1) t.2


/-- Positions of the literal top dots, in the serializer's strand order. -/
def topPositions (R : F.members) (n : MatchingStrand (List.ofFn fun r : Fin c => (true, a r)) R.val → ℕ) : List ℕ :=
  (leftEnds₂ (List.ofFn fun r : Fin c => (true, a r)) R.val).attach.flatMap
    (fun j => List.replicate (n j) (F.topPosition a b R j).val)


theorem topPositions_length (R : F.members) (n) :
    (F.topPositions a b R n).length = ∑ j, n j := by
  classical
  unfold topPositions
  rw [List.length_flatMap]
  simp only [List.length_replicate]
  rw [← List.sum_toFinset n (nodup_leftEnds₂ _ _).attach]
  have he : (leftEnds₂ (List.ofFn fun r : Fin c => (true, a r)) R.val).attach.toFinset = Finset.univ := by
    ext j
    simp
  rw [he]

theorem topPositions_bound (R : F.members) (n) :
    ∀ i ∈ F.topPositions a b R n, i < d := by
  intro i hi
  obtain ⟨j, _, hj⟩ := List.mem_flatMap.mp hi
  rw [List.eq_of_mem_replicate hj]
  exact (F.topPosition a b R j).isLt

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


theorem topPositions_count (R : F.members) (n) (j : MatchingStrand (List.ofFn fun r : Fin c => (true, a r)) R.val) :
    (F.topPositions a b R n).count (F.topPosition a b R j).val = n j := by
  unfold topPositions
  exact count_flatMap_replicate _ (nodup_leftEnds₂ _ _).attach
    (fun j => (F.topPosition a b R j).val) n
    (fun x _ y _ h => (F.topPosition a b R).injective (Fin.ext h)) (List.mem_attach _ j)


theorem topPositions_count_eq (R : F.members) (n) (i : ℕ) :
    (F.topPositions a b R n).count i = (F.topCountsEquiv a b R n).val i := by
  by_cases hi : i < d
  · let j := (F.topPosition a b R).symm ⟨i, hi⟩
    have hj : (F.topPosition a b R j).val = i := by simp [j]
    rw [← hj, F.topPositions_count, F.topCountsEquiv_apply]
  · have hc : (F.topCountsEquiv a b R n).val i = 0 := by
      by_contra hn
      exact hi ((F.topCountsEquiv a b R n).property i (Finsupp.mem_support_iff.mpr hn))
    rw [hc]
    exact List.count_eq_zero.mpr (fun h => hi (F.topPositions_bound a b R n i h))

private theorem dLay_dt_list (v : List (Letter I)) (is : List ℕ) :
    dLay v (is.map (.dt (I := I))) = dotsOn v is := by
  induction is with
  | nil => rfl
  | cons j is ih => simpa only [List.map_cons, dLay, dotsOn_cons] using congrArg (dotOn v j ++ ·) ih

theorem atTop_moves (R : (F.atTop a b).members) (n) :
    (F.atTop a b).serialize R n = R.val.map .tm ++ (F.topPositions a b R n).map .dt := by
  change topDotMoves _ _ _ _ = _
  unfold topDotMoves topPositions
  conv_lhs => rw [← List.attach_map_subtype_val (leftEnds₂ _ _), List.flatMap_map]
  rw [List.map_flatMap]
  congr 1
  apply List.flatMap_congr
  intro j _
  simp only [List.map_replicate, strandCounts_apply, strandPosition_apply]

theorem atTop_layers_dotsOn (t : (F.atTop a b).Labels) :
    (F.atTop a b).layers t = tLay (List.ofFn fun r : Fin c => (true, a r)) t.1.val ++
      dotsOn (List.ofFn fun r : Fin d => (true, b r)) (F.topPositions a b t.1 t.2) := by
  change dLay _ _ = _
  rw [F.atTop_moves a b, dLay_append, dLay_map_tm, tmoves_map_tm,
    (F.matching t.1.val t.1.property).1.2, dLay_dt_list]


/-- Every top-decorated upward representative has ordinary layers, exactly
rather than up to a scalar or matching isomorphism. -/
theorem atTop_ordinary (t : (F.atTop a b).Labels) :
    ∃ L : List (LayerData I),
      SChain (List.ofFn fun r : Fin c => (true, a r)) L (List.ofFn fun r : Fin d => (true, b r)) ∧
      L.map ofL = (F.atTop a b).layers t := by
  obtain ⟨L₀, _, he, _⟩ := positive_tLay_ofL a b
    (F.matching t.1.val t.1.property).1 (F.matching t.1.val t.1.property).2
  let L := L₀ ++ topDotLayers b (F.topPosition a b t.1) t.2
  have he' : L.map ofL = (F.atTop a b).layers t := by
    rw [F.atTop_layers a b]
    simp only [L, List.map_append, he]
  refine ⟨L, ?_, he'⟩
  have hc := (F.atTop a b).layers_chain t
  rw [← he'] at hc
  suffices h : ∀ (v z : List (Letter I)) (M : List (LayerData I)),
      XChain v (M.map ofL) z → SChain v M z from h _ _ L hc
  intro v z M
  induction M generalizing v with
  | nil => exact id
  | cons x M ih =>
    rintro ⟨h, ht⟩
    exact ⟨h, ih _ ht⟩

end MatchingBasisChoice
end OddMath.SKM
