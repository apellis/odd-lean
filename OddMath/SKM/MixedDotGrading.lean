import OddMath.SKM.MatchingStrandColour
import OddMath.SKM.TableIsotopy

/-! # Dot grading for mixed matchings

BE2 v2 §8 and the dot-choice part of the independence paragraph preceding
Theorem 10.3. The downward dot is evaluated from its expanded `ddotL` list.
-/
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
open scoped BigOperators

@[simp] theorem tableDegree_dot {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) (a : Letter I) :
    tableDegree D sy μ (xDotL a) = 2 * sy.d a.2 := by
  obtain ⟨_ | _, i⟩ := a
  · simp [xDotL, tableDegree, ofL, ddotL, mateL, dotsL, whL, gdeg, wt, sh,
      D.cd.coroot_root_self]
    ring
  · simp [xDotL, tableDegree, gdeg]

@[simp] theorem xpar_dot {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (μ : X) (a : Letter I) :
    xpar D μ (xDotL a) = D.parity a.2 := by
  obtain ⟨_ | _, i⟩ := a <;>
    simp [xDotL, xpar, xlpar, ofL, ddotL, mateL, dotsL, whL, Shape.parity]

private def pointWeight {I M : Type*} [Zero M] (f : I → M)
    (a : List (Letter I)) (R : List (TMove (Letter I))) (q : ℕ × ℕ) : M :=
  ((((R.take q.1).foldl tLet a)[q.2]?).map Prod.snd).elim 0 f

private theorem decorated_weight {I M : Type*} [AddCommMonoid M]
    (W : List (XLayer I) → M) (f : I → M) (hzero : W [] = 0)
    (hadd : ∀ L K, W (L ++ K) = W L + W K)
    (hdot : ∀ u a v, W ((xDotL a).map (xwhL u v)) = f a.2)
    (a : List (Letter I)) (ds : List (DTMove I)) (hok : DOk₂ a ds) :
    W (dLay a ds) = W (tLay a (tmoves ds)) +
      ((dotPts ds).map (pointWeight f a (tmoves ds))).sum := by
  induction ds generalizing a with
  | nil => simp [dLay, tLay, tmoves, dotPts, hzero]
  | cons z ds ih =>
    cases z with
    | tm m =>
      simp only [dLay, tmoves, tLay, dotPts, hadd, List.map_map]
      rw [ih _ hok]
      have hh : (fun q : ℕ × ℕ => pointWeight f a (m :: tmoves ds) (q.1 + 1, q.2)) =
          pointWeight f (tLet a m) (tmoves ds) := by
        funext q
        simp only [pointWeight, List.take_succ_cons, List.foldl_cons]
      change _ = _ + ((dotPts ds).map (fun q => pointWeight f a _ (q.1 + 1, q.2))).sum
      rw [hh, add_assoc]
    | dt p =>
      obtain ⟨u, x, v, rfl, rfl⟩ := exists_split_dot hok.1
      simp only [dLay, tmoves, dotPts, hadd, List.map_cons, List.sum_cons]
      rw [dotOn_eq, hdot, ih _ hok.2]
      have hh : pointWeight f (u ++ x :: v) (tmoves ds) (0, u.length) = f x.2 := by
        simp [pointWeight]
      rw [hh]
      ac_rfl

private theorem decoration_ok {I : Type*} {a : List (Letter I)}
    {R : List (TMove (Letter I))} {q : ℕ → ℕ × ℕ} {c : ℕ → ℕ}
    {ds : List (DTMove I)} (hq : ∀ j ∈ leftEnds₂ a R, OnStrand₂ a R j (q j))
    (hds : Decorates₂ a R q c ds) : DOk₂ a ds := by
  apply dOk₂_of_dotPts
  intro x hx
  obtain ⟨j, hj, hx⟩ := List.mem_flatMap.mp (hds.2.mem_iff.mp hx)
  have he : x = q j := (List.mem_replicate.mp hx).2
  rw [he, hds.1]
  exact (hq j hj).1

private theorem dot_weights {I M : Type*} [AddCommMonoid M]
    {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a b R) (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ a R, OnStrand₂ a R j (q j))
    (c : MatchingStrand a R → ℕ) (ds : List (DTMove I))
    (hds : Decorates₂ a R q (strandCounts c) ds) (f : I → M) :
    ((dotPts ds).map (pointWeight f a R)).sum =
      ∑ j, c j • f (matchingStrandColour a R j) := by
  classical
  have ht (j : MatchingStrand a R) :
      pointWeight f a R (q j) = f (matchingStrandColour a R j) := by
    unfold pointWeight
    rw [onStrand₂_colour hR j (hq j j.property)]
    rfl
  rw [(hds.2.map _).sum_eq]
  have sum_flat (s : List ℕ) (g : ℕ → List M) :
      (s.flatMap g).sum = (s.map fun x => (g x).sum).sum := by
    induction s with
    | nil => rfl
    | cons x s ih => simp only [List.flatMap_cons, List.sum_append, ih, List.map_cons,
        List.sum_cons]
  simp only [List.map_flatMap, List.map_replicate, sum_flat, List.sum_replicate]
  conv_lhs => rw [← List.attach_map_subtype_val (leftEnds₂ a R), List.map_map]
  change ((leftEnds₂ a R).attach.map fun j : MatchingStrand a R =>
    strandCounts c j.val • pointWeight f a R (q j.val)).sum = _
  simp only [strandCounts_apply, ht]
  have hu : (leftEnds₂ a R).attach.toFinset = Finset.univ := by ext j; simp
  rw [← List.sum_toFinset _ ((nodup_leftEnds₂ a R).attach), hu]

/-- The generator-table degree and parity of any valid mixed decoration are the
undecorated values plus its finite strand-labelled dot contributions. There is no
reducedness or assumed numerical-preservation premise. Existing decorations suffice;
bounded heights are required only when constructing a serializer, not for this identity. -/
theorem mixed_decorated_degree_parity {I X : Type*} [AddCommGroup X]
    (D : Datum I X) (sy : Symmetrizer D) (μ : X)
    {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a b R) (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ a R, OnStrand₂ a R j (q j))
    (c : MatchingStrand a R → ℕ) (ds : List (DTMove I))
    (hds : Decorates₂ a R q (strandCounts c) ds) :
    tableDegree D sy μ (dLay a ds) = tableDegree D sy μ (tLay a R) +
      ∑ j, (c j : ℤ) * (2 * sy.d (matchingStrandColour a R j)) ∧
    xpar D μ (dLay a ds) = xpar D μ (tLay a R) +
      ∑ j, (c j : ZMod 2) * D.parity (matchingStrandColour a R j) := by
  have hok := decoration_ok hq hds
  constructor
  · have h := decorated_weight (tableDegree D sy μ) (fun i => 2 * sy.d i)
      rfl (tableDegree_append D sy μ)
      (fun u x v => by rw [tableDegree_whisk, tableDegree_dot]) a ds hok
    rw [hds.1, dot_weights hR q hq c ds hds] at h
    simpa only [nsmul_eq_mul] using h
  · have h := decorated_weight (xpar D μ) D.parity
      rfl (xpar_append μ)
      (fun u x v => by rw [xpar_map_xwhL, xpar_dot]) a ds hok
    rw [hds.1, dot_weights hR q hq c ds hds] at h
    simpa only [nsmul_eq_mul] using h

end OddMath.SKM
