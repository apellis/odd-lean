import OddMath.SKM.Claim4Coefficients
import OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
import OddMath.SKM.BoundaryNormalizationExamples

/-! Both intersection cases on complete one-representative families at distinct
odd colours. The serializers include every natural finite-strand label. -/
noncomputable section
namespace OddMath.SKM.Claim4CoefficientsExamples
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators
open MixedCrossingLocalExamples
open CoveringQuantum CoveringQuantum.UDot.GenericTensor
open CoveringQuantum.Coefficients CoveringQuantum.UDot.GenericVerma.MixedGram
open CoveringQuantum.UDot.ContextualExchangeExamples

private theorem same_letter {I : Type*} {s : List (ℕ × Letter I)}
    (hl : Lettered flipL s) {i j : ℕ} (h : Same s i j) :
    (s[j]?).map Prod.snd = ((s[i]?).map Prod.snd).map flipL := by
  rcases lt_or_gt_of_ne h.ne with hij | hji
  · simpa only [Option.map_map] using hl i j h hij
  · have hh := congrArg (Option.map flipL) (hl j i h.symm hji)
    simpa only [Option.map_map, Function.comp_def, flipL_flipL] using hh.symm

private theorem iso_nodup_letters {I : Type*} {s t : List (ℕ × Letter I)}
    (hs : Valid s) (ht : Valid t) (hls : Lettered flipL s) (hlt : Lettered flipL t)
    (he : s.map Prod.snd = t.map Prod.snd) (hn : (s.map Prod.snd).Nodup) : Iso s t := by
  have forward {u v : List (ℕ × Letter I)} (hv : Valid v)
      (hlu : Lettered flipL u) (hlv : Lettered flipL v)
      (he : u.map Prod.snd = v.map Prod.snd) (hn : (v.map Prod.snd).Nodup)
      (i j : ℕ) (h : Same u i j) : Same v i j := by
    have hlen : u.length = v.length := by simpa using congrArg List.length he
    obtain ⟨k, hk, _⟩ := hv i (hlen ▸ h.lt_left)
    have h1 := same_letter hlu h
    have h2 := same_letter hlv hk
    simp only [← List.getElem?_map] at h1 h2
    rw [he] at h1
    have hj := h.lt_right
    have hjk : j = k := (List.Nodup.getElem?_inj (by simp only [List.length_map]; omega) hn).mp
      (h1.trans h2.symm)
    exact hjk ▸ hk
  exact ⟨he, fun i j => ⟨forward ht hls hlt he (he ▸ hn) i j,
    forward hs hlt hls he.symm hn i j⟩⟩

private def tail (k : Bool) : List (Letter Bool) :=
  if k then [(false, false), (true, true)] else [(true, true), (false, false)]
private def A (k : Bool) : List (Letter Bool) := (true, false) :: (false, true) :: tail k
private def B (k : Bool) : List (Letter Bool) := (false, true) :: (true, false) :: tail k
private def R (k : Bool) : List (TMove (Letter Bool)) :=
  if k then [.mv (.cross 0), .cap 1, .cap 0] else [.cap 1, .cap 0]
private def S (k : Bool) : List (TMove (Letter Bool)) :=
  if k then [.cap 1, .cap 0] else [.mv (.cross 0), .cap 1, .cap 0]
private def M (k : Bool) : Set (List (TMove (Letter Bool))) := {R k}
private def N (k : Bool) : Set (List (TMove (Letter Bool))) := {S k}
private abbrev T (k : Bool) := Σ V : {V // V ∈ M k}, MatchingStrand (A k) V.val → ℕ
private abbrev U (k : Bool) := Σ V : {V // V ∈ N k}, MatchingStrand (B k) V.val → ℕ

private theorem hm (k : Bool) : IsMatching₂ (A k) [] (R k) := by
  cases k
  · refine ⟨?_, rfl⟩
    refine ⟨⟨(4, (false, true)), (2, (true, true)), rfl, rfl, rfl, by decide⟩, ?_⟩
    exact ⟨⟨(6, (true, false)), (0, (false, false)), rfl, rfl, rfl, by decide⟩, trivial⟩
  · exact source_matching
private theorem hn (k : Bool) : IsMatching₂ (B k) [] (S k) := by
  cases k
  · refine ⟨⟨by change 5 < 8; decide, ?_⟩, rfl⟩
    refine ⟨⟨(6, (false, true)), (2, (true, true)), rfl, rfl, rfl, by decide⟩, ?_⟩
    exact ⟨⟨(4, (true, false)), (0, (false, false)), rfl, rfl, rfl, by decide⟩, trivial⟩
  · exact target_matching
private theorem rm (k : Bool) : StrictReduced₂ (A k) (R k) := by
  cases k
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([4, 6] : List ℕ).Nodup
    simp
  · exact source_reduced
private theorem rn (k : Bool) : StrictReduced₂ (B k) (S k) := by
  cases k
  · change (([s(6, 4)] : List (Sym2 ℕ)).Nodup ∧
      (∀ z ∈ ([s(6, 4)] : List (Sym2 ℕ)), ¬ z.IsDiag)) ∧ ([6, 4] : List ℕ).Nodup
    simp
  · exact target_reduced
private theorem hM (k : Bool) : ∀ V ∈ M k, IsMatching₂ (A k) [] V ∧ StrictReduced₂ (A k) V := by
  intro V hv
  obtain rfl := Set.mem_singleton_iff.mp hv
  exact ⟨hm k, rm k⟩
private theorem hN (k : Bool) : ∀ V ∈ N k, IsMatching₂ (B k) [] V ∧ StrictReduced₂ (B k) V := by
  intro V hv
  obtain rfl := Set.mem_singleton_iff.mp hv
  exact ⟨hn k, rn k⟩

private theorem hMrep (k : Bool) : ∀ V, IsMatching₂ (A k) [] V → StrictReduced₂ (A k) V →
    ∃ W ∈ M k, Iso (pairing₂ (A k) W) (pairing₂ (A k) V) := by
  intro V h _
  refine ⟨R k, Set.mem_singleton _, ?_⟩
  apply iso_nodup_letters (hm k).pairing_properties.1 h.pairing_properties.1
    (hm k).pairing_properties.2.1 h.pairing_properties.2.1
    ((hm k).pairing_properties.2.2.trans h.pairing_properties.2.2.symm)
  rw [(hm k).pairing_properties.2.2]
  cases k <;> decide
private theorem hNrep (k : Bool) : ∀ V, IsMatching₂ (B k) [] V → StrictReduced₂ (B k) V →
    ∃ W ∈ N k, Iso (pairing₂ (B k) W) (pairing₂ (B k) V) := by
  intro V h _
  refine ⟨S k, Set.mem_singleton _, ?_⟩
  apply iso_nodup_letters (hn k).pairing_properties.1 h.pairing_properties.1
    (hn k).pairing_properties.2.1 h.pairing_properties.2.1
    ((hn k).pairing_properties.2.2.trans h.pairing_properties.2.2.symm)
  rw [(hn k).pairing_properties.2.2]
  cases k <;> decide

/-- Both branches have the asserted intersection geometry. -/
theorem intersection_cases : Ilv (pairing₂ (A true) (R true)) 2 ∧
    ¬ Ilv (pairing₂ (A false) (R false)) 2 :=
  ⟨BoundaryNormalizationExamples.existing_intersection,
    BoundaryNormalizationExamples.no_existing_intersection⟩

private theorem endsR (k : Bool) : leftEnds₂ (A k) (R k) = [0, 1] := by
  classical
  cases k
  · change (List.range 4).filter (fun j => decide (IsLeftEnd
      [(6, (true, false)), (4, (false, true)), (4, (true, true)), (6, (false, false))] j)) = [0, 1]
    norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
    exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩
  · change (List.range 4).filter (fun j => decide (IsLeftEnd
      [(4, (false, true)), (6, (true, false)), (4, (true, true)), (6, (false, false))] j)) = [0, 1]
    norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
    exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩

private theorem endsS (k : Bool) : leftEnds₂ (B k) (S k) = [0, 1] := by
  classical
  cases k
  · change (List.range 4).filter (fun j => decide (IsLeftEnd
      [(4, (true, false)), (6, (false, true)), (4, (false, false)), (6, (true, true))] j)) = [0, 1]
    norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
    exact ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩
  · change (List.range 4).filter (fun j => decide (IsLeftEnd
      [(6, (false, true)), (4, (true, false)), (4, (false, false)), (6, (true, true))] j)) = [0, 1]
    norm_num [List.range_succ, IsLeftEnd, Same, idAt, Nat.lt_succ_iff_lt_or_eq]
    exact ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩

private def q (k : Bool) (_ : {V // V ∈ M k}) (j : ℕ) : ℕ × ℕ := (0, 3 - j)
private def r (k : Bool) (_ : {V // V ∈ N k}) (j : ℕ) : ℕ × ℕ := (0, 3 - j)
private theorem hq (k : Bool) : ∀ V j, j ∈ leftEnds₂ (A k) V.val →
    (q k V j).1 ≤ V.val.length ∧ OnStrand₂ (A k) V.val j (q k V j) := by
  rintro ⟨V, hv⟩ j hj
  obtain rfl := Set.mem_singleton_iff.mp hv
  simp only [endsR, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> cases k <;> dsimp only [q, r] <;> unfold OnStrand₂ <;> decide
private theorem hr (k : Bool) : ∀ V j, j ∈ leftEnds₂ (B k) V.val →
    (r k V j).1 ≤ V.val.length ∧ OnStrand₂ (B k) V.val j (r k V j) := by
  rintro ⟨V, hv⟩ j hj
  obtain rfl := Set.mem_singleton_iff.mp hv
  simp only [endsS, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl <;> cases k <;> dsimp only [q, r] <;> unfold OnStrand₂ <;> decide

private def τ (k : Bool) (V : {V // V ∈ M k}) (c : MatchingStrand (A k) V.val → ℕ) : List (DTMove Bool) :=
  (exists_decorates₂_of_bounded_points (A k) V.val (q k V)
    (fun j hj => (hq k V j hj).2) (fun j hj => (hq k V j hj).1) c).choose
private theorem hτ (k : Bool) (V : {V // V ∈ M k}) (c : MatchingStrand (A k) V.val → ℕ) :
    Decorates₂ (A k) V.val (q k V) (strandCounts c) (τ k V c) :=
  (exists_decorates₂_of_bounded_points (A k) V.val (q k V)
    (fun j hj => (hq k V j hj).2) (fun j hj => (hq k V j hj).1) c).choose_spec.1
private def υ (k : Bool) (V : {V // V ∈ N k}) (c : MatchingStrand (B k) V.val → ℕ) : List (DTMove Bool) :=
  (exists_decorates₂_of_bounded_points (B k) V.val (r k V)
    (fun j hj => (hr k V j hj).2) (fun j hj => (hr k V j hj).1) c).choose
private theorem hυ (k : Bool) (V : {V // V ∈ N k}) (c : MatchingStrand (B k) V.val → ℕ) :
    Decorates₂ (B k) V.val (r k V) (strandCounts c) (υ k V c) :=
  (exists_decorates₂_of_bounded_points (B k) V.val (r k V)
    (fun j hj => (hr k V j hj).2) (fun j hj => (hr k V j hj).1) c).choose_spec.1

/-- An actual application to both complete families, with independently fixed
valid serializers for all natural counts; the equivalence precedes all gradings. -/
private theorem graphical_families (k : Bool) : ∃ F : T k ≃ U k,
    ∀ (D : Datum Bool (Bool → ℤ)) (sy : Symmetrizer D) (μ : Bool → ℤ),
    let d := fun t : T k => tableDegree D sy μ (dLay (A k) (τ k t.1 t.2))
    let e := fun u : U k => tableDegree D sy μ (dLay (B k) (υ k u.1 u.2))
    let p := fun t : T k => xpar D μ (dLay (A k) (τ k t.1 t.2))
    let p' := fun u : U k => xpar D μ (dLay (B k) (υ k u.1 u.2))
    ∃ (hf : ∀ z : ℤ, Set.Finite {t | d t = z}) (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
      (∀ t, e (F t) = d t ∧ p' (F t) = p t + D.parity false * D.parity true) ∧
      (∀ z, Nonempty ({t // d t = z} ≃ {u // e u = z})) ∧
      ∀ σ : ℚ, σ ^ 2 = 1 → ∀ z : ℤ,
        (∑ u ∈ (hg z).toFinset, σ ^ (p' u).val) =
          σ ^ (D.parity false * D.parity true).val * ∑ t ∈ (hf z).toFinset, σ ^ (p t).val ∧
        (∑ t ∈ (hf z).toFinset, σ ^ (p t).val) =
          σ ^ (D.parity false * D.parity true).val * ∑ u ∈ (hg z).toFinset, σ ^ (p' u).val := by
  exact opposite_boundary_labelled_family_coefficients (a := []) (b := tail k)
    colours_distinct (hM k) (hN k) (q k) (r k)
    (fun V j hj => (hq k V j hj).2) (fun V j hj => (hr k V j hj).2)
    (τ k) (υ k) (hτ k) (hυ k) (hMrep k) (hNrep k)
    (fun _ hV _ hW _ => (Set.mem_singleton_iff.mp hV).trans (Set.mem_singleton_iff.mp hW).symm)
    (fun _ hV _ hW _ => (Set.mem_singleton_iff.mp hV).trans (Set.mem_singleton_iff.mp hW).symm)

private abbrev D := twoOddDatum.toSKM
private abbrev sy := twoOddDatum.skmSymmetrizer
private def d (k : Bool) (t : T k) : ℤ := tableDegree D sy 0 (dLay (A k) (τ k t.1 t.2))
private def e (k : Bool) (u : U k) : ℤ := tableDegree D sy 0 (dLay (B k) (υ k u.1 u.2))
private def p (k : Bool) (t : T k) : ZMod 2 := xpar D 0 (dLay (A k) (τ k t.1 t.2))
private def p' (k : Bool) (u : U k) : ZMod 2 := xpar D 0 (dLay (B k) (υ k u.1 u.2))
private def jf (k : Bool) : MatchingStrand (A k) (R k) :=
  ⟨if k then 1 else 0, by rw [endsR]; cases k <;> simp⟩
private def jt (k : Bool) : MatchingStrand (A k) (R k) :=
  ⟨if k then 0 else 1, by rw [endsR]; cases k <;> simp⟩
private def oneDot (k : Bool) : T k :=
  ⟨⟨R k, Set.mem_singleton _⟩, fun j => if j.val = (jf k).val then 1 else 0⟩

private theorem base_values (k : Bool) :
    tableDegree D sy 0 (tLay (A k) (R k)) = 2 ∧
    xpar D 0 (tLay (A k) (R k)) = if k then 0 else 1 := by
  cases k <;>
    norm_num [A, R, tail, tLay, tmLay, tLet, moveLay, chStep, lstep, swapAt, xCrL, xCapL, sigmaL, up, dn,
      tableDegree, xpar, xlpar, ofL, gdeg, Shape.parity, xwhL, wt, sh, ipar,
      D, sy, twoOddDatum, RootDatum.toSKM, RootDatum.skmSymmetrizer,
      Datum.h, Datum.α, Datum.d]
  all_goals rfl

private theorem count_grading (k : Bool) (c : MatchingStrand (A k) (R k) → ℕ) :
    d k ⟨⟨R k, Set.mem_singleton _⟩, c⟩ = 2 + 2 * (c (jf k) : ℤ) + 2 * (c (jt k) : ℤ) ∧
    p k ⟨⟨R k, Set.mem_singleton _⟩, c⟩ = (if k then 0 else 1) +
      (c (jf k) : ZMod 2) + (c (jt k) : ZMod 2) := by
  classical
  have hu : (Finset.univ : Finset (MatchingStrand (A k) (R k))) = {jf k, jt k} := by
    ext j
    have hj := j.property
    simp only [endsR, List.mem_cons, List.not_mem_nil, or_false] at hj
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    cases k <;> rcases hj with hj | hj
    · exact Or.inl (Subtype.ext hj)
    · exact Or.inr (Subtype.ext hj)
    · exact Or.inr (Subtype.ext hj)
    · exact Or.inl (Subtype.ext hj)
  have hne : jf k ≠ jt k := by
    intro h
    have hh := congrArg Subtype.val h
    cases k <;> cases hh
  have cf : matchingStrandColour (A k) (R k) (jf k) = false := by cases k <;> rfl
  have ct : matchingStrandColour (A k) (R k) (jt k) = true := by cases k <;> rfl
  have h := mixed_decorated_degree_parity D sy 0 (hm k)
    (q k ⟨R k, Set.mem_singleton _⟩) (fun j hj => (hq k _ j hj).2) c _ (hτ k ⟨R k, Set.mem_singleton _⟩ c)
  simp only [hu, Finset.sum_insert (show jf k ∉ ({jt k} : Finset _) by simpa using hne), Finset.sum_singleton,
    cf, ct, (base_values k).1, (base_values k).2] at h
  constructor
  · have hd := h.1
    change d k ⟨⟨R k, Set.mem_singleton _⟩, c⟩ = 2 + ((c (jf k) : ℤ) * 2 + (c (jt k) : ℤ) * 2) at hd
    linarith
  · simpa only [p, D, twoOddDatum, RootDatum.toSKM, mul_one, add_assoc] using h.2


private def noDot (k : Bool) : T k := ⟨⟨R k, Set.mem_singleton _⟩, fun _ => 0⟩

private theorem noDot_values (k : Bool) : d k (noDot k) = 2 ∧
    p k (noDot k) = if k then 0 else 1 := by
  have h := count_grading k (noDot k).2
  simpa only [noDot, Nat.cast_zero, mul_zero, add_zero] using h

private theorem oneDot_values (k : Bool) : d k (oneDot k) = 4 ∧
    p k (oneDot k) = if k then 1 else 0 := by
  have h := count_grading k (oneDot k).2
  cases k <;> norm_num [oneDot, jf, jt] at h ⊢ <;> exact h

private theorem fiber_two (k : Bool) : {t : T k | d k t = 2} = {noDot k} := by
  ext t
  constructor
  · rcases t with ⟨⟨V, hV⟩, c⟩
    obtain rfl := Set.mem_singleton_iff.mp hV
    intro hd
    have h := (count_grading k c).1
    change d k ⟨⟨R k, hV⟩, c⟩ = 2 at hd
    have hf : c (jf k) = 0 := by omega
    have ht : c (jt k) = 0 := by omega
    have hc : c = (noDot k).2 := by
      funext j
      have hj := j.property
      simp only [endsR, List.mem_cons, List.not_mem_nil, or_false] at hj
      cases k <;> rcases hj with hj | hj
      · have he : j = jf false := Subtype.ext hj
        rw [he, hf]
        rfl
      · have he : j = jt false := Subtype.ext hj
        rw [he, ht]
        rfl
      · have he : j = jt true := Subtype.ext hj
        rw [he, ht]
        rfl
      · have he : j = jf true := Subtype.ext hj
        rw [he, hf]
        rfl
    subst c
    exact Set.mem_singleton _
  · rintro (rfl : t = noDot k)
    exact (noDot_values k).1

/-- Both intersection cases invoke the coefficientwise Claim 4 theorem with
complete unique families and serializers valid for every finite strand-label vector.
The datum has two odd roots with symmetrizers one, so it is bar consistent. -/
theorem two_odd_coeff_iff (k : Bool) : ∃ F : T k ≃ U k,
    ∃ (hf : ∀ z : ℤ, Set.Finite {t : T k | d k t = z})
      (hg : ∀ z : ℤ, Set.Finite {u : U k | e k u = z}),
      (∀ t, e k (F t) = d k t ∧ p' k (F t) = p k t + 1) ∧
      ∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
      ((∀ z : ℤ,
        (signLaurent σ hσ (sesquilinearForm twoOddDatum twoOdd_barConsistent
          (algebraWord twoOddDatum 0 (A k)) (algebraWord twoOddDatum 0 []))).coeff z =
            ∑ t ∈ (hf z).toFinset, σ ^ (p k t).val) ↔
       (∀ z : ℤ,
        (signLaurent σ hσ (sesquilinearForm twoOddDatum twoOdd_barConsistent
          (algebraWord twoOddDatum 0 (B k)) (algebraWord twoOddDatum 0 []))).coeff z =
            ∑ u ∈ (hg z).toFinset, σ ^ (p' k u).val)) := by
  obtain ⟨F, hF⟩ := opposite_boundary_labelled_form_coeff_iff (X := Bool → ℤ)
    (a := []) (b := tail k) colours_distinct (hM k) (hN k) (q k) (r k)
    (fun V j hj => (hq k V j hj).2) (fun V j hj => (hr k V j hj).2)
    (τ k) (υ k) (hτ k) (hυ k) (hMrep k) (hNrep k)
    (fun _ hV _ hW _ => (Set.mem_singleton_iff.mp hV).trans (Set.mem_singleton_iff.mp hW).symm)
    (fun _ hV _ hW _ => (Set.mem_singleton_iff.mp hV).trans (Set.mem_singleton_iff.mp hW).symm)
  obtain ⟨hf, hg, hgrading, _, hiff⟩ := hF twoOddDatum twoOdd_barConsistent 0
  exact ⟨F, hf, hg, hgrading, hiff⟩

/-- The same finite fibers used by the iff have populated degree two and a nonzero
dot at degree four. At π=-1 the degree-two source and target sums are different;
at π=1 both sums are one. This is not an equivalence of reflexive propositions. -/
theorem populated_iff (k : Bool) :
    ∃ (hf : ∀ z : ℤ, Set.Finite {t : T k | d k t = z})
      (hg : ∀ z : ℤ, Set.Finite {u : U k | e k u = z}),
      (∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
        ((∀ z : ℤ,
          (signLaurent σ hσ (sesquilinearForm twoOddDatum twoOdd_barConsistent
            (algebraWord twoOddDatum 0 (A k)) (algebraWord twoOddDatum 0 []))).coeff z =
              ∑ t ∈ (hf z).toFinset, σ ^ (p k t).val) ↔
         (∀ z : ℤ,
          (signLaurent σ hσ (sesquilinearForm twoOddDatum twoOdd_barConsistent
            (algebraWord twoOddDatum 0 (B k)) (algebraWord twoOddDatum 0 []))).coeff z =
              ∑ u ∈ (hg z).toFinset, σ ^ (p' k u).val))) ∧
      (∃ t, d k t = 4 ∧ ∃ j, t.2 j ≠ 0) ∧
      (∃ t, d k t = 2) ∧ (∃ u, e k u = 2) ∧
      (∀ (σ : ℚ), σ ^ 2 = 1 →
        (∑ t ∈ (hf 2).toFinset, σ ^ (p k t).val) = σ ^ (if k then 0 else 1) ∧
        (∑ u ∈ (hg 2).toFinset, σ ^ (p' k u).val) = σ * σ ^ (if k then 0 else 1)) ∧
      (∑ t ∈ (hf 2).toFinset, (-1 : ℚ) ^ (p k t).val) ≠
        ∑ u ∈ (hg 2).toFinset, (-1 : ℚ) ^ (p' k u).val := by
  classical
  obtain ⟨F, hf, hg, hgrading, hiff⟩ := two_odd_coeff_iff k
  have hc (σ : ℚ) : (∑ t ∈ (hf 2).toFinset, σ ^ (p k t).val) = σ ^ (if k then 0 else 1) := by
    have he : (hf 2).toFinset = {noDot k} := by
      ext t
      rw [Set.Finite.mem_toFinset]
      rw [fiber_two]
      simp
    rw [he, Finset.sum_singleton, (noDot_values k).2]
    cases k <;> rfl
  have ht (σ : ℚ) (hσ : σ ^ 2 = 1) :
      (∑ u ∈ (hg 2).toFinset, σ ^ (p' k u).val) = σ * σ ^ (if k then 0 else 1) := by
    obtain ⟨_, hG⟩ := graphical_families k
    obtain ⟨_, _, _, _, hs⟩ := hG D sy 0
    have he := (hs σ hσ 2).1
    change (∑ u ∈ (hg 2).toFinset, σ ^ (p' k u).val) =
      σ ^ (1 : ZMod 2).val * ∑ t ∈ (hf 2).toFinset, σ ^ (p k t).val at he
    simpa only [ZMod.val_one, pow_one, hc σ] using he
  refine ⟨hf, hg, hiff, ⟨oneDot k, (oneDot_values k).1, jf k, ?_⟩,
    ⟨noDot k, (noDot_values k).1⟩,
    ⟨F (noDot k), (hgrading _).1.trans (noDot_values k).1⟩,
    fun σ hσ => ⟨hc σ, ht σ hσ⟩, ?_⟩
  · simp [oneDot]
  · rw [hc (-1), ht (-1) (by norm_num)]
    cases k <;> norm_num

end OddMath.SKM.Claim4CoefficientsExamples
