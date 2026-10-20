/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.Claim5Coefficients
import OddMath.CoveringQuantum.UDot.ContextualExchangeExamples
import OddMath.SKM.MixedCrossingLocalExamples

/-! # Concrete Claim 5 coefficient comparisons

BE2, arXiv:1701.04133v2, Theorem 10.3 Claim 5 on complete decorated
families, with all shorter-word coefficient premises discharged. -/
noncomputable section
namespace OddMath.SKM.Claim5CoefficientsExamples
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators LaurentSeries
open CoveringQuantum.PreF.DotSeries
open MixedCrossingLocalExamples (oddDatum oddSymmetrizer)

private def a (k j : Bool) : List (Letter Bool) := if k then [(true, j)] else []
private def b (k j : Bool) : List (Letter Bool) := if k then [(false, j)] else []
private def A (ε k j : Bool) := a k j ++ (ε, false) :: (!ε, false) :: b k j
private def R (k : Bool) : List (TMove (Letter Bool)) :=
  if k then [.cap 1, .cap 0] else [.cap 0]
private def S (k : Bool) : List (TMove (Letter Bool)) := if k then [.cap 0] else []

private theorem matching (ε k j : Bool) : IsMatching₂ (A ε k j) [] (R k) := by
  cases ε <;> cases k
  · exact ⟨⟨⟨(2, (false, false)), (0, (true, false)),
      rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩
  · refine ⟨⟨?_, ?_⟩, rfl⟩
    · exact ⟨(4, (false, false)), (2, (true, false)), rfl, rfl, rfl, by decide⟩
    · exact ⟨⟨(6, (true, j)), (0, (false, j)), rfl, rfl, rfl,
        by change (6 : ℕ) ≠ 0; decide⟩, trivial⟩
  · exact ⟨⟨⟨(2, (true, false)), (0, (false, false)),
      rfl, rfl, rfl, by decide⟩, trivial⟩, rfl⟩
  · refine ⟨⟨?_, ?_⟩, rfl⟩
    · exact ⟨(4, (true, false)), (2, (false, false)), rfl, rfl, rfl, by decide⟩
    · exact ⟨⟨(6, (true, j)), (0, (false, j)), rfl, rfl, rfl,
        by change (6 : ℕ) ≠ 0; decide⟩, trivial⟩

private theorem shorter_matching (k j : Bool) : IsMatching₂ (a k j ++ b k j) [] (S k) := by
  cases k
  · exact ⟨trivial, rfl⟩
  · exact ⟨⟨⟨(2, (true, j)), (0, (false, j)), rfl, rfl, rfl,
      by change (2 : ℕ) ≠ 0; decide⟩, trivial⟩, rfl⟩

private theorem cap (ε k j : Bool) :
    Same (pairing₂ (A ε k j) (R k)) (b k j).length ((b k j).length + 1) := by
  cases ε <;> cases k <;> cases j <;> unfold Same idAt <;> decide

private def q (k : Bool) (t : ℕ) : ℕ × ℕ :=
  if k then if t = 0 then (1, 0) else (0, 1) else (0, 0)
private def r (_ : ℕ) : ℕ × ℕ := (0, 1)

private theorem points (ε k j : Bool) (t : ℕ) (ht : t ∈ leftEnds₂ (A ε k j) (R k)) :
    (q k t).1 ≤ (R k).length ∧ OnStrand₂ (A ε k j) (R k) t (q k t) := by
  have h := mem_leftEnds₂.mp ht
  have hb := h.1
  cases k
  · change t < 2 at hb
    interval_cases t
    · cases ε <;> cases j <;> constructor
      all_goals first | decide | unfold OnStrand₂; decide
    · exact (h.2 ⟨0, by decide, (cap ε false j).symm⟩).elim
  · change t < 4 at hb
    interval_cases t
    · cases ε <;> cases j <;> constructor
      all_goals first | decide | unfold OnStrand₂; decide
    · cases ε <;> cases j <;> constructor
      all_goals first | decide | unfold OnStrand₂; decide
    · exact (h.2 ⟨1, by decide, (cap ε true j).symm⟩).elim
    · apply False.elim
      apply h.2
      refine ⟨0, by decide, ?_⟩
      cases ε <;> cases j <;> unfold Same idAt <;> decide

private theorem shorter_points (k j : Bool) (t : ℕ)
    (ht : t ∈ leftEnds₂ (a k j ++ b k j) (S k)) :
    (r t).1 ≤ (S k).length ∧ OnStrand₂ (a k j ++ b k j) (S k) t (r t) := by
  have h := mem_leftEnds₂.mp ht
  have hb := h.1
  cases k
  · change t < 0 at hb
    omega
  · change t < 2 at hb
    interval_cases t
    · cases j <;> constructor
      all_goals first | decide | unfold OnStrand₂; decide
    · apply False.elim
      apply h.2
      refine ⟨0, by decide, ?_⟩
      cases j <;> unfold Same idAt <;> decide

private def υ (k j : Bool) (c : MatchingStrand (a k j ++ b k j) (S k) → ℕ) :
    List (DTMove Bool) :=
  (exists_decorates₂_of_bounded_points (a k j ++ b k j) (S k) r
    (fun t ht => (shorter_points k j t ht).2)
    (fun t ht => (shorter_points k j t ht).1) c).choose

private theorem υ_valid (k j : Bool) (c : MatchingStrand (a k j ++ b k j) (S k) → ℕ) :
    Decorates₂ (a k j ++ b k j) (S k) r (strandCounts c) (υ k j c) :=
  (exists_decorates₂_of_bounded_points (a k j ++ b k j) (S k) r
    (fun t ht => (shorter_points k j t ht).2)
    (fun t ht => (shorter_points k j t ht).1) c).choose_spec.1

private def shortStrand (j : Bool) : MatchingStrand (a true j ++ b true j) (S true) :=
  ⟨0, mem_leftEnds₂.mpr ⟨by change 0 < 2; decide, by simp⟩⟩

private theorem shortStrand_unique (j : Bool)
    (s : MatchingStrand (a true j ++ b true j) (S true)) : s = shortStrand j := by
  apply Subtype.ext
  have h := mem_leftEnds₂.mp s.property
  have hb := h.1
  change s.val < 2 at hb
  have hs : s.val ≠ 1 := by
    intro he
    apply h.2
    refine ⟨0, by omega, ?_⟩
    rw [he]
    cases j <;> unfold Same idAt <;> decide
  change s.val = 0
  omega

private theorem shorter_values (m : ℕ) :
    tableDegree oddDatum oddSymmetrizer 0
      (dLay (a true true ++ b true true) (υ true true (fun _ => m))) = 2 + 4 * m ∧
    xpar oddDatum 0
      (dLay (a true true ++ b true true) (υ true true (fun _ => m))) = m := by
  classical
  have hs {V : Type} [AddCommMonoid V]
      (f : MatchingStrand (a true true ++ b true true) (S true) → V) :
      ∑ j, f j = f (shortStrand true) := by
    apply Finset.sum_eq_single (shortStrand true)
    · intro j _ hj
      exact (hj (shortStrand_unique true j)).elim
    · simp
  obtain ⟨hd, hp⟩ := mixed_decorated_degree_parity oddDatum oddSymmetrizer 0
    (shorter_matching true true) r (fun t ht => (shorter_points true true t ht).2)
    (fun _ => m) _ (υ_valid true true (fun _ => m))
  rw [hs] at hd hp
  change _ = (2 : ℤ) + m * (2 * 2) at hd
  change _ = (0 : ZMod 2) + m * 1 at hp
  exact ⟨by simpa only [show (2 : ℤ) * 2 = 4 from rfl, mul_comm] using hd,
    by simpa only [zero_add, mul_one] using hp⟩
private def M (k : Bool) : Set (List (TMove (Letter Bool))) := {R k}
private def N (k : Bool) : Set (List (TMove (Letter Bool))) := {S k}

private theorem reducedM (ε k : Bool) : StrictReduced₂ (A ε k true) (R k) := by
  cases k
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([2] : List ℕ).Nodup
    simp
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([4, 6] : List ℕ).Nodup
    simp

private theorem reducedN (k : Bool) : StrictReduced₂ (a k true ++ b k true) (S k) := by
  cases k
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([] : List ℕ).Nodup
    simp
  · change (([] : List (Sym2 ℕ)).Nodup ∧ ∀ z ∈ ([] : List (Sym2 ℕ)), ¬ z.IsDiag) ∧
      ([2] : List ℕ).Nodup
    simp

private theorem same_letter {s : List (ℕ × Letter Bool)}
    (hl : Lettered flipL s) {i j : ℕ} (h : Same s i j) :
    (s[j]?).map Prod.snd = ((s[i]?).map Prod.snd).map flipL := by
  rcases lt_or_gt_of_ne h.ne with hij | hji
  · simpa only [Option.map_map] using hl i j h hij
  · have hh := congrArg (Option.map flipL) (hl j i h.symm hji)
    simpa only [Option.map_map, Function.comp_def, flipL_flipL] using hh.symm

private theorem iso_nodup_letters {s t : List (ℕ × Letter Bool)}
    (hs : Valid s) (ht : Valid t) (hls : Lettered flipL s) (hlt : Lettered flipL t)
    (he : s.map Prod.snd = t.map Prod.snd) (hn : (s.map Prod.snd).Nodup) : Iso s t := by
  have forward {u v : List (ℕ × Letter Bool)} (hv : Valid v)
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

private theorem hM (ε k : Bool) : ∀ V ∈ M k,
    IsMatching₂ (A ε k true) [] V ∧ StrictReduced₂ (A ε k true) V := by
  intro V hv
  obtain rfl := Set.mem_singleton_iff.mp hv
  exact ⟨matching ε k true, reducedM ε k⟩

private theorem hN (k : Bool) : ∀ V ∈ N k,
    IsMatching₂ (a k true ++ b k true) [] V ∧ StrictReduced₂ (a k true ++ b k true) V := by
  intro V hv
  obtain rfl := Set.mem_singleton_iff.mp hv
  exact ⟨shorter_matching k true, reducedN k⟩

private theorem hMrep (ε k : Bool) : ∀ V, IsMatching₂ (A ε k true) [] V →
    StrictReduced₂ (A ε k true) V →
    ∃ W ∈ M k, Iso (pairing₂ (A ε k true) W) (pairing₂ (A ε k true) V) := by
  intro V h _
  refine ⟨R k, Set.mem_singleton _, ?_⟩
  apply iso_nodup_letters (matching ε k true).pairing_properties.1 h.pairing_properties.1
    (matching ε k true).pairing_properties.2.1 h.pairing_properties.2.1
    ((matching ε k true).pairing_properties.2.2.trans h.pairing_properties.2.2.symm)
  rw [(matching ε k true).pairing_properties.2.2]
  cases ε <;> cases k <;> decide

private theorem hNrep (k : Bool) : ∀ V, IsMatching₂ (a k true ++ b k true) [] V →
    StrictReduced₂ (a k true ++ b k true) V →
    ∃ W ∈ N k, Iso (pairing₂ (a k true ++ b k true) W) (pairing₂ (a k true ++ b k true) V) := by
  intro V h _
  refine ⟨S k, Set.mem_singleton _, ?_⟩
  apply iso_nodup_letters (shorter_matching k true).pairing_properties.1 h.pairing_properties.1
    (shorter_matching k true).pairing_properties.2.1 h.pairing_properties.2.1
    ((shorter_matching k true).pairing_properties.2.2.trans h.pairing_properties.2.2.symm)
  rw [(shorter_matching k true).pairing_properties.2.2]
  cases k <;> decide

private def C (ε k : Bool) : Set (List (TMove (Letter Bool))) :=
  {V | V ∈ M k ∧ Same (pairing₂ (A ε k true) V) (b k true).length ((b k true).length + 1)}

private theorem family_points (ε k : Bool) (V : C ε k) (t : ℕ)
    (ht : t ∈ leftEnds₂ (A ε k true) V.val) :
    (q k t).1 ≤ V.val.length ∧ OnStrand₂ (A ε k true) V.val t (q k t) := by
  rcases V with ⟨V, hV, _⟩
  obtain rfl := Set.mem_singleton_iff.mp hV
  exact points ε k true t ht

private theorem shorter_family_points (k : Bool) (V : N k) (t : ℕ)
    (ht : t ∈ leftEnds₂ (a k true ++ b k true) V.val) :
    (r t).1 ≤ V.val.length ∧ OnStrand₂ (a k true ++ b k true) V.val t (r t) := by
  rcases V with ⟨V, hV⟩
  obtain rfl := Set.mem_singleton_iff.mp hV
  exact shorter_points k true t ht

private def φ (ε k : Bool) (V : C ε k) (c : MatchingStrand (A ε k true) V.val → ℕ) :
    List (DTMove Bool) :=
  (exists_decorates₂_of_bounded_points (A ε k true) V.val (q k)
    (fun t ht => (family_points ε k V t ht).2)
    (fun t ht => (family_points ε k V t ht).1) c).choose

private theorem φ_valid (ε k : Bool) (V : C ε k)
    (c : MatchingStrand (A ε k true) V.val → ℕ) :
    Decorates₂ (A ε k true) V.val (q k) (strandCounts c) (φ ε k V c) :=
  (exists_decorates₂_of_bounded_points (A ε k true) V.val (q k)
    (fun t ht => (family_points ε k V t ht).2)
    (fun t ht => (family_points ε k V t ht).1) c).choose_spec.1

private def ψ (k : Bool) (V : N k) (c : MatchingStrand (a k true ++ b k true) V.val → ℕ) :
    List (DTMove Bool) :=
  (exists_decorates₂_of_bounded_points (a k true ++ b k true) V.val r
    (fun t ht => (shorter_family_points k V t ht).2)
    (fun t ht => (shorter_family_points k V t ht).1) c).choose

private theorem ψ_valid (k : Bool) (V : N k)
    (c : MatchingStrand (a k true ++ b k true) V.val → ℕ) :
    Decorates₂ (a k true ++ b k true) V.val r (strandCounts c) (ψ k V c) :=
  (exists_decorates₂_of_bounded_points (a k true ++ b k true) V.val r
    (fun t ht => (shorter_family_points k V t ht).2)
    (fun t ht => (shorter_family_points k V t ht).1) c).choose_spec.1

private abbrev K := Σ V : N true, MatchingStrand (a true true ++ b true true) V.val → ℕ
private def label (n : ℕ) : K := ⟨⟨S true, rfl⟩, fun _ => n⟩
private def degree (u : K) : ℤ :=
  tableDegree oddDatum oddSymmetrizer 0 (dLay (a true true ++ b true true) (ψ true u.1 u.2))
private def parity (u : K) : ZMod 2 :=
  xpar oddDatum 0 (dLay (a true true ++ b true true) (ψ true u.1 u.2))

private theorem label_values (n : ℕ) : degree (label n) = 2 + 4 * n ∧
    parity (label n) = n := shorter_values n

private theorem exists_label (u : K) : ∃ n, u = label n := by
  rcases u with ⟨⟨V, hV⟩, c⟩
  obtain rfl := Set.mem_singleton_iff.mp hV
  refine ⟨c (shortStrand true), ?_⟩
  congr 1
  funext s
  rw [shortStrand_unique true s]

/-- The shorter one-strand series is explicitly shifted by degree two;
its dot increment is four, so the symmetrizer-two strand is retained. -/
def shorterSeries (σ : ℚ) : LaurentSeries ℚ :=
  HahnSeries.single 2 1 * (factor σ 4 (by decide) : LaurentSeries ℚ)

private theorem shorter_coefficients (σ : ℚ) (hσ : σ ^ 2 = 1)
    (he : ∀ k : ℤ, Set.Finite {u : K | degree u = k}) (k : ℤ) :
    (∑ u ∈ (he k).toFinset, σ ^ (parity u).val) = (shorterSeries σ).coeff k := by
  classical
  rw [shorterSeries, HahnSeries.coeff_single_mul, one_mul]
  by_cases hk : ∃ n : ℕ, k = 2 + 4 * n
  · obtain ⟨n, rfl⟩ := hk
    have hf : (he (2 + 4 * n)).toFinset = {label n} := by
      ext u
      rw [Set.Finite.mem_toFinset, Finset.mem_singleton]
      obtain ⟨m, rfl⟩ := exists_label u
      change degree (label m) = 2 + 4 * n ↔ label m = label n
      constructor
      · intro h
        rw [(label_values m).1] at h
        have : m = n := by omega
        rw [this]
      · rintro h
        rw [h, (label_values n).1]
    rw [hf, Finset.sum_singleton, (label_values n).2]
    have hpar := parity_pow_nat_mul σ hσ n 1
    simp only [mul_one, ZMod.val_one, pow_one] at hpar
    rw [hpar, show (2 : ℤ) + 4 * n - 2 = 4 * n by ring]
    exact (laurent_factor_coeff σ 4 (by decide) n).symm
  · have hf : (he k).toFinset = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      obtain ⟨n, rfl⟩ := exists_label u
      have h := (he k).mem_toFinset.mp hu
      exact hk ⟨n, h.symm.trans (label_values n).1⟩
    rw [hf, Finset.sum_empty]
    symm
    by_contra hc
    obtain ⟨n, hn⟩ := laurent_factor_support σ 4 (by decide) (k - 2) hc
    exact hk ⟨n, by omega⟩

private def fullCap (ε k : Bool) (V : M k) : C ε k :=
  ⟨V.val, V.property, by
    obtain h := Set.mem_singleton_iff.mp V.property
    rw [h]
    exact cap ε k true⟩

/-- Complete full family, with its serializer fixed before restricting to caps. -/
def fullFamily (ε k : Bool) : CoefficientFamily (A ε k true) where
  members := M k
  matching := hM ε k
  unique _ hV _ hW _ := (Set.mem_singleton_iff.mp hV).trans (Set.mem_singleton_iff.mp hW).symm
  points _ := q k
  onStrand V t ht := (family_points ε k (fullCap ε k V) t ht).2
  serialize V := φ ε k (fullCap ε k V)
  decorates V := φ_valid ε k (fullCap ε k V)

private theorem full_complete (ε k : Bool) : (fullFamily ε k).Complete := hMrep ε k

/-- Shorter complete family with an independently valid serializer. -/
def shortFamily (k : Bool) : CoefficientFamily (a k true ++ b k true) where
  members := N k
  matching := hN k
  unique _ hV _ hW _ := (Set.mem_singleton_iff.mp hV).trans (Set.mem_singleton_iff.mp hW).symm
  points _ := r
  onStrand V t ht := (shorter_family_points k V t ht).2
  serialize := ψ k
  decorates := ψ_valid k

private theorem short_complete (k : Bool) : (shortFamily k).Complete := hNrep k

/-- The whole graphical commutator on a nonempty prefix and suffix, with
symmetrizer-two shorter strand and its all-degree premise proved. -/
theorem graphical_commutator (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (fullFamily true true).coeff oddDatum oddSymmetrizer 0 σ z -
      σ * (fullFamily false true).coeff oddDatum oddSymmetrizer 0 σ z =
    ((claim5CapSeries oddDatum oddSymmetrizer 0 (b true true) true false σ -
      HahnSeries.C σ * claim5CapSeries oddDatum oddSymmetrizer 0 (b true true) false false σ) *
        shorterSeries σ).coeff z := by
  have h := claim5_graphical_commutator (a := a true true) (b := b true true) (i := false)
    (fullFamily true true) (fullFamily false true) (shortFamily true)
    (full_complete true true) (full_complete false true) (short_complete true)
    oddDatum oddSymmetrizer 0 σ hσ (shorterSeries σ)
    (shorter_coefficients σ hσ _) z
  simpa only [show oddDatum.parity false = 1 from rfl, ZMod.val_one, pow_one] using h

private instance empty_strands : IsEmpty (MatchingStrand ([] : List (Letter Bool)) []) :=
  ⟨fun t => by have h := (mem_leftEnds₂.mp t.property).1; change t.val < 0 at h; omega⟩

private instance empty_strands_alias :
    IsEmpty (MatchingStrand (a false true ++ b false true) (S false)) := empty_strands

private def emptyLabel : (shortFamily false).Labels :=
  ⟨⟨S false, Set.mem_singleton _⟩, fun t => isEmptyElim t⟩

private theorem emptyLabel_unique (t : (shortFamily false).Labels) : t = emptyLabel := by
  rcases t with ⟨⟨V, hV⟩, c⟩
  obtain rfl := Set.mem_singleton_iff.mp hV
  congr 1
  funext s
  exact isEmptyElim s

private theorem empty_grading {Y : Type*} [AddCommGroup Y]
    (D : Datum Bool Y) (sy : Symmetrizer D) (μ : Y) :
    (shortFamily false).degree D sy μ emptyLabel = 0 ∧
      (shortFamily false).parity D μ emptyLabel = 0 := by
  have h := mixed_decorated_degree_parity D sy μ
    (shorter_matching false true) r (fun t ht => (shorter_points false true t ht).2)
    emptyLabel.2 _ (ψ_valid false emptyLabel.1 emptyLabel.2)
  simpa [CoefficientFamily.degree, CoefficientFamily.parity, shortFamily,
    emptyLabel, a, b, S, tableDegree, xpar, xlpar, tLay] using h

private theorem empty_coeff {Y : Type*} [AddCommGroup Y]
    (D : Datum Bool Y) (sy : Symmetrizer D) (μ : Y) (σ : ℚ) (z : ℤ) :
    (shortFamily false).coeff D sy μ σ z = (1 : LaurentSeries ℚ).coeff z := by
  classical
  have hf : ((shortFamily false).finite D sy μ z).toFinset =
      if z = 0 then {emptyLabel} else ∅ := by
    ext t
    rw [Set.Finite.mem_toFinset, emptyLabel_unique t]
    change (shortFamily false).degree D sy μ emptyLabel = z ↔ _
    rw [(empty_grading D sy μ).1]
    by_cases hz : z = 0 <;> simp [hz, eq_comm]
  unfold CoefficientFamily.coeff
  rw [hf]
  by_cases hz : z = 0
  · simp [hz, (empty_grading D sy μ).2]
  · simp [hz, HahnSeries.coeff_one]

open CoveringQuantum CoveringQuantum.Coefficients CoveringQuantum.UDot
open CoveringQuantum.UDot.GenericTensor CoveringQuantum.UDot.GenericVerma.MixedGram
open CoveringQuantum.UDot.ContextualExchangeExamples (twoOddDatum)

private theorem empty_form (μ : Bool → ℤ) :
    sesquilinearForm twoOddDatum
      (algebraWord twoOddDatum μ []) (algebraWord twoOddDatum μ []) = 1 := by
  have he : algebraWord twoOddDatum μ [] = positiveHalf twoOddDatum Coefficients.q pi μ
      (twoOddDatum.toSerreF Coefficients.q pi (PreF.monomial Coefficients.Ring [])) := by
    apply Subtype.ext
    simp only [PreF.monomial_nil, map_one, positiveHalf_one, algebraWord]
  rw [he, sesquilinearForm_positiveHalf, CoveringQuantum.UDot.GenericVerma.halfBar_monomial]
  simp only [PreF.monomial_nil, map_one, SuperCartanDatum.serreForm_one_one]

/-- Actual application of the form iff with all premises discharged. Both signs,
all integer degrees, and arbitrary external weights are included. -/
theorem form_coeff_iff (μ : Bool → ℤ) :
    ((∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
      (signLaurent σ hσ (sesquilinearForm twoOddDatum
        (algebraWord twoOddDatum μ [(true, false), (false, false)])
        (algebraWord twoOddDatum μ []))).coeff z =
          (fullFamily true false).coeff twoOddDatum.toSKM twoOddDatum.skmSymmetrizer μ σ z) ↔
     (∀ (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ),
      (signLaurent σ hσ (sesquilinearForm twoOddDatum
        (algebraWord twoOddDatum μ [(false, false), (true, false)])
        (algebraWord twoOddDatum μ []))).coeff z =
          (fullFamily false false).coeff twoOddDatum.toSKM twoOddDatum.skmSymmetrizer μ σ z)) := by
  apply same_boundary_labelled_form_coeff_iff (a := []) (b := []) (i := false)
    (fullFamily true false) (fullFamily false false) (shortFamily false)
    (full_complete true false) (full_complete false false) (short_complete false)
    twoOddDatum μ
  intro σ hσ z
  change _ = (signLaurent σ hσ (sesquilinearForm twoOddDatum
    (algebraWord twoOddDatum μ []) (algebraWord twoOddDatum μ []))).coeff z
  rw [empty_form, map_one]
  exact empty_coeff _ _ μ σ z

end OddMath.SKM.Claim5CoefficientsExamples

