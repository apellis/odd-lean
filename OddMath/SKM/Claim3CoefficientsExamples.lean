/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.SKM.Claim3Coefficients
import OddMath.SKM.BoundedPointSerialization
import OddMath.SKM.PositiveFormCoefficientsExamples

/-! # Coefficientwise BE2 Theorem 10.3 Claim 3 examples -/

noncomputable section
namespace OddMath.SKM.Claim3CoefficientsExamples
open StringDiagrams StringDiagrams.Chord
open CoveringQuantum CoveringQuantum.UDot.GenericTensor
open CoveringQuantum.Coefficients CoveringQuantum.UDot.GenericVerma.MixedGram
open PositiveDecoratedFamilyCoefficientsExamples PositiveFormCoefficientsExamples
open scoped BigOperators

private def A : List (Letter Unit) := [(false, ()), (true, ())]
private def a : List (Letter Unit) := [(true, ())]
private def R : List (TMove (Letter Unit)) := [.cap 0]
private def M : Set (List (TMove (Letter Unit))) := {R}
private def N : Set (List (TMove (Letter Unit))) := {[]}
private abbrev T := Σ S : {S // S ∈ M}, MatchingStrand A S.val → ℕ
private abbrev U := Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ

private theorem hm : IsMatching₂ A [] R := by
  constructor
  · refine ⟨?_, trivial⟩
    exact ⟨(2, (false, ())), (0, (true, ())), rfl, rfl, rfl, by decide⟩
  · rfl
private theorem hn : IsMatching₂ a a [] := ⟨trivial, rfl⟩
private theorem hM : ∀ S ∈ M, IsMatching₂ A [] S ∧ StrictReduced₂ A S := by
  intro S h
  obtain rfl := Set.mem_singleton_iff.mp h
  exact ⟨hm, ⟨⟨List.nodup_nil, by simp [R, tRun, tStep, tStart]⟩,
    List.nodup_singleton _⟩⟩
private theorem hN : ∀ S ∈ N, IsMatching₂ a a S ∧ StrictReduced₂ a S := by
  intro S h
  obtain rfl := Set.mem_singleton_iff.mp h
  exact ⟨hn, ⟨⟨List.nodup_nil, by simp [tRun, tStart]⟩, List.nodup_nil⟩⟩

private theorem same_two {s : List (ℕ × Letter Unit)}
    (hv : Valid s) (hlen : s.length = 2) (i j : ℕ) :
    Same s i j ↔ i < 2 ∧ j < 2 ∧ i ≠ j := by
  constructor
  · intro h
    exact ⟨hlen ▸ h.lt_left, hlen ▸ h.lt_right, h.ne⟩
  · rintro ⟨hi, hj, hne⟩
    obtain ⟨k, hk, -⟩ := hv i (hlen ▸ hi)
    have hkl : k < 2 := hlen ▸ hk.lt_right
    have hkn := hk.ne
    have : k = j := by omega
    exact this ▸ hk
private theorem iso_two {s t : List (ℕ × Letter Unit)}
    (hs : Valid s) (ht : Valid t) (hl : s.map Prod.snd = t.map Prod.snd)
    (hlen : s.length = 2) : Iso s t := by
  have hlen' : t.length = 2 := by
    have := congrArg List.length hl
    simp only [List.length_map] at this
    omega
  exact ⟨hl, fun i j => (same_two hs hlen i j).trans (same_two ht hlen' i j).symm⟩

private theorem hMrep : ∀ S, IsMatching₂ A [] S → StrictReduced₂ A S →
    ∃ V ∈ M, Iso (pairing₂ A V) (pairing₂ A S) := by
  intro S h _
  refine ⟨R, Set.mem_singleton _, ?_⟩
  exact iso_two hm.pairing_properties.1 h.pairing_properties.1
    (hm.pairing_properties.2.2.trans h.pairing_properties.2.2.symm) rfl
private theorem hNrep : ∀ S, IsMatching₂ a a S → StrictReduced₂ a S →
    ∃ V ∈ N, Iso (pairing₂ a V) (pairing₂ a S) := by
  intro S h _
  refine ⟨[], Set.mem_singleton _, ?_⟩
  exact iso_two hn.pairing_properties.1 h.pairing_properties.1
    (hn.pairing_properties.2.2.trans h.pairing_properties.2.2.symm) rfl

private theorem ends_pair {B : List (Letter Unit)} {S : List (TMove (Letter Unit))}
    (n : ℕ) (x y : Letter Unit) (he : pairing₂ B S = [(n, x), (n, y)]) :
    leftEnds₂ B S = [0] := by
  have h (j : ℕ) : IsLeftEnd (pairing₂ B S) j ↔ j = 0 := by
    rw [he]
    change (j < 2 ∧ ¬ ∃ k, k < j ∧ Same [(n, x), (n, y)] j k) ↔ j = 0
    constructor
    · intro h
      have hj := h.1
      interval_cases j
      · rfl
      · exact (h.2 ⟨0, by decide, by simp [Same, idAt]⟩).elim
    · rintro rfl
      exact ⟨by decide, by simp⟩
  have hlen : (pairing₂ B S).length = 2 := by rw [he]; rfl
  unfold leftEnds₂
  simp only [hlen, h]
  decide
private theorem endsM : leftEnds₂ A R = [0] := ends_pair 2 (false, ()) (true, ()) rfl
private theorem endsN : leftEnds₂ a [] = [0] := ends_pair 0 (false, ()) (true, ()) rfl
private def q (_ : {S // S ∈ M}) (_ : ℕ) : ℕ × ℕ := (0, 1)
private def r (_ : {S // S ∈ N}) (_ : ℕ) : ℕ × ℕ := (0, 0)
private theorem hq : ∀ S j, j ∈ leftEnds₂ A S.val →
    (q S j).1 ≤ S.val.length ∧ OnStrand₂ A S.val j (q S j) := by
  rintro ⟨S, hS⟩ j hj
  obtain rfl := Set.mem_singleton_iff.mp hS
  have : j = 0 := by simpa [endsM] using hj
  subst j
  exact ⟨by change 0 ≤ 1; decide, by change 1 < 2; decide, rfl⟩
private theorem hr : ∀ S j, j ∈ leftEnds₂ a S.val →
    (r S j).1 ≤ S.val.length ∧ OnStrand₂ a S.val j (r S j) := by
  rintro ⟨S, hS⟩ j hj
  obtain rfl := Set.mem_singleton_iff.mp hS
  have : j = 0 := by simpa [endsN] using hj
  subst j
  exact ⟨by change 0 ≤ 0; decide, by change 0 < 1; decide, rfl⟩

private def τ (S : {S // S ∈ M}) (c : MatchingStrand A S.val → ℕ) : List (DTMove Unit) :=
  (exists_decorates₂_of_bounded_points A S.val (q S)
    (fun j hj => (hq S j hj).2) (fun j hj => (hq S j hj).1) c).choose
private theorem hτ (S : {S // S ∈ M}) (c : MatchingStrand A S.val → ℕ) :
    Decorates₂ A S.val (q S) (strandCounts c) (τ S c) :=
  (exists_decorates₂_of_bounded_points A S.val (q S)
    (fun j hj => (hq S j hj).2) (fun j hj => (hq S j hj).1) c).choose_spec.1
private def υ (S : {S // S ∈ N}) (c : MatchingStrand a S.val → ℕ) : List (DTMove Unit) :=
  (exists_decorates₂_of_bounded_points a S.val (r S)
    (fun j hj => (hr S j hj).2) (fun j hj => (hr S j hj).1) c).choose
private theorem hυ (S : {S // S ∈ N}) (c : MatchingStrand a S.val → ℕ) :
    Decorates₂ a S.val (r S) (strandCounts c) (υ S c) :=
  (exists_decorates₂_of_bounded_points a S.val (r S)
    (fun j hj => (hr S j hj).2) (fun j hj => (hr S j hj).1) c).choose_spec.1

/-- An inhabited application with full coverage and uniqueness, to every natural
strand count on the left-cap/upward-identity representative families. -/
private theorem family : ∃ F : T ≃ U,
    ∀ (D : Datum Unit ℤ) (sy : Symmetrizer D) (μ : ℤ),
      let d := fun t : T => tableDegree D sy μ (dLay A (τ t.1 t.2))
      let e := fun u : U => tableDegree D sy μ (dLay a (υ u.1 u.2))
      let p := fun t : T => xpar D μ (dLay A (τ t.1 t.2))
      let p' := fun u : U => xpar D μ (dLay a (υ u.1 u.2))
      let δ := sy.d () * (1 - D.h () (wt D μ a))
      let p₀ := ipar D () (wt D μ a)
      ∃ (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
        (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
        (∀ t, e (F t) = d t + δ ∧ p' (F t) = p t + p₀) ∧
        (∀ z, Nonempty ({t // d t = z - δ} ≃ {u // e u = z})) ∧
        ∀ (σ : ℚ), σ ^ 2 = 1 → ∀ (z : ℤ),
          (∑ u ∈ (hg z).toFinset, σ ^ (p' u).val) =
            σ ^ p₀.val * ∑ t ∈ (hf (z - δ)).toFinset, σ ^ (p t).val := by
  exact leftCup_labelled_family_coefficients hM hN q r hq (fun S j hj => (hr S j hj).2)
    τ υ hτ hυ hMrep hNrep
    (fun _ hS _ hV _ => (Set.mem_singleton_iff.mp hS).trans (Set.mem_singleton_iff.mp hV).symm)
    (fun _ hS _ hV _ => (Set.mem_singleton_iff.mp hS).trans (Set.mem_singleton_iff.mp hV).symm)

private abbrev D := oddDatum.toSKM
private abbrev sy := oddDatum.skmSymmetrizer
private def d (t : T) : ℤ := tableDegree D sy 0 (dLay A (τ t.1 t.2))
private def e (u : U) : ℤ := tableDegree D sy 0 (dLay a (υ u.1 u.2))
private def p (t : T) : ZMod 2 := xpar D 0 (dLay A (τ t.1 t.2))
private def p' (u : U) : ZMod 2 := xpar D 0 (dLay a (υ u.1 u.2))
private def j0 : MatchingStrand A R := ⟨0, by rw [endsM]; simp⟩
private def t (n : ℕ) : T := ⟨⟨R, Set.mem_singleton _⟩, fun _ => n⟩

private theorem count_grading (c : MatchingStrand A R → ℕ) :
    d ⟨⟨R, Set.mem_singleton _⟩, c⟩ = 2 * (c j0 : ℤ) + 1 ∧
    p ⟨⟨R, Set.mem_singleton _⟩, c⟩ = (c j0 : ZMod 2) + 1 := by
  have hj (j : MatchingStrand A R) : j = j0 := by
    apply Subtype.ext
    have := j.property
    simpa [endsM, j0] using this
  have hu : (Finset.univ : Finset (MatchingStrand A R)) = {j0} := by
    ext j
    simp [hj j]
  have h := mixed_decorated_degree_parity D sy 0 hm (q ⟨R, Set.mem_singleton _⟩)
    (fun j hj => (hq ⟨R, Set.mem_singleton _⟩ j hj).2) c _ (hτ ⟨R, Set.mem_singleton _⟩ c)
  simp only [hu, Finset.sum_singleton] at h
  have hb : tableDegree D sy 0 (tLay A R) = 1 := by rfl
  have hp : xpar D 0 (tLay A R) = 1 := by rfl
  have hc : matchingStrandColour A R j0 = () := rfl
  rw [hb, hp, hc] at h
  simpa [d, p, oddDatum, RootDatum.toSKM,
    RootDatum.skmSymmetrizer, mul_comm, add_comm] using h

private theorem source_fiber (n : ℕ) :
    {x : T | d x = 2 * (n : ℤ) + 1} = {t n} := by
  ext x
  constructor
  · rcases x with ⟨⟨S, hS⟩, c⟩
    obtain rfl := Set.mem_singleton_iff.mp hS
    intro hx
    have hg := (count_grading c).1
    change d ⟨⟨R, hS⟩, c⟩ = 2 * (n : ℤ) + 1 at hx
    have hn : c j0 = n := by omega
    have hc : c = fun _ => n := by
      funext j
      have hj : j = j0 := by
        apply Subtype.ext
        simpa [endsM, j0] using j.property
      rw [hj, hn]
    subst c
    exact Set.mem_singleton _
  · rintro (rfl : x = t n)
    exact (count_grading (fun _ => n)).1

/-- All natural counts, not a fixed decorated singleton, are included. The actual
source fiber is nonempty and finite in degree `2*n+1`; the cup moves it to degree
`2*n`. The source parity is `n+1`, and the parity-one cup contributes the factor `σ`. -/
theorem left_cup_cap_all_counts (n : ℕ) (σ : ℚ) (hσ : σ ^ 2 = 1) :
    ∃ (hf : Set.Finite {x : T | d x = 2 * (n : ℤ) + 1})
      (hg : Set.Finite {u : U | e u = 2 * (n : ℤ)}),
      (∃ x, d x = 2 * (n : ℤ) + 1) ∧ (∃ u, e u = 2 * (n : ℤ)) ∧
      (∑ x ∈ hf.toFinset, σ ^ (p x).val) = σ ^ ((n : ZMod 2) + 1).val ∧
      (∑ u ∈ hg.toFinset, σ ^ (p' u).val) = σ * ∑ x ∈ hf.toFinset, σ ^ (p x).val := by
  classical
  obtain ⟨F, hF⟩ := family
  obtain ⟨hfAll, hgAll, h⟩ := hF D sy 0
  change (∀ x, e (F x) = d x + (-1) ∧ p' (F x) = p x + 1) ∧
    (∀ z, Nonempty ({x // d x = z - (-1)} ≃ {u // e u = z})) ∧
    (∀ (σ : ℚ), σ ^ 2 = 1 → ∀ (z : ℤ),
      (∑ u ∈ (hgAll z).toFinset, σ ^ (p' u).val) =
        σ ^ (1 : ZMod 2).val * ∑ x ∈ (hfAll (z - (-1))).toFinset, σ ^ (p x).val) at h
  have hf : Set.Finite {x : T | d x = 2 * (n : ℤ) + 1} := hfAll _
  have hg : Set.Finite {u : U | e u = 2 * (n : ℤ)} := hgAll _
  have heq : (∑ u ∈ hg.toFinset, σ ^ (p' u).val) =
      σ * ∑ x ∈ hf.toFinset, σ ^ (p x).val := by
    simpa only [sub_neg_eq_add, show (1 : ZMod 2).val = 1 from rfl, pow_one] using h.2.2 σ hσ (2 *
      (n : ℤ))
  have hfs : hf.toFinset = {t n} := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact Set.ext_iff.mp (source_fiber n) x
  refine ⟨hf, hg, ⟨t n, (count_grading (fun _ => n)).1⟩, ?_, ?_, heq⟩
  · refine ⟨F (t n), ?_⟩
    rw [(h.1 (t n)).1, show d (t n) = 2 * (n : ℤ) + 1 from (count_grading (fun _ => n)).1]
    ring
  · rw [hfs, Finset.sum_singleton, show p (t n) = (n : ZMod 2) + 1 from (count_grading (fun _ =>
    n)).2]

/-- The same all-count families specialize at both rational signs. -/
theorem left_cup_cap_both_signs (n : ℕ) :
    (∃ (hf : Set.Finite {x : T | d x = 2 * (n : ℤ) + 1})
       (hg : Set.Finite {u : U | e u = 2 * (n : ℤ)}),
      (∃ x, d x = 2 * (n : ℤ) + 1) ∧ (∃ u, e u = 2 * (n : ℤ)) ∧
      (∑ x ∈ hf.toFinset, (1 : ℚ) ^ (p x).val) = 1 ∧
      (∑ u ∈ hg.toFinset, (1 : ℚ) ^ (p' u).val) = 1) ∧
    (∃ (hf : Set.Finite {x : T | d x = 2 * (n : ℤ) + 1})
       (hg : Set.Finite {u : U | e u = 2 * (n : ℤ)}),
      (∃ x, d x = 2 * (n : ℤ) + 1) ∧ (∃ u, e u = 2 * (n : ℤ)) ∧
      (∑ x ∈ hf.toFinset, (-1 : ℚ) ^ (p x).val) = (-1 : ℚ) ^ ((n : ZMod 2) + 1).val ∧
      (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' u).val) =
        -(∑ x ∈ hf.toFinset, (-1 : ℚ) ^ (p x).val)) := by
  constructor
  · obtain ⟨hf, hg, hx, hu, hs, ht⟩ := left_cup_cap_all_counts n 1 (by norm_num)
    refine ⟨hf, hg, hx, hu, ?_, ?_⟩
    · simpa using hs
    · simpa using ht.trans (congrArg (fun v : ℚ => 1 * v) hs)
  · obtain ⟨hf, hg, hx, hu, hs, ht⟩ := left_cup_cap_all_counts n (-1) (by norm_num)
    exact ⟨hf, hg, hx, hu, hs, by simpa using ht⟩

/-- Omitting the left-cup parity factor is false: at count zero and sign -1,
the source degree-one coefficient is -1 but the target degree-zero coefficient is 1. -/
theorem left_cup_negative_sign_distinction :
    ∃ (hf : Set.Finite {x : T | d x = 1}) (hg : Set.Finite {u : U | e u = 0}),
      (∃ x, d x = 1) ∧ (∃ u, e u = 0) ∧
      (∑ x ∈ hf.toFinset, (-1 : ℚ) ^ (p x).val) = -1 ∧
      (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' u).val) = 1 ∧
      (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' u).val) ≠
        ∑ x ∈ hf.toFinset, (-1 : ℚ) ^ (p x).val := by
  obtain ⟨hf, hg, hx, hu, hs, ht⟩ := left_cup_cap_all_counts 0 (-1) (by norm_num)
  have hs' : (∑ x ∈ hf.toFinset, (-1 : ℚ) ^ (p x).val) = -1 := by
    simpa only [Nat.cast_zero, zero_add, show (1 : ZMod 2).val = 1 from rfl, pow_one] using hs
  have ht' : (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' u).val) = 1 := by
    rw [hs'] at ht
    simpa using ht
  refine ⟨by simpa using hf, by simpa using hg, by simpa using hx, by simpa using hu,
    hs', ht', ?_⟩
  rw [ht', hs']
  norm_num

/-- The coefficientwise Claim 3 equivalence on the complete cap/upward-identity
families. Every natural count is included, with the very same finite witnesses
in the iff and in the populated, parity-sensitive coefficient calculation. -/
theorem cap_form_coeff_iff :
    ∃ (hf : ∀ z : ℤ, Set.Finite {x : T | d x = z})
      (hg : ∀ z : ℤ, Set.Finite {u : U | e u = z}),
      (∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
       ((∀ z : ℤ,
        (signLaurent σ hσ (sesquilinearForm oddDatum
          (algebraWord oddDatum 0 A) (algebraWord oddDatum 0 []))).coeff z =
            ∑ x ∈ (hf z).toFinset, σ ^ (p x).val) ↔
        (∀ z : ℤ,
        (signLaurent σ hσ (sesquilinearForm oddDatum
          (algebraWord oddDatum 0 a) (algebraWord oddDatum 0 a))).coeff z =
            ∑ u ∈ (hg z).toFinset, σ ^ (p' u).val))) ∧
      ∀ (n : ℕ) (σ : ℚ), σ ^ 2 = 1 →
        (∃ x, d x = 2 * (n : ℤ) + 1) ∧ (∃ u, e u = 2 * (n : ℤ)) ∧
        (∑ x ∈ (hf (2 * (n : ℤ) + 1)).toFinset, σ ^ (p x).val) =
          σ ^ ((n : ZMod 2) + 1).val ∧
        (∑ u ∈ (hg (2 * (n : ℤ))).toFinset, σ ^ (p' u).val) =
          σ * ∑ x ∈ (hf (2 * (n : ℤ) + 1)).toFinset, σ ^ (p x).val := by
  obtain ⟨_, hF⟩ := leftCup_labelled_form_coeff_iff (X := ℤ)
    hM hN q r hq (fun S j hj => (hr S j hj).2) τ υ hτ hυ hMrep hNrep
    (fun _ hS _ hV _ => (Set.mem_singleton_iff.mp hS).trans (Set.mem_singleton_iff.mp hV).symm)
    (fun _ hS _ hV _ => (Set.mem_singleton_iff.mp hS).trans (Set.mem_singleton_iff.mp hV).symm)
  obtain ⟨hf, hg, _, _, hiff⟩ := hF oddDatum 0
  refine ⟨hf, hg, hiff, ?_⟩
  intro n σ hσ
  obtain ⟨_, _, hx, hu, hs, ht⟩ := left_cup_cap_all_counts n σ hσ
  exact ⟨hx, hu, hs, ht⟩

/-- The sign factor is necessary in the same witnesses as the form iff. -/
theorem cap_form_negative_sign :
    ∃ (hf : Set.Finite {x : T | d x = 1}) (hg : Set.Finite {u : U | e u = 0}),
      (∑ x ∈ hf.toFinset, (-1 : ℚ) ^ (p x).val) = -1 ∧
      (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' u).val) = 1 := by
  obtain ⟨hf, hg, _, h⟩ := cap_form_coeff_iff
  obtain ⟨_, _, hs, ht⟩ := h 0 (-1) (by norm_num)
  refine ⟨hf 1, hg 0, ?_, ?_⟩
  · simpa [show (1 : ZMod 2).val = 1 from rfl] using hs
  · rw [hs] at ht
    simpa [show (1 : ZMod 2).val = 1 from rfl] using ht

namespace Mismatch
private def A : List (Letter Unit) := [(false, ())]
private def B : List (Letter Unit) := [(true, ())]
private def E : Set (List (TMove (Letter Unit))) := ∅
private abbrev T := Σ R : {R // R ∈ E}, MatchingStrand A R.val → ℕ
private abbrev U := Σ R : {R // R ∈ E}, MatchingStrand ([] : List (Letter Unit)) R.val → ℕ

private theorem source_ne : wt oddDatum.toSKM 0 A ≠ wt oddDatum.toSKM 0 [] := by
  change (-2 : ℤ) ≠ 0
  norm_num
private theorem target_ne : wt oddDatum.toSKM 0 [] ≠ wt oddDatum.toSKM 0 B := by
  change (0 : ℤ) ≠ 2
  norm_num
private theorem no_source (R : List (TMove (Letter Unit))) : ¬ IsMatching₂ A [] R :=
  not_isMatching₂_of_weight_ne oddDatum.toSKM 0 source_ne R
private theorem no_target (R : List (TMove (Letter Unit))) : ¬ IsMatching₂ [] B R :=
  not_isMatching₂_of_weight_ne oddDatum.toSKM 0 target_ne R
private def q (R : {R // R ∈ E}) (_ : ℕ) : ℕ × ℕ := False.elim R.property
private def τ (R : {R // R ∈ E}) (_ : MatchingStrand A R.val → ℕ) : List (DTMove Unit) :=
  False.elim R.property
private def υ (R : {R // R ∈ E}) (_ : MatchingStrand ([] : List (Letter Unit)) R.val → ℕ) : List
  (DTMove Unit) :=
  False.elim R.property
private def d (t : T) : ℤ := tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0 (dLay A (τ t.1
  t.2))
private def e (u : U) : ℤ := tableDegree oddDatum.toSKM oddDatum.skmSymmetrizer 0 (dLay [] (υ u.1
  u.2))
private def p (t : T) : ZMod 2 := xpar oddDatum.toSKM 0 (dLay A (τ t.1 t.2))
private def p' (u : U) : ZMod 2 := xpar oddDatum.toSKM 0 (dLay [] (υ u.1 u.2))

/-- Empty families cover all representatives here because the endpoints forbid
any matching. This instantiates the endpoint-unrestricted headline, with two
different algebraic word pairs and all geometric premises discharged. -/
theorem empty_form_coeff_iff :
    ∃ (hf : ∀ z : ℤ, Set.Finite {t : T | d t = z})
      (hg : ∀ z : ℤ, Set.Finite {u : U | e u = z}),
      ∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
       ((∀ z : ℤ,
        (signLaurent σ hσ (sesquilinearForm oddDatum
          (algebraWord oddDatum 0 A) (algebraWord oddDatum 0 []))).coeff z =
            ∑ t ∈ (hf z).toFinset, σ ^ (p t).val) ↔
        (∀ z : ℤ,
        (signLaurent σ hσ (sesquilinearForm oddDatum
          (algebraWord oddDatum 0 []) (algebraWord oddDatum 0 B))).coeff z =
            ∑ u ∈ (hg z).toFinset, σ ^ (p' u).val)) := by
  obtain ⟨_, hF⟩ := leftCup_labelled_form_coeff_iff (X := ℤ) (i := ())
    (a := []) (b := []) (M := E) (N := E)
    (fun _ h => False.elim h) (fun _ h => False.elim h) q q
    (fun R => False.elim R.property) (fun R => False.elim R.property)
    τ υ (fun R => False.elim R.property) (fun R => False.elim R.property)
    (fun R h _ => False.elim (no_source R h))
    (fun R h _ => False.elim (no_target R h))
    (fun _ h => False.elim h) (fun _ h => False.elim h)
  obtain ⟨hf, hg, _, _, hiff⟩ := hF oddDatum 0
  exact ⟨hf, hg, hiff⟩

/-- Off support, both distinct form coefficients and both family sums vanish. -/
theorem empty_coefficients_zero (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ)
    (hf : Set.Finite {t : T | d t = z}) (hg : Set.Finite {u : U | e u = z}) :
    (signLaurent σ hσ (sesquilinearForm oddDatum
      (algebraWord oddDatum 0 A) (algebraWord oddDatum 0 []))).coeff z = 0 ∧
    (signLaurent σ hσ (sesquilinearForm oddDatum
      (algebraWord oddDatum 0 []) (algebraWord oddDatum 0 B))).coeff z = 0 ∧
    (∑ t ∈ hf.toFinset, σ ^ (p t).val) = 0 ∧
    (∑ u ∈ hg.toFinset, σ ^ (p' u).val) = 0 := by
  have hs := sesquilinearForm_mixed_eq_zero_of_weight_ne oddDatum 0 A [] source_ne
  have ht := sesquilinearForm_mixed_eq_zero_of_weight_ne oddDatum 0 [] B target_ne
  refine ⟨by rw [hs, map_zero, HahnSeries.coeff_zero],
    by rw [ht, map_zero, HahnSeries.coeff_zero], ?_, ?_⟩
  · exact Finset.sum_eq_zero (fun t _ => False.elim t.1.property)
  · exact Finset.sum_eq_zero (fun u _ => False.elim u.1.property)
end Mismatch
end OddMath.SKM.Claim3CoefficientsExamples
