import OddMath.SKM.Claim2Coefficients
import OddMath.SKM.BoundedPointSerialization
import OddMath.SKM.PositiveFormCoefficientsExamples

/-! # Coefficientwise BE2 Theorem 10.3 Claim 2 examples -/

noncomputable section
namespace OddMath.SKM.Claim2CoefficientsExamples
open StringDiagrams StringDiagrams.Chord
open CoveringQuantum CoveringQuantum.UDot.GenericTensor
open CoveringQuantum.Coefficients CoveringQuantum.UDot.GenericVerma.MixedGram
open PositiveDecoratedFamilyCoefficientsExamples PositiveFormCoefficientsExamples
open scoped BigOperators

private def A : List (Letter Unit) := [(true, ()), (false, ())]
private def a : List (Letter Unit) := [(false, ())]
private def R : List (TMove (Letter Unit)) := [.cap 0]
private def M : Set (List (TMove (Letter Unit))) := {R}
private def N : Set (List (TMove (Letter Unit))) := {[]}
private abbrev T := Σ S : {S // S ∈ M}, MatchingStrand A S.val → ℕ
private abbrev U := Σ S : {S // S ∈ N}, MatchingStrand a S.val → ℕ

private theorem hm : IsMatching₂ A [] R := by
  constructor
  · refine ⟨?_, trivial⟩
    exact ⟨(2, (true, ())), (0, (false, ())), rfl, rfl, rfl, by decide⟩
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
private theorem endsM : leftEnds₂ A R = [0] := ends_pair 2 (true, ()) (false, ()) rfl
private theorem endsN : leftEnds₂ a [] = [0] := ends_pair 0 (true, ()) (false, ()) rfl
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
strand count on the right-cap/downward-identity representative families. -/
private theorem family : ∃ F : T ≃ U,
    ∀ (D : Datum Unit ℤ) (sy : Symmetrizer D) (μ : ℤ),
      let d := fun t : T => tableDegree D sy μ (dLay A (τ t.1 t.2))
      let e := fun u : U => tableDegree D sy μ (dLay a (υ u.1 u.2))
      let p := fun t : T => xpar D μ (dLay A (τ t.1 t.2))
      let p' := fun u : U => xpar D μ (dLay a (υ u.1 u.2))
      let δ := sy.d () * (1 + D.h () (wt D μ a))
      ∃ (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
        (hg : ∀ z : ℤ, Set.Finite {u | e u = z}),
        (∀ t, e (F t) = d t + δ ∧ p' (F t) = p t) ∧
        (∀ z, Nonempty ({t // d t = z - δ} ≃ {u // e u = z})) ∧
        ∀ (σ : ℚ) (z : ℤ),
          (∑ u ∈ (hg z).toFinset, σ ^ (p' u).val) =
            ∑ t ∈ (hf (z - δ)).toFinset, σ ^ (p t).val := by
  exact rightCup_labelled_family_coefficients hM hN q r hq (fun S j hj => (hr S j hj).2)
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
    p ⟨⟨R, Set.mem_singleton _⟩, c⟩ = (c j0 : ZMod 2) := by
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
  have hp : xpar D 0 (tLay A R) = 0 := by rfl
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
`2*n`. Its coefficient is the parity weight, for either sign (indeed every rational). -/
private theorem right_cup_cap_all_counts (n : ℕ) (σ : ℚ) :
    ∃ (hf : Set.Finite {x : T | d x = 2 * (n : ℤ) + 1})
      (hg : Set.Finite {u : U | e u = 2 * (n : ℤ)}),
      (∃ x, d x = 2 * (n : ℤ) + 1) ∧ (∃ u, e u = 2 * (n : ℤ)) ∧
      (∑ x ∈ hf.toFinset, σ ^ (p x).val) = σ ^ (n : ZMod 2).val ∧
      (∑ u ∈ hg.toFinset, σ ^ (p' u).val) = ∑ x ∈ hf.toFinset, σ ^ (p x).val := by
  classical
  obtain ⟨F, hF⟩ := family
  obtain ⟨hfAll, hgAll, h⟩ := hF D sy 0
  change (∀ x, e (F x) = d x + (-1) ∧ p' (F x) = p x) ∧
    (∀ z, Nonempty ({x // d x = z - (-1)} ≃ {u // e u = z})) ∧
    (∀ (σ : ℚ) (z : ℤ),
      (∑ u ∈ (hgAll z).toFinset, σ ^ (p' u).val) =
        ∑ x ∈ (hfAll (z - (-1))).toFinset, σ ^ (p x).val) at h
  have hf : Set.Finite {x : T | d x = 2 * (n : ℤ) + 1} := hfAll _
  have hg : Set.Finite {u : U | e u = 2 * (n : ℤ)} := hgAll _
  have heq : (∑ u ∈ hg.toFinset, σ ^ (p' u).val) =
      ∑ x ∈ hf.toFinset, σ ^ (p x).val := by
    simpa using h.2.2 σ (2 * (n : ℤ))
  have hfs : hf.toFinset = {t n} := by
    ext x
    simp only [Set.Finite.mem_toFinset, Finset.mem_singleton]
    exact Set.ext_iff.mp (source_fiber n) x
  refine ⟨hf, hg, ⟨t n, (count_grading (fun _ => n)).1⟩, ?_, ?_, heq⟩
  · refine ⟨F (t n), ?_⟩
    rw [(h.1 (t n)).1, show d (t n) = 2 * (n : ℤ) + 1 from (count_grading (fun _ => n)).1]
    ring
  · rw [hfs, Finset.sum_singleton, show p (t n) = (n : ZMod 2) from (count_grading (fun _ => n)).2]

/-- Claim 2 instantiated on the complete cap and downward-identity families.
The serializers include all natural counts and are fixed before the signs and
degrees. No endpoint condition is requested; bar consistency is discharged. The same
finite witnesses occurring in the iff have populated fibers and parity-sensitive
values; neither side of the iff is assumed or replaced by a tautology. -/
theorem cap_form_coeff_iff :
    ∃ (hf : ∀ z : ℤ, Set.Finite {x : T | d x = z})
      (hg : ∀ z : ℤ, Set.Finite {u : U | e u = z}),
      (∀ (σ : ℚ) (hσ : σ ^ 2 = 1),
       ((∀ z : ℤ,
        (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
          (algebraWord oddDatum 0 A) (algebraWord oddDatum 0 []))).coeff z =
            ∑ x ∈ (hf z).toFinset, σ ^ (p x).val) ↔
        (∀ z : ℤ,
        (signLaurent σ hσ (sesquilinearForm oddDatum odd_barConsistent
          (algebraWord oddDatum 0 a) (algebraWord oddDatum 0 a))).coeff z =
            ∑ u ∈ (hg z).toFinset, σ ^ (p' u).val))) ∧
      ∀ (n : ℕ) (σ : ℚ),
        (∃ x, d x = 2 * (n : ℤ) + 1) ∧ (∃ u, e u = 2 * (n : ℤ)) ∧
        (∑ x ∈ (hf (2 * (n : ℤ) + 1)).toFinset, σ ^ (p x).val) =
          σ ^ (n : ZMod 2).val ∧
        (∑ u ∈ (hg (2 * (n : ℤ))).toFinset, σ ^ (p' u).val) =
          σ ^ (n : ZMod 2).val := by
  obtain ⟨F, hF⟩ := rightCup_labelled_form_coeff_iff (X := ℤ)
    hM hN q r hq (fun S j hj => (hr S j hj).2) τ υ hτ hυ hMrep hNrep
    (fun _ hS _ hV _ => (Set.mem_singleton_iff.mp hS).trans (Set.mem_singleton_iff.mp hV).symm)
    (fun _ hS _ hV _ => (Set.mem_singleton_iff.mp hS).trans (Set.mem_singleton_iff.mp hV).symm)
  obtain ⟨hf, hg, _, _, hiff⟩ := hF oddDatum odd_barConsistent 0
  refine ⟨hf, hg, hiff, ?_⟩
  intro n σ
  obtain ⟨_, _, hsource, htarget, hs, ht⟩ := right_cup_cap_all_counts n σ
  exact ⟨hsource, htarget, hs, ht.trans hs⟩

/-- Both signs at the populated one-dot target fiber of the iff. -/
example : ∃ hg : Set.Finite {u : U | e u = 2},
    (∃ u, e u = 2) ∧
    (∑ u ∈ hg.toFinset, (1 : ℚ) ^ (p' u).val) = 1 ∧
    (∑ u ∈ hg.toFinset, (-1 : ℚ) ^ (p' u).val) = -1 := by
  obtain ⟨_, hg, _, h⟩ := cap_form_coeff_iff
  have hp := h 1 1
  have hn := h 1 (-1)
  refine ⟨hg 2, ?_, ?_, ?_⟩
  · simpa using hp.2.1
  · simpa using hp.2.2.2
  · simpa [show (1 : ZMod 2).val = 1 from rfl] using hn.2.2.2

end OddMath.SKM.Claim2CoefficientsExamples
