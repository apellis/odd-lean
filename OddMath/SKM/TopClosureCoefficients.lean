import OddMath.SKM.TopMatchingChoice
import OddMath.SKM.MixedRealization
import OddMath.SKM.UpwardTopDots
import OddMath.SKM.PositiveClosureDetector
import OddMath.SKM.MatchingTargetExpansion

/-! Canonical top-label coefficients of positive closure corrections. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc)
variable {c d : ℕ} (a : Fin c → I) (b : Fin d → I)
namespace MatchingBasisChoice
variable (F : MatchingBasisChoice (List.ofFn fun r => (true, a r)) (List.ofFn fun r => (true, b r)))

/-- Every bounded position list has the canonical top serializer with the
same multiplicities, regardless of its original order. -/
theorem topPositions_perm_counts (R : F.members) (is : List ℕ)
    (hb : ∀ i ∈ is, i < d) :
    is.Perm (F.topPositions a b R (fun j => is.count (F.topPosition a b R j).val)) := by
  apply List.perm_iff_count.mpr
  intro i
  by_cases hi : i < d
  · let j := (F.topPosition a b R).symm ⟨i, hi⟩
    have hj : (F.topPosition a b R j).val = i := by simp [j]
    rw [← hj, F.topPositions_count]
  · rw [List.count_eq_zero.mpr (fun h => hi (hb i h)),
      List.count_eq_zero.mpr (fun h => hi (F.topPositions_bound a b R _ i h))]

/-- An actual positive-dot correction preserves the skeleton and strictly
increases the canonical top count, up to an exact sign. -/
theorem top_correction_signed (μ : X) (t : (F.atTop a b).Labels)
    (L : PositiveWordDots (List.ofFn fun r : Fin d => (true, b r))) :
    ∃ (n : MatchingStrand (List.ofFn fun r : Fin c => (true, a r)) t.1.val → ℕ)
      (p : ZMod 2),
      (F.atTop a b).openDots t < (F.atTop a b).openDots ⟨t.1, n⟩ ∧
      xev cs μ (List.ofFn fun r : Fin c => (true, a r)) (List.ofFn fun r : Fin d => (true, b r))
        ((F.atTop a b).layers t ++ L.val.map ofL) =
      zsign k p • xev cs μ (List.ofFn fun r : Fin c => (true, a r)) (List.ofFn fun r : Fin d => (true, b r))
        ((F.atTop a b).layers ⟨t.1, n⟩) := by
  obtain ⟨ns, hns, hn, hb⟩ := upDotsOnly_eq_dotsOn L.property.1 L.property.2.1
  let is := F.topPositions a b t.1 t.2 ++ ns
  let n := fun j => is.count (F.topPosition a b t.1 j).val
  have his : ∀ i ∈ is, i < d := by
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · exact F.topPositions_bound a b t.1 t.2 i hi
    · simpa only [List.length_ofFn] using hb i hi
  have hperm := F.topPositions_perm_counts a b t.1 is his
  have hP : XChain (List.ofFn fun r : Fin c => (true, a r))
      (tLay (List.ofFn fun r : Fin c => (true, a r)) t.1.val)
      (List.ofFn fun r : Fin d => (true, b r)) := by
    have H := matching_dLay_chain (F.matching t.1.val t.1.property).1
      (t.1.val.map DTMove.tm) (DTMove.tmoves_map_tm t.1.val)
    simpa only [dLay_map_tm] using H
  obtain ⟨p, hp⟩ := top_dots_perm_eq cs hperm
    (fun i hi => by simpa only [List.length_ofFn] using his i hi) μ
    (tLay (List.ofFn fun r : Fin c => (true, a r)) t.1.val) [] hP
  refine ⟨n, p, ?_, ?_⟩
  · change (∑ j, t.2 j) < ∑ j, n j
    rw [← F.topPositions_length a b t.1 t.2, ← F.topPositions_length a b t.1 n,
      ← hperm.length_eq]
    change (F.topPositions a b t.1 t.2).length < (F.topPositions a b t.1 t.2 ++ ns).length
    rw [List.length_append, hn]
    exact Nat.lt_add_of_pos_right L.property.2.2
  · rw [F.atTop_layers_dotsOn a b, F.atTop_layers_dotsOn a b, hns]
    simpa only [List.append_nil, is, dotsOn_append, List.append_assoc] using hp

/-- Every finite actual positive-dot closure correction lifts to an at-top
coefficient vector supported at strictly greater open-dot count. -/
theorem top_positiveExpansion_lift (μ : X) (t : (F.atTop a b).Labels)
    (z : PositiveWordDots (List.ofFn fun r : Fin d => (true, b r)) →₀ SYM D k) :
    ∃ r : (F.atTop a b).Labels →₀ SYM D k,
      (∀ u ∈ r.support, (F.atTop a b).openDots t < (F.atTop a b).openDots u) ∧
      (F.atTop a b).targetExpansion cs μ r =
        xev cs μ (List.ofFn fun r : Fin c => (true, a r)) (List.ofFn fun r : Fin d => (true, b r))
          ((F.atTop a b).layers t) ≫
        positiveWordExpansion cs μ (List.ofFn fun r : Fin d => (true, b r)) z := by
  classical
  let T := (Finsupp.supported (SYM D k) k
    {u | (F.atTop a b).openDots t < (F.atTop a b).openDots u}).map ((F.atTop a b).targetExpansion cs μ)
  have hc : XChain (List.ofFn fun r : Fin c => (true, a r)) ((F.atTop a b).layers t)
      (List.ofFn fun r : Fin d => (true, b r)) :=
    matching_dLay_chain (F.matching t.1.val t.1.property).1 _ ((F.atTop a b).decorates t.1 t.2).1
  have ht (L : PositiveWordDots (List.ofFn fun r : Fin d => (true, b r))) (p : SYM D k) :
      xev cs μ (List.ofFn fun r : Fin c => (true, a r)) (List.ofFn fun r : Fin d => (true, b r))
        ((F.atTop a b).layers t) ≫
      positiveWordExpansion cs μ (List.ofFn fun r : Fin d => (true, b r)) (Finsupp.single L p) ∈ T := by
    obtain ⟨n, q, hn, he⟩ := F.top_correction_signed cs a b μ t L
    refine ⟨Finsupp.single ⟨t.1, n⟩ (zsign k q • p), Finsupp.single_mem_supported k _ hn, ?_⟩
    rw [targetExpansion_single, positiveWordExpansion_single, ← Category.assoc,
      ← xev_map_ofL cs μ _ _ L.val, ← xev_append cs _ hc, he]
    simp only [map_smul, Linear.comp_smul, Linear.smul_comp]
  have hz :
      xev cs μ (List.ofFn fun r : Fin c => (true, a r)) (List.ofFn fun r : Fin d => (true, b r))
        ((F.atTop a b).layers t) ≫
      positiveWordExpansion cs μ (List.ofFn fun r : Fin d => (true, b r)) z ∈ T := by
    induction z using Finsupp.induction with
    | zero => simp only [map_zero, Limits.comp_zero]; exact Submodule.zero_mem _
    | @single_add L p z _ _ ih =>
      rw [map_add, Preadditive.comp_add]
      exact Submodule.add_mem _ (ht L p) ih
  obtain ⟨r, hr, he⟩ := hz
  exact ⟨r, (Finsupp.mem_supported k r).mp hr, he⟩

end MatchingBasisChoice
end OddMath.SKM
