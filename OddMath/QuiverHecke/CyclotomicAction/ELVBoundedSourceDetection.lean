import OddMath.QuiverHecke.CyclotomicAction.ELVJointPBWDetection
import OddMath.QuiverHecke.WeightedCoefficientSeparation

/-! # Detection of the bounded recovery source
This compares the literal total coefficient/PBW windows of bounded recovery
with the integer-degree windows in joint reservoir detection
(SwappedVacuumCoordinates §6). All bounds precede the quotient cutoffs.
-/
noncomputable section
open CategoryTheory StringDiagrams
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  (Sc : SKM.Scalars D k) (hc : Sc.Homogeneous)

/-- There are finitely many affine normal forms with a bounded dot count,
even when the colour set is infinite. -/
theorem finite_nf_dotLength_le (v w : List I) (d : ℕ) :
    {i : NFIdx v w | i.1.1.length ≤ d}.Finite := by
  classical
  let S : Set (List ℕ × Equiv.Perm (Fin v.length)) :=
    ((fun l : List (Fin v.length) => l.map Fin.val) '' {l | l.length ≤ d}) ×ˢ Set.univ
  have hS : S.Finite := ((List.finite_length_le _ d).image _).prod Set.finite_univ
  refine (hS.preimage (Subtype.val_injective.injOn)).subset ?_
  intro i hi
  have hlt := i.2.2.1
  refine ⟨⟨i.1.1.pmap (fun x hx => (⟨x, hx⟩ : Fin v.length)) hlt, ?_, ?_⟩,
    Set.mem_univ _⟩
  · change (List.pmap _ _ _).length ≤ d
    rw [List.length_pmap]
    exact hi
  · simp [List.map_pmap]

/-- A bound for the integer degrees of those finitely many affine forms. -/
theorem exists_nf_degree_upper_bound (v w : List I) (d : ℕ) :
    ∃ P : ℤ, ∀ i : NFIdx v w, i.1.1.length ≤ d → i.deg D sy ≤ P := by
  obtain ⟨P, hP⟩ := ((finite_nf_dotLength_le v w d).image
    (fun i => i.deg D sy)).bddAbove
  exact ⟨P, fun i hi => hP ⟨i, hi, rfl⟩⟩

/-- The full bounded-recovery window fits inside one cutoff-independent
joint source window. Finite colours bound coefficient degree by weight. -/
theorem exists_extendedAtMost_le_jointPBWWindow [Finite I]
    (v w : List I) (d : ℕ) :
    ∃ B : ℤ, ExtendedAtMost D Sc v w d ≤ jointPBWWindow D sy Sc d v w B := by
  obtain ⟨M, hM, hm⟩ := SKM.SYM.exists_coefficientDegree_bound D sy
  obtain ⟨P, hP⟩ := exists_nf_degree_upper_bound D sy v w d
  refine ⟨M * d + P + 1, Submodule.span_le.mpr ?_⟩
  rintro _ ⟨⟨a,i⟩, hi, rfl⟩
  have hi' : SKM.SYM.coefficientWeight D a + i.1.1.length ≤ d := hi
  have ha : SKM.SYM.coefficientWeight D a ≤ d := by omega
  have hlen : i.1.1.length ≤ d := by omega
  have hdeg := hm a
  have hmono := mul_le_mul_of_nonneg_left (Nat.cast_le.mpr ha : 
    (SKM.SYM.coefficientWeight D a : ℤ) ≤ d) hM
  rw [extensionBasis_apply]
  apply Submodule.subset_span
  refine ⟨(a,i), ⟨ha, ?_⟩, rfl⟩
  have hp := hP i hlen
  change SKM.SYM.coefficientDegree D sy a + i.deg D sy < M * d + P + 1
  omega

include sy hc in
/-- The actual coefficient-truncated cyclotomic quotients detect the exact
bounded source used by recovery, including arbitrary exterior products. -/
theorem extendedAtMost_detected_at_high_cutoffs [Finite I]
    (v w : List I) (d : ℕ) :
    ∃ K : ℕ, ∀ (cutoff : I → ℕ) (N : ℕ),
      (∀ i, K ≤ cutoff i) → K ≤ N →
      Function.Injective (fun x : ExtendedAtMost D Sc v w d =>
        (truncatedIdeal D Sc cutoff N v w).mkQ
          (elvHomQuotient D Sc cutoff v w x.val)) := by
  obtain ⟨B, hB⟩ := exists_extendedAtMost_le_jointPBWWindow D sy Sc v w d
  by_cases hp : w.Perm v
  · obtain ⟨K, hK⟩ := jointPBWWindow_detected_at_high_cutoffs D sy Sc hc v d B
    refine ⟨K, fun cutoff N hcut hN x y hxy => ?_⟩
    have he := hK cutoff N hcut hN v w (List.Perm.refl _) hp
      (a₁ := ⟨x.val, hB x.property⟩) (a₂ := ⟨y.val, hB y.property⟩) hxy
    have hval : x.val = y.val := congrArg
      (fun z : jointPBWWindow D sy Sc d v w B => z.val) he
    exact Subtype.ext hval
  · refine ⟨0, fun cutoff N _ _ x y _ => ?_⟩
    apply Subtype.ext
    let H := (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)
    let _ : Subsingleton H :=
      ⟨fun f g => (OddMath.QuiverHecke.hom_eq_zero_of_not_perm D Sc hp f).trans
        (OddMath.QuiverHecke.hom_eq_zero_of_not_perm D Sc hp g).symm⟩
    let _ : Subsingleton (coefficientObj D Sc v ⟶ coefficientObj D Sc w) :=
      Function.Injective.subsingleton (sourceTensorEquiv D Sc v w).symm.injective
    exact Subsingleton.elim _ _

include sy hc in
/-- These literal quotients jointly separate every full source Hom. The
separation result alone does not construct their categorical action. -/
theorem truncated_quotients_jointly_detect [Finite I] (v w : List I)
    (f : coefficientObj D Sc v ⟶ coefficientObj D Sc w)
    (hf : ∀ N : ℕ, (truncatedIdeal D Sc (fun _ => N) N v w).mkQ
      (elvHomQuotient D Sc (fun _ => N) v w f) = 0) : f = 0 := by
  obtain ⟨d, hd⟩ := exists_mem_extendedAtMost D Sc v w f
  obtain ⟨K, hK⟩ := extendedAtMost_detected_at_high_cutoffs D sy Sc hc v w d
  have he := hK (fun _ => K) K (fun _ => le_rfl) le_rfl
    (a₁ := ⟨f, hd⟩) (a₂ := 0) (by simpa only [ZeroMemClass.coe_zero,
      map_zero] using (hf K))
  exact congrArg (fun z : ExtendedAtMost D Sc v w d => z.val) he

end OddMath.QuiverHecke.ELVOld
