import OddMath.QuiverHecke.PairingExtensionComposition
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates

/-! # The literal power-quotient ideal under pairing extension

`SwappedVacuumCoordinates.md` §§5–7: region inclusion retains the source
coefficient truncation, the powers of each elementary generator, and the
signed last-boundary polynomials. Thus the transport uses the same ideal
as the proved power-word half-turn coordinate kernel.
-/
noncomputable section
namespace OddMath.QuiverHecke.PairingExtension
open CategoryTheory StringDiagrams
open scoped TensorProduct Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
local notation "Dₑ" => ReservoirWeights.pairingExtension D
local notation "Scₑ" => ReservoirWeights.pairingExtensionScalars D Sc
local notation "e" => SKM.PairingExtension.coefficientEquiv (k := k) D

@[simp] theorem coefficientEquiv_e (i : I) (n : ℕ) :
    e (SKM.SYM.e D k i n) = SKM.SYM.e Dₑ k i n :=
  SKM.PairingExtension.coefficientEquiv_ι D (.inl (i,n))
@[simp] theorem coefficientEquiv_delta (i : {i : I // D.parity i = 1}) :
    e (SKM.SYM.delta D k i) = SKM.SYM.delta Dₑ k i :=
  SKM.PairingExtension.coefficientEquiv_ι D (.inr i)
@[simp] theorem coefficientEquiv_chi (i : {i : I // D.parity i = 1}) (n : ℕ) :
    e (SKM.SYM.elvChi D k i n) = SKM.SYM.elvChi Dₑ k i n := by
  cases n <;> simp [SKM.SYM.elvChi]

private theorem coefficientRelation_map_iff (cutoff : I → ℕ) (a : SKM.SYM D k) :
    SKM.SYM.ELVCoefficientRelation Dₑ k cutoff (e a) ↔
      SKM.SYM.ELVCoefficientRelation D k cutoff a := by
  constructor
  · rintro (⟨i,n,hn,ha⟩ | ⟨i,hi,ha⟩)
    · exact Or.inl ⟨i,n,hn,e.injective (ha.trans (coefficientEquiv_e D i n).symm)⟩
    · refine Or.inr ⟨i,hi,e.injective ?_⟩
      simpa only [map_mul, coefficientEquiv_delta, coefficientEquiv_chi] using ha
  · rintro (⟨i,n,hn,rfl⟩ | ⟨i,hi,rfl⟩)
    · exact Or.inl ⟨i,n,hn,coefficientEquiv_e D i n⟩
    · exact Or.inr ⟨i,hi,by rw [map_mul, coefficientEquiv_delta, coefficientEquiv_chi]⟩

/-- The exact odd/even coefficient specialization ideal is retained. -/
theorem coefficientIdeal_map_iff (cutoff : I → ℕ) (a : SKM.SYM D k) :
    e a ∈ SKM.SYM.elvCoefficientIdeal Dₑ k cutoff ↔
      a ∈ SKM.SYM.elvCoefficientIdeal D k cutoff := by
  have hf : SKM.SYM.elvCoefficientIdeal D k cutoff ≤
      (SKM.SYM.elvCoefficientIdeal Dₑ k cutoff).comap e.toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    intro a ha
    exact TwoSidedIdeal.mem_comap.mpr
      (TwoSidedIdeal.subset_span ((coefficientRelation_map_iff D cutoff a).mpr ha))
  have hb : SKM.SYM.elvCoefficientIdeal Dₑ k cutoff ≤
      (SKM.SYM.elvCoefficientIdeal D k cutoff).comap e.symm.toRingHom := by
    apply TwoSidedIdeal.span_le.mpr
    intro b hb
    apply TwoSidedIdeal.mem_comap.mpr
    apply TwoSidedIdeal.subset_span
    apply (coefficientRelation_map_iff D cutoff (e.symm b)).mp
    simpa only [AlgEquiv.apply_symm_apply] using hb
  constructor
  · intro h
    have hh := TwoSidedIdeal.mem_comap.mp (hb h)
    simpa only [AlgEquiv.symm_apply_apply] using hh
  · intro h
    exact TwoSidedIdeal.mem_comap.mp (hf h)

/-- Elementary powers retain their literal colour, index, and exponent. -/
theorem coefficientPower_map_iff (L : I × ℕ → ℕ) (a : SKM.SYM D k) :
    e a ∈ Set.range (fun j : I × ℕ => SKM.SYM.e Dₑ k j.1 j.2 ^ L j) ↔
      a ∈ Set.range (fun j : I × ℕ => SKM.SYM.e D k j.1 j.2 ^ L j) := by
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨j,e.injective ?_⟩
    simpa only [map_pow, coefficientEquiv_e] using hj
  · rintro ⟨j,rfl⟩
    exact ⟨j,by rw [map_pow, coefficientEquiv_e]⟩

theorem coefficientEquiv_transformedCoefficient (i : I) (N : ℕ) (j : Fin (N+1)) :
    e (transformedCoefficient D i N j) = transformedCoefficient Dₑ i N j := by
  unfold transformedCoefficient factorCoefficient
  simp only [ReservoirWeights.pairingExtension_parity, map_smul]
  split_ifs with hi
  · simp only [SKM.SYM.elvMonicCoefficient, map_smul, SKM.SYM.elvCoefficient,
      map_ite, map_mul, coefficientEquiv_delta, coefficientEquiv_chi]
  · unfold SKM.SYM.evenMonicCoefficient
    rw [map_smul]
    congr 1
    cases N-j.val <;> simp [SKM.SYM.evenCyclotomicCoefficient]

theorem presentationFunctor_lastDotPower (t : List I) (n : ℕ) :
    (presentationFunctor D Sc).map (lastDotPower D Sc t n) = lastDotPower Dₑ Scₑ t n := by
  unfold lastDotPower cl
  exact presentationFunctor_diag D Sc _

/-- The half-turn sign and last-position convention are preserved exactly. -/
theorem coefficientHomEquiv_transformedCyclotomic (v : List I) (i : I) (N : ℕ) :
    coefficientHomEquiv D Sc (v++[i]) (v++[i]) (transformedCyclotomic D Sc v i N) =
      transformedCyclotomic Dₑ Scₑ v i N := by
  unfold transformedCyclotomic lastBoundaryPolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [coefficientHomEquiv_source, coefficientEquiv_transformedCoefficient,
    presentationFunctor_lastDotPower]

/-- All three literal families of transformed generators are retained. -/
theorem transformedGenerator_map_iff (cutoff : I → ℕ) (L : I × ℕ → ℕ)
    (t : List I) (r : coefficientObj D Sc t ⟶ coefficientObj D Sc t) :
    TransformedGenerator Dₑ Scₑ cutoff
        (Set.range fun j : I × ℕ => SKM.SYM.e Dₑ k j.1 j.2 ^ L j) t
        (coefficientHomEquiv D Sc t t r) ↔
      TransformedGenerator D Sc cutoff
        (Set.range fun j : I × ℕ => SKM.SYM.e D k j.1 j.2 ^ L j) t r := by
  constructor
  · rintro (⟨a,ha,hr⟩ | ⟨a,ha,hr⟩ | ⟨v,i,h,hr⟩)
    · refine Or.inl ⟨e.symm a,?_,?_⟩
      · apply (coefficientIdeal_map_iff D cutoff _).mp
        simpa only [AlgEquiv.apply_symm_apply] using ha
      · apply (coefficientHomEquiv D Sc t t).injective
        rw [hr, coefficientHomEquiv_source, AlgEquiv.apply_symm_apply,
          (presentationFunctor D Sc).map_id]
    · refine Or.inr (Or.inl ⟨e.symm a,?_,?_⟩)
      · apply (coefficientPower_map_iff D L _).mp
        simpa only [AlgEquiv.apply_symm_apply] using ha
      · apply (coefficientHomEquiv D Sc t t).injective
        rw [hr, coefficientHomEquiv_source, AlgEquiv.apply_symm_apply,
          (presentationFunctor D Sc).map_id]
    · subst t
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hr
      refine Or.inr (Or.inr ⟨v,i,rfl,?_⟩)
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      apply (coefficientHomEquiv D Sc _ _).injective
      rw [hr, coefficientHomEquiv_transformedCyclotomic]
  · rintro (⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩ | ⟨v,i,h,rfl⟩)
    · refine Or.inl ⟨e a,(coefficientIdeal_map_iff D cutoff a).mpr ha,?_⟩
      rw [coefficientHomEquiv_source, (presentationFunctor D Sc).map_id]
    · refine Or.inr (Or.inl ⟨e a,(coefficientPower_map_iff D L a).mpr ha,?_⟩)
      rw [coefficientHomEquiv_source, (presentationFunctor D Sc).map_id]
    · subst t
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      refine Or.inr (Or.inr ⟨v,i,rfl,?_⟩)
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      exact coefficientHomEquiv_transformedCyclotomic D Sc v i (cutoff i)

private theorem transformedIdeal_forward (cutoff : I → ℕ) (L : I × ℕ → ℕ)
    {s t : List I} {f : coefficientObj D Sc s ⟶ coefficientObj D Sc t}
    (hf : f ∈ TransformedIdeal D Sc cutoff
      (Set.range fun j : I × ℕ => SKM.SYM.e D k j.1 j.2 ^ L j) s t) :
    coefficientHomEquiv D Sc s t f ∈ TransformedIdeal Dₑ Scₑ cutoff
      (Set.range fun j : I × ℕ => SKM.SYM.e Dₑ k j.1 j.2 ^ L j) s t := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v,hv,r,hr,a,b,rfl⟩ := hf
    rw [coefficientHomEquiv_comp, coefficientHomEquiv_comp]
    exact Submodule.subset_span ⟨v,hv,coefficientHomEquiv D Sc v v r,
      (transformedGenerator_map_iff D Sc cutoff L v r).mpr hr,
      coefficientHomEquiv D Sc s v a, coefficientHomEquiv D Sc v t b,rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

private theorem transformedIdeal_backward (cutoff : I → ℕ) (L : I × ℕ → ℕ)
    {s t : List I} {f : coefficientObj Dₑ Scₑ s ⟶ coefficientObj Dₑ Scₑ t}
    (hf : f ∈ TransformedIdeal Dₑ Scₑ cutoff
      (Set.range fun j : I × ℕ => SKM.SYM.e Dₑ k j.1 j.2 ^ L j) s t) :
    (coefficientHomEquiv D Sc s t).symm f ∈ TransformedIdeal D Sc cutoff
      (Set.range fun j : I × ℕ => SKM.SYM.e D k j.1 j.2 ^ L j) s t := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨v,hv,r,hr,a,b,rfl⟩ := hf
    obtain ⟨r,rfl⟩ := (coefficientHomEquiv D Sc v v).surjective r
    obtain ⟨a,rfl⟩ := (coefficientHomEquiv D Sc s v).surjective a
    obtain ⟨b,rfl⟩ := (coefficientHomEquiv D Sc v t).surjective b
    rw [← coefficientHomEquiv_comp, ← coefficientHomEquiv_comp, LinearEquiv.symm_apply_apply]
    exact Submodule.subset_span ⟨v,hv,r,
      (transformedGenerator_map_iff D Sc cutoff L v r).mp hr,a,b,rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- Equality of the specified transformed power ideals under the proved equivalence. -/
theorem transformedIdeal_map_iff (cutoff : I → ℕ) (L : I × ℕ → ℕ)
    {s t : List I} (f : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    coefficientHomEquiv D Sc s t f ∈ TransformedIdeal Dₑ Scₑ cutoff
        (Set.range fun j : I × ℕ => SKM.SYM.e Dₑ k j.1 j.2 ^ L j) s t ↔
      f ∈ TransformedIdeal D Sc cutoff
        (Set.range fun j : I × ℕ => SKM.SYM.e D k j.1 j.2 ^ L j) s t := by
  constructor
  · intro hf
    simpa only [LinearEquiv.symm_apply_apply] using transformedIdeal_backward D Sc cutoff L hf
  · exact transformedIdeal_forward D Sc cutoff L

/-- The actual half-turn power-word coordinate kernels commute with pairing extension. -/
theorem powerWordHalfTurnCoordinate_ker_map_iff (cutoff : I → ℕ) (L : I × ℕ → ℕ)
    {s t : List I} (f : coefficientObj D Sc s ⟶ coefficientObj D Sc t) :
    coefficientHomEquiv D Sc s t f ∈ LinearMap.ker
        (powerWordHalfTurnCoordinate Dₑ Scₑ cutoff L s t) ↔
      f ∈ LinearMap.ker (powerWordHalfTurnCoordinate D Sc cutoff L s t) := by
  rw [powerWordHalfTurnCoordinate_ker, powerWordHalfTurnCoordinate_ker]
  exact transformedIdeal_map_iff D Sc cutoff L f

end OddMath.QuiverHecke.PairingExtension
