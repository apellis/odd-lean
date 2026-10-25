import OddMath.SKM.SameColourUnpairedCoordinates
import OddMath.SKM.DistinctTargetDescent

/-! Same-colour contextual target exchange descent, using native all-height
paired columns and unit unpaired coordinates modulo the paired sector. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}
namespace SameColourTargetFrame
variable {cs : CScalars Sc} {μ : X} {a P Q : List (Letter I)} {i : I}
  (F : SameColourTargetFrame cs μ a P Q i)

def principalCoordinates (hG : Function.Injective (F.swapped.expansion cs μ)) :
    (F.original.Labels →₀ SYM D k) →ₗ[k] (F.swapped.Labels →₀ SYM D k) where
  toFun v := F.swappedCoordinates hG
    (F.original.expansion cs μ v ≫ sameColourTargetCross (Sc := Sc) μ P Q i)
  map_add' v w := by rw [map_add, Preadditive.add_comp, map_add]
  map_smul' c v := by rw [map_smul, Linear.smul_comp, map_smul]; rfl

private theorem principalCoordinates_off
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (s t : F.original.Labels) (ht : t ∉ Set.range F.paired) (hst : s ≠ t) (d : SYM D k) :
    F.principalCoordinates hG (Finsupp.single s d) (F.exchange t) = 0 := by
  classical
  by_cases hs : s ∈ Set.range F.paired
  · obtain ⟨⟨b, r⟩, rfl⟩ := hs
    exact F.swappedCoordinates_paired_cross_off hG b r d t ht
  · rcases F.swappedCoordinates_unpaired_cross hG s t hs ht d with H | H
    · simpa [principalCoordinates, F.exchange.injective.ne hst] using H
    · simpa [principalCoordinates, F.exchange.injective.ne hst] using H

private theorem principalCoordinates_diagonal
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (t : F.original.Labels) (ht : t ∉ Set.range F.paired) (d : SYM D k) :
    F.principalCoordinates hG (Finsupp.single t d) (F.exchange t) = d ∨
      F.principalCoordinates hG (Finsupp.single t d) (F.exchange t) = -d := by
  simpa [principalCoordinates] using F.swappedCoordinates_unpaired_cross hG t t ht ht d

/-- A relation among the complete original family has only paired support. -/
theorem kernel_supported_paired
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (f : F.original.Labels →₀ SYM D k) (hf : F.original.expansion cs μ f = 0)
    (t : F.original.Labels) (ht : t ∉ Set.range F.paired) : f t = 0 := by
  classical
  have proj (v : F.original.Labels →₀ SYM D k) :
      F.principalCoordinates hG v (F.exchange t) =
        F.principalCoordinates hG (Finsupp.single t (v t)) (F.exchange t) := by
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v w hv hw =>
      simp only [map_add, Finsupp.add_apply, Finsupp.single_add, hv, hw]
    | single s d =>
      by_cases hst : s = t
      · subst s; simp
      · rw [F.principalCoordinates_off hG s t ht hst d]
        simp [Ne.symm hst]
  have hz : F.principalCoordinates hG (Finsupp.single t (f t)) (F.exchange t) = 0 := by
    rw [← proj]
    simp [principalCoordinates, hf]
  rcases F.principalCoordinates_diagonal hG t ht (f t) with H | H
  · exact H.symm.trans hz
  · exact neg_eq_zero.mp (H.symm.trans hz)

/-- Full same-colour target-family descent, not merely paired-sector descent. -/
theorem originalExpansion_injective
    (hG : Function.Injective (F.swapped.expansion cs μ))
    (hB : Function.Injective (F.residual.expansion cs μ)) :
    Function.Injective (F.original.expansion cs μ) := by
  classical
  let p : F.residual.Labels × ℕ ↪ F.original.Labels :=
    ⟨fun r => F.paired (r.2, r.1), by
      intro r s he
      have H := F.paired.injective he
      exact Prod.ext (congrArg Prod.snd H) (congrArg Prod.fst H)⟩
  have hz (f : F.original.Labels →₀ SYM D k) (hf : F.original.expansion cs μ f = 0) : f = 0 := by
    have hs : ↑f.support ⊆ Set.range p := by
      intro t ht
      by_contra hn
      have hn' : t ∉ Set.range F.paired := by
        rintro ⟨⟨b, r⟩, he⟩
        exact hn ⟨(r, b), he⟩
      exact (Finsupp.mem_support_iff.mp ht) (F.kernel_supported_paired hG f hf t hn')
    let g := Finsupp.comapDomain p f p.injective.injOn
    have hg : F.originalPairedInclusion g = f := by
      exact (Finsupp.embDomain_eq_mapDomain p g).symm.trans (Finsupp.embDomain_comapDomain hs)
    have hgz : g = 0 := by
      apply F.pairedExpansion_injective hG hB
      change F.original.expansion cs μ (F.originalPairedInclusion g) = F.pairedExpansion 0
      rw [hg, hf, map_zero]
    rw [← hg, hgz, map_zero]
  intro f g he
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, he, sub_self]

end SameColourTargetFrame

/-- Same-colour target exchange uses the swapped boundary and the shortened
residual boundary, with complete adapted choices constructed internally. -/
theorem same_colour_target_exchange_descent (cs : CScalars Sc) (μ : X)
    (a P Q : List (Letter I)) (i : I)
    (hG : BoundaryIndependence cs μ a (P ++ dn i :: up i :: Q))
    (hB : BoundaryIndependence cs μ a (P ++ Q)) :
    BoundaryIndependence cs μ a (P ++ up i :: dn i :: Q) := by
  intro hab A
  let F := Classical.choice (sameColourTargetFrame_nonempty cs μ a P Q i)
  have hswap : wt D 0 a = wt D 0 (P ++ dn i :: up i :: Q) :=
    hab.trans (wt_context_opposite_swap 0 P Q i i).symm
  have hres : wt D 0 a = wt D 0 (P ++ Q) :=
    hswap.trans (wt_context_pair_delete 0 P Q i)
  exact A.expansion_injective_of_choice cs μ F.original
    (F.originalExpansion_injective (hG hswap F.swapped) (hB hres F.residual))

/-- Full contextual target descent for equal and distinct colours. -/
theorem target_exchange_descent (cs : CScalars Sc) : TargetExchangeDescent cs := by
  intro μ a P Q i j hG hB
  by_cases hij : i = j
  · subst j
    exact same_colour_target_exchange_descent cs μ a P Q i hG (hB rfl)
  · exact distinct_target_exchange_descent cs μ a P Q i j hij hG

#print axioms same_colour_target_exchange_descent
#print axioms target_exchange_descent
end OddMath.SKM
