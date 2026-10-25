import OddMath.SKM.SameColourSourceKernel
import OddMath.SKM.PairedSourceIndependence
import OddMath.SKM.DistinctSourceDescent

/-! Same-colour source exchange descent over the full coefficient algebra. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}
namespace SameColourSourceFrame
variable {cs : CScalars Sc} {μ : X} {P Q Z : List (Letter I)} {i : I}
  (F : SameColourSourceFrame P Q Z i)

/-- Full same-colour source-family descent, not merely paired-sector descent. -/
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
      apply F.pairedExpansion_injective cs μ hG hB
      change F.original.expansion cs μ (F.originalPairedInclusion g) = F.pairedExpansion cs μ 0
      rw [hg, hf, map_zero]
    rw [← hg, hgz, map_zero]
  intro f g he
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, he, sub_self]

end SameColourSourceFrame

theorem same_colour_source_exchange_descent (cs : CScalars Sc) (μ : X)
    (P Q Z : List (Letter I)) (i : I)
    (hG : BoundaryIndependence cs μ (P ++ up i :: dn i :: Q) Z)
    (hB : BoundaryIndependence cs μ (P ++ Q) Z) :
    BoundaryIndependence cs μ (P ++ dn i :: up i :: Q) Z := by
  intro hab A
  let F := Classical.choice (sameColourSourceFrame_nonempty P Q Z i)
  have hswap : wt D 0 (P ++ up i :: dn i :: Q) = wt D 0 Z :=
    (wt_context_opposite_swap 0 P Q i i).symm.trans hab
  have hres : wt D 0 (P ++ Q) = wt D 0 Z :=
    (wt_context_pair_delete 0 P Q i).symm.trans hab
  exact A.expansion_injective_of_choice cs μ F.original
    (F.originalExpansion_injective (hG hswap F.swapped) (hB hres F.residual))

theorem source_exchange_descent (cs : CScalars Sc) : SourceExchangeDescent cs := by
  intro μ P Q i j Z hG hB
  by_cases hij : i = j
  · subst j
    exact same_colour_source_exchange_descent cs μ P Q Z i hG (hB rfl)
  · exact distinct_source_exchange_descent cs μ P Q Z i j hij hG

#print axioms same_colour_source_exchange_descent
#print axioms source_exchange_descent
end OddMath.SKM
