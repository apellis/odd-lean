/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.GradedTwoEnvelopeFunctor
import OddMath.SKM.ChevalleyQTwoGraded
import StringDiagrams.Super.PiSOpTwo
import OddMath.SKM.ChevalleyQPiHom

/-!
# The Chevalley involution on the `(Q,Π)`-envelope

[BE2] J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Proposition
9.3 (construction of `ω̃`, via Lemma 9.1): the graded 2-superfunctor

  `ω̃ : 𝔘_{q,π}(𝔤) → 𝔘_{q,π}(𝔤)^{sop}`  (`chevalleyQPiTwo`),

the Π-envelope of `chevalleyQTwo` followed by `PiSOp.twoFunctor`. On objects `λ ↦ -λ`
(`chevalleyQPiTwo_obj`), on 1-morphisms `Qᵐ Πᵃ F ↦ Q⁻ᵐ Πᵃ ω(F)`, in particular `Qᵐ Πᵃ Eᵢ 1_λ ↦
Q⁻ᵐ Πᵃ Fᵢ 1_{-λ}` and `Qᵐ Πᵃ Fᵢ 1_λ ↦ Q⁻ᵐ Πᵃ Eᵢ 1_{-λ}` (`chevalleyQPiTwo_map`), on 2-morphisms
by `chevQPiHom` (`chevalleyQPiTwo_map₂`); its composition comparison carries the sign
`(-1)^{ab}` (`chevalleyQPiTwo_mapComp`), so `ω̃` is not strict, as noted after Remark 9.2. It is
graded (`chevalleyQPiTwo_isGraded`), every hom functor is a graded superequivalence and it is
surjective on objects (`chevalleyQPiTwo_isLocalTwoSuperequivalence`).

The assertion of Proposition 9.3 that `ω̃` is an isomorphism is proved in the adjoint
biequivalence reading in `OddMath.SKM.ChevalleyQPiBiequivalence`
(`chevalleyQPiTwo_isAdjointBiequivalence`).
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory GradedSupercategory BicategoryStruct
open TwoSupercategory
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- **[BE2] Proposition 9.3** (the 2-superfunctor `ω̃`):
`ω̃ : 𝔘_{q,π}(𝔤) → 𝔘_{q,π}(𝔤)^{sop}`. -/
def chevalleyQPiTwo :
    TwoSuperfunctor k (QPiTwoEnvelope k (UGr D Sc sy hc))
      (TwoSOp k (QPiTwoEnvelope k (UGr D Sc sy hc))) :=
  (TwoEnvelope.mapPi (chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc))).comp
    PiSOp.twoFunctor

local notation "F" => chevalleyQPiTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc)
local notation "L" => TwoEnvelope.mapPi
  (chevalleyQTwo (D := D) (Sc := Sc) (sy := sy) (hc := hc))
local notation "P" => PiSOp.twoFunctor (R := k) (B := QTwoEnvelope k (UGr D Sc sy hc))

/-- The hom functors of `ω̃` are `chevQPiHom`. -/
theorem chevalleyQPiTwo_mapFunctor (a b : QPiTwoEnvelope k (UGr D Sc sy hc)) :
    (F).mapFunctor a b = chevQPiHom a.as.as b.as.as := rfl

/-- The hom functors of `ω̃`, unfolded. -/
theorem chevalleyQPiTwo_mapFunctor_mk (x y : UGr D Sc sy hc) :
    (F).mapFunctor ⟨⟨x⟩⟩ ⟨⟨y⟩⟩ = Envelope.map k (chevQHom x y) ⋙ PiSOp.bridge := rfl

/-- `ω̃` sends `λ` to `-λ`. -/
theorem chevalleyQPiTwo_obj (a : QPiTwoEnvelope k (UGr D Sc sy hc)) :
    (F).obj a = TwoSOp.mk ⟨⟨negWeight a.as.as⟩⟩ := rfl

/-- `ω̃(Qᵐ Πᵃ F) = Q⁻ᵐ Πᵃ ω(F)`. -/
theorem chevalleyQPiTwo_map {a b : QPiTwoEnvelope k (UGr D Sc sy hc)} (f : a ⟶ b) :
    SOp.unop ((F).map f) = ⟨f.par, ⟨-f.obj.shift, chevHomObj f.obj.obj⟩⟩ := rfl

/-- `ω̃` on 2-morphisms is `chevQPiHom`. -/
theorem chevalleyQPiTwo_map₂ {a b : QPiTwoEnvelope k (UGr D Sc sy hc)}
    {f g : a ⟶ b} (η : f ⟶ g) :
    (F).map₂ η = (chevQPiHom a.as.as b.as.as).map η := rfl

/-- The composition comparison of `ω̃`: the sign `(-1)^{ab}` of `PiSOp.twoFunctor`
followed by the Π-envelope of the comparison of `chevalleyQTwo`. -/
theorem chevalleyQPiTwo_mapComp {a b c : QPiTwoEnvelope k (UGr D Sc sy hc)}
    (f : a ⟶ b) (g : b ⟶ c) :
    (F).mapComp f g = (P).mapComp ((L).map f) ((L).map g) ≪≫
      (P).map₂Iso ((L).mapComp f g) := rfl

/-- `ω̃` is graded, with degree-zero comparison maps. -/
theorem chevalleyQPiTwo_isGraded : (F).IsGraded where
  map₂_mem_degree {a b _ _ _ _} h :=
    (chevQPiHom_graded a.as.as b.as.as).map_mem_degree h
  mapComp_hom_mem_degree f g := by
    have h := comp_mem_degree
      (PiSOp.twoFunctor_isGraded.mapComp_hom_mem_degree ((L).map f) ((L).map g))
      (PiSOp.twoFunctor_isGraded.map₂_mem_degree
        ((TwoEnvelope.mapPi_isGraded chevalleyQTwo_isGraded).mapComp_hom_mem_degree f g))
    rw [add_zero] at h
    exact h
  mapId_hom_mem_degree a := by
    have h := comp_mem_degree
      (PiSOp.twoFunctor_isGraded.mapId_hom_mem_degree ((L).obj a))
      (PiSOp.twoFunctor_isGraded.map₂_mem_degree
        ((TwoEnvelope.mapPi_isGraded chevalleyQTwo_isGraded).mapId_hom_mem_degree a))
    rw [add_zero] at h
    exact h

/-- Every hom functor of `ω̃` is a graded superequivalence. -/
def chevalleyQPiTwo_homGradedEquivalence (a b : QPiTwoEnvelope k (UGr D Sc sy hc)) :
    GradedSuperequivalence k ((F).mapFunctor a b) :=
  chevQPiHomGradedEquivalence a.as.as b.as.as

/-- `ω̃` is surjective on objects. -/
theorem chevalleyQPiTwo_obj_surjective : Function.Surjective (F).obj := by
  intro c
  refine ⟨⟨⟨negWeight c.unop.as.as⟩⟩, ?_⟩
  apply congrArg TwoSOp.mk
  apply TwoEnvelope.ext
  apply QTwoEnvelope.ext
  apply Presentation.Bicat.ext
  exact neg_neg (show X from c.unop.as.as.region)

/-- `ω̃` is a local 2-superequivalence. -/
theorem chevalleyQPiTwo_isLocalTwoSuperequivalence : (F).IsLocalTwoSuperequivalence where
  hom a b := ⟨(chevalleyQPiTwo_homGradedEquivalence a b).toSuperequivalence⟩
  essSurj c := by
    obtain ⟨a, ha⟩ := chevalleyQPiTwo_obj_surjective c
    exact ⟨a, ha.symm ▸ Superequivalent.refl c⟩
end OddMath.SKM
