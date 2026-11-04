import OddMath.QuiverHecke.SwappedAssembly.ReservoirWordFunctor
import StringDiagrams.Super.PiTwo

/-! # The reservoir word comparison is an identity transport in `Π-𝔖ℭ𝔞𝔱`

SwappedVacuumCoordinates §2: in the strict 2-supercategory `Π-𝔖ℭ𝔞𝔱` every
unitor and associator is an identity, so the comparison of a vacuum path
functor with postcomposition by its reservoir induction word is an
equality transport at every object. Chart changes built from it therefore
introduce no coefficient: they only reindex the target word.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u

local instance reservoirWordStrictHomPi {k : Type u} [CommRing k] (A C : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ C) := PiTwoSupercategory.homPiLeft A C

/-- An arrow heterogeneously equal to an equality transport, along equal
endpoints, is itself an equality transport. -/
theorem exists_eqToHom_of_heq {C : Type*} [Category C] {A B A' B' : C}
    (f : A ⟶ B) (g : A' ⟶ B') (hA : A = A') (hB : B = B') (hfg : HEq f g)
    (hg : ∃ h, g = eqToHom h) : ∃ h, f = eqToHom h := by
  subst hA hB
  cases eq_of_heq hfg
  exact hg

/-- Composites of equality transports are equality transports. -/
theorem exists_eqToHom_comp {C : Type*} [Category C] {A B B' : C}
    (f : A ⟶ B) (g : B ⟶ B') (hf : ∃ h, f = eqToHom h) (hg : ∃ h, g = eqToHom h) :
    ∃ h, f ≫ g = eqToHom h := by
  obtain ⟨h, rfl⟩ := hf
  obtain ⟨h', rfl⟩ := hg
  exact ⟨h.trans h', eqToHom_trans h h'⟩

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {D : Datum I X} {Sc : Scalars D k}

/-- Right whiskering of an equality transport in `Π-𝔖ℭ𝔞𝔱` is an equality
transport. -/
theorem exists_eqToHom_whiskerRight {A B C : PiSCat.{u,u,u + 1} k} {F G : A ⟶ B}
    (f : F ⟶ G) (E : B ⟶ C) (hf : ∃ h, f = eqToHom h) : ∃ h, f ▷ E = eqToHom h := by
  obtain ⟨h, rfl⟩ := hf
  subst h
  exact ⟨rfl, by simp only [eqToHom_refl, TwoSupercategory.id_whiskerRight (R := k)]⟩

namespace ProbeReservoir
variable (P : ProbeReservoir k (PiSCat.{u,u,u + 1} k) D Sc)

/-- In `Π-𝔖ℭ𝔞𝔱` the reservoir word comparison of every upward vacuum path
is an equality transport at every object. -/
theorem reservoirWordFunctorIso_hom_app_eqToHom {l : List (Col I X)} {c d : I →₀ ℕ}
    (p : SPath l (0, c) (0, d)) (hl : ∀ a ∈ l, a.l.1 = true) (Z : P.H (0, d)) :
    ∃ h, (P.reservoirWordFunctorIso p hl).hom.app Z = eqToHom h := by
  induction l generalizing c with
  | nil =>
    cases p
    refine exists_eqToHom_of_heq _ (rightUnitor Z).inv rfl ?_
      (P.reservoirWordFunctorIso_nil_hom_heq d Z) ⟨rfl, rfl⟩
    exact congrArg (fun w => Z ≫ w) (ReservoirWord.word_nil P.W.toRouquierData P.ΛR d)
  | cons a l ih =>
    cases p with
    | cons a side s hv p =>
      have ha := hl a List.mem_cons_self
      have ht : ∀ b ∈ l, b.l.1 = true := fun b hb => hl b (List.mem_cons_of_mem _ hb)
      rcases a with ⟨⟨b, i⟩, r⟩
      cases b with
      | false => cases ha
      | true =>
        have hs := SPath.side_eq_false_of_upward_probe_zero i side p ht rfl
        subst side
        let E := P.W.E i (show ReservoirWord.weight D P.ΛR (c - Finsupp.single i 1) + D.α i =
            ReservoirWord.weight D P.ΛR c by
          simp only [ReservoirWord.weight]
          rw [add_assoc, contentWeight_sub_single hv])
        have hstep : P.step (true, i) false (0, c) hv = homPost (k := k) E := by
          simp only [step, homContentPostE, homContentShift, contentParity, map_zero,
            mul_zero, homParityShift_zero, Functor.comp_id]
          rfl
        have hF : P.pathFunctor (.cons ⟨(true,i),r⟩ false (0,c) hv p) =
            P.pathFunctor p ⋙ homPost (k := k) E := by
          rw [pathFunctor_cons, hstep]
        refine exists_eqToHom_of_heq _ _
          (congrArg (fun F => F.obj Z) hF)
          (congrArg (fun w => Z ≫ w)
            (ReservoirWord.word_cons P.W.toRouquierData P.ΛR i r hv p ht))
          (P.reservoirWordFunctorIso_cons_hom_heq i r hv p ht Z) ?_
        exact exists_eqToHom_comp _ _
          (exists_eqToHom_whiskerRight _ E (ih p ht Z)) ⟨rfl, rfl⟩

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
