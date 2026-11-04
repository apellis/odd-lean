import OddMath.QuiverHecke.CyclotomicAction.ELVProbeWeightLoopDot
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeUpperLoopDot

/-! # The whole-weight raw vacuum dot in the cap source chart

SwappedActionAssembly F2 and SwappedVacuumNonpositiveBubbles §1 (2):
transport the literal restricted probe dot through precisely the source
isomorphism used for the normalized whole-weight cap.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open CyclotomicAction BalancedInduction CyclotomicCrossingTensor
attribute [local irreducible] probeAppendUpperLoopSuperIso
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

/-- The dot before selecting any source comparison. -/
def evaluatedLoopDot (ν : List I) (i : I) (N : ProbeEvaluatedModules D Sc m ν) :
    End ((probeEvaluatedRestriction D Sc m ν i).obj
      ((probeEvaluatedInduction D Sc m ν i).obj N)) :=
  (probeEvaluatedRestriction D Sc m ν i).map
    (probeAppendToDotComponent D Sc m ν i (i :: ν) (List.Perm.refl _) N)

/-- The OLD upper-loop comparison preserves the raw dot on every input. -/
theorem upperLoop_dot (ν : List I) (i : I) {μ : List I}
    (perm : (i :: ν).Perm μ) (N : ProbeEvaluatedModules D Sc m ν) :
    evaluatedLoopDot D Sc m ν i N ≫
      (probeAppendUpperLoopSuperIso D Sc m ν i perm).hom.total N =
    (probeAppendUpperLoopSuperIso D Sc m ν i perm).hom.total N ≫
      (probeEvaluatedRestrictTo D Sc m ν i μ perm).map
        (probeAppendToDotComponent D Sc m ν i μ perm N) := by
  apply InducedCategory.hom_ext
  change (evaluatedLoopDot D Sc m ν i N).hom ≫
      ((probeAppendUpperLoopSuperIso D Sc m ν i perm).hom.total N).hom =
    ((probeAppendUpperLoopSuperIso D Sc m ν i perm).hom.total N).hom ≫ _
  rw [probeAppendUpperLoopSuperIso_hom_total]
  exact oldAppendUpperLoop_dot D Sc m ν i perm N.obj

/-- Empty-content forgetting keeps this entire dot map. -/
theorem forgetEmpty_upper_dot (ν : List I) (hν : ν = []) (i : I)
    (N : ProbeEvaluatedModules D Sc m ν) :
    (emptyContentForget D Sc m ν hν).map (evaluatedLoopDot D Sc m ν i N) ≫
      eqToHom (forgetEmpty_upper_obj D Sc m ν hν i N) =
    eqToHom (forgetEmpty_upper_obj D Sc m ν hν i N) ≫
      restrictedDotEnd (oldContentAppend D Sc (probeCutoff D m) [] i)
        (probeOldContentAppendDot_supernatural D Sc m [] i)
        ((emptyContentForget D Sc m ν hν).obj N) := by
  subst ν
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  rfl

private def totalEvaluation {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A] (N : C) :
    Superfunctor k C A ⥤ A where
  obj F := F.obj N
  map f := f.total N
  map_id F := SuperNatTrans.id_total F.toFunctor N
  map_comp f g := Superfunctor.comp_total f g N

private theorem inverse_square {C : Type*} [Category C] {A B : C}
    (e : A ≅ B) (f : End A) (g : End B) (h : f ≫ e.hom = e.hom ≫ g) :
    g ≫ e.inv = e.inv ≫ f := by
  apply (cancel_epi e.hom).mp
  rw [← Category.assoc, ← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

private theorem four_squares {C : Type*} [Category C] {A B E F G : C}
    (a : A ≅ B) (b : B ≅ E) (c : E ≅ F) (d : F ≅ G)
    (x : End A) (y : End B) (z : End E) (v : End F) (w : End G)
    (ha : x ≫ a.hom = a.hom ≫ y) (hb : y ≫ b.hom = b.hom ≫ z)
    (hc : z ≫ c.hom = c.hom ≫ v) (hd : v ≫ d.hom = d.hom ≫ w) :
    x ≫ (a ≪≫ b ≪≫ c ≪≫ d).hom = (a ≪≫ b ≪≫ c ≪≫ d).hom ≫ w := by
  simp only [Iso.trans_hom, Category.assoc]
  rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, hd]

private theorem family_eqToHom {C : Type*} [Category C] (F : C ⥤ C)
    (a : ∀ N, End (F.obj N)) {M N : C} (h : M = N) :
    a M ≫ F.map (eqToHom h) = F.map (eqToHom h) ≫ a N := by
  subst N
  simp

private theorem emptyBlock_list (Λ : X) :
    (emptyBlock D Λ).1.toList = [] := Multiset.toList_zero

variable [Fintype I] (Λ : X) (i : I) {y : X} (edge : -Λ + D.α i = y)
local notation "δ₀" => emptyBlock D Λ
local notation "N₀" => regularProbe D Sc m Λ
local notation "γ₀" => Multiset.toList (Subtype.val (emptyBlock D Λ))
local notation "perm" => probeOldBlockTarget_perm D i Λ edge δ₀ (blockSucc D Λ i edge δ₀) rfl
local notation "F₀" => emptyContentForget D Sc m γ₀ (emptyBlock_list D Λ)
local notation "K" => oldContentAppend D Sc (probeCutoff D m) [] i

/-- The literal whole-weight raw upper-loop dot retains its empty block. -/
def vacuumLoopDot :
    End ((emptyProbe D Sc m Λ).obj
      (((probeOldE D Sc m i Λ edge) ≫ (probeOldF D Sc m i Λ edge)).obj N₀)) :=
  (emptyProbe D Sc m Λ).map
    ((probeOldActionDot D Sc m i Λ edge ▷ probeOldF D Sc m i Λ edge).total N₀)

/-- The raw whole-weight dot and the prescribed module dot commute with
exactly the cap's four-factor source chart. -/
theorem vacuumLoopDot_source :
    vacuumLoopDot D Sc m Λ i edge ≫ (vacuumCapSourceIso D Sc m Λ i edge).hom =
      (vacuumCapSourceIso D Sc m Λ i edge).hom ≫ ProbeVacuumCap.moduleDot D Sc m i := by
  let e := (totalEvaluation (N₀ δ₀)).mapIso
    (probeAppendUpperLoopSuperIso D Sc m γ₀ i perm)
  have h₁ := congrArg (F₀).map
    (probeOldWeightFollowing_dot D Sc m i Λ edge δ₀ N₀)
  rw [Functor.map_comp, Functor.map_comp] at h₁
  have hu := upperLoop_dot D Sc m γ₀ i perm (N₀ δ₀)
  have hu' := inverse_square e (evaluatedLoopDot D Sc m γ₀ i (N₀ δ₀))
    ((probeEvaluatedRestrictTo D Sc m γ₀ i _ perm).map
      (probeAppendToDotComponent D Sc m γ₀ i _ perm (N₀ δ₀))) hu
  have h₂ := congrArg (F₀).map hu'
  rw [Functor.map_comp, Functor.map_comp] at h₂
  have h₃ := forgetEmpty_upper_dot D Sc m γ₀ (emptyBlock_list D Λ) i (N₀ δ₀)
  have h₄ := family_eqToHom ((induction K) ⋙ (restriction K))
    (fun N => restrictedDotEnd K (probeOldContentAppendDot_supernatural D Sc m [] i) N)
    (emptyProbe_regular D Sc m Λ)
  let a := (F₀).mapIso (eqToIso (probeOldWeightFollowing_obj D Sc m i Λ edge δ₀ N₀))
  let b := (F₀).mapIso e.symm
  let c := eqToIso (forgetEmpty_upper_obj D Sc m γ₀ (emptyBlock_list D Λ) i (N₀ δ₀))
  let d := ((induction K) ⋙ (restriction K)).mapIso (eqToIso (emptyProbe_regular D Sc m Λ))
  let y := (F₀).map ((probeEvaluatedRestrictTo D Sc m γ₀ i _ perm).map
    (probeAppendToDotComponent D Sc m γ₀ i _ perm (N₀ δ₀)))
  let z := (F₀).map (evaluatedLoopDot D Sc m γ₀ i (N₀ δ₀))
  let v := restrictedDotEnd K (probeOldContentAppendDot_supernatural D Sc m [] i) ((F₀).obj (N₀ δ₀))
  have ha : vacuumLoopDot D Sc m Λ i edge ≫ a.hom = a.hom ≫ y := by
    convert h₁ using 1 <;> rfl
  have hb : y ≫ b.hom = b.hom ≫ z := by
    convert h₂ using 1 <;> rfl
  have hc : z ≫ c.hom = c.hom ≫ v := h₃
  have hd : v ≫ d.hom = d.hom ≫ ProbeVacuumCap.moduleDot D Sc m i := by
    convert h₄ using 1 <;> rfl
  have hf := four_squares a b c d (vacuumLoopDot D Sc m Λ i edge) y z v
    (ProbeVacuumCap.moduleDot D Sc m i) ha hb hc hd
  convert hf using 1 <;> rfl

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
