import OddMath.QuiverHecke.CyclotomicAction.ProbeReindexMate
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend
import OddMath.QuiverHecke.CyclotomicAction.WeightMixed
import OddMath.SKM.AugmentedInverseNaturality
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDot
import OddMath.QuiverHecke.CyclotomicAction.InductionGridRouquier
import OddMath.QuiverHecke.CyclotomicAction.RouquierPowerWords
import OddMath.QuiverHecke.CyclotomicAction.DistinctSlides
import OddMath.QuiverHecke.CyclotomicAction.ParameterUntwist

/-!
# Probe weight pair dots

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients: the two whiskered dots and the distinct-colour crossing on
two-step weight induction of the probe, in block coordinates (Brundan–Ellis,
arXiv:1701.04133v2, (1.8)). These comparisons do not use the loop reindexing of
`ProbeReindexWeight`, so the braid relations can be built without it. Each section
below was a separate file; its docstring describes it.
-/

section

/-! # The chosen OLD probe dots on two-step weight induction

Brundan–Ellis (1.8): identify both independently whiskered global dots
in the same literal stored-target coordinates as the chosen equal crossing.
The identities retain all input modules and every parity component; they
supply the comparison required by the signed two-strand slide equations.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELV CyclotomicAction
universe u v w t z

private theorem outerDot_conjugate
    {k : Type u} [CommRing k] {C : Type v} [Category.{w} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {A : Type t} [Category.{z} A] [Preadditive A] [Linear k A] [Supercategory k A]
    (G : C ⥤ A) {M₀ M₁ : C} (hM : M₀ = M₁) {V : A}
    (hV : V = G.obj M₀) (hW : V = G.obj M₁) (d : SuperNatTrans k G G) (p : ZMod 2) :
    eqToHom hV ≫ d.app p M₀ ≫ eqToHom hV.symm =
      eqToHom hW ≫ d.app p M₁ ≫ eqToHom hW.symm := by
  cases hM
  cases hV
  cases hW
  rfl

private theorem innerDot_conjugate
    {C : Type v} [Category.{w} C] {A : Type t} [Category.{z} A]
    (G : C ⥤ A) {M₀ M₁ : C} (hM : M₀ = M₁) {V : A}
    (hV : V = G.obj M₀) (hW : V = G.obj M₁) (d : End M₁) :
    eqToHom hV ≫ G.map (eqToHom hM ≫ d ≫ eqToHom hM.symm) ≫ eqToHom hV.symm =
      eqToHom hW ≫ G.map d ≫ eqToHom hW.symm := by
  cases hM
  cases hV
  cases hW
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

section Pair
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i j : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = x₂)

/-- The selected pair coordinate retains two independently chosen colours. -/
theorem probeOldWeightPair₂_obj_eq (β : WeightBlocks D Λ x₀)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldEFunctor D Sc m j Λ h₁ ⋙
      (probeOldInductionComponent D Sc m i Λ h₂ (blockSucc₂ D i j Λ h₁ h₂ β)).toFunctor).obj M =
      (probeOldBlockPairInd D Sc m i j Λ h₁ h₂ β).obj (M β) :=
  congrArg (fun H => H.obj M) (probeOldEFunctor_comp₂_blockSucc D Sc m i j Λ h₁ h₂ β)

/-- The outer independently chosen global dot uses the exact pair coordinate equality. -/
theorem probeOldPairOuterDot_component (β : WeightBlocks D Λ x₀)
    (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    ((probeOldE D Sc m j Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).app p M)
        (blockSucc₂ D i j Λ h₁ h₂ β) =
      eqToHom (probeOldWeightPair₂_obj_eq D Sc m i j Λ h₁ h₂ β M) ≫
        (probeOldBlockDot D Sc m i Λ h₂ (blockSucc D Λ j h₁ β)).app p
          ((probeOldBlockInd D Sc m j Λ h₁ β).obj (M β)) ≫
        eqToHom (probeOldWeightPair₂_obj_eq D Sc m i j Λ h₁ h₂ β M).symm := by
  change probeOldWeightDotComponent D Sc m i Λ h₂ p
    ((probeOldEFunctor D Sc m j Λ h₁).obj M) (blockSucc₂ D i j Λ h₁ h₂ β) = _
  rw [probeOldWeightDotComponent_blockSucc]
  exact outerDot_conjugate
    (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ j h₁ β)).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m j Λ h₁ β M) _
    (probeOldWeightPair₂_obj_eq D Sc m i j Λ h₁ h₂ β M)
    (probeOldBlockDot D Sc m i Λ h₂ (blockSucc D Λ j h₁ β)) p

/-- The inner independently chosen global dot uses the identical pair coordinate equality. -/
theorem probeOldPairInnerDot_component (β : WeightBlocks D Λ x₀)
    (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    ((probeOldActionDot D Sc m j Λ h₁ ▷ probeOldE D Sc m i Λ h₂).app p M)
        (blockSucc₂ D i j Λ h₁ h₂ β) =
      eqToHom (probeOldWeightPair₂_obj_eq D Sc m i j Λ h₁ h₂ β M) ≫
        (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ j h₁ β)).map
          ((probeOldBlockDot D Sc m j Λ h₁ β).app p (M β)) ≫
        eqToHom (probeOldWeightPair₂_obj_eq D Sc m i j Λ h₁ h₂ β M).symm := by
  change (probeOldInductionComponent D Sc m i Λ h₂ (blockSucc₂ D i j Λ h₁ h₂ β)).map
    ((probeOldActionDot D Sc m j Λ h₁).app p M) = _
  rw [probeOldInductionComponent_map_blockSucc]
  change eqToHom _ ≫ (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ j h₁ β)).map
    (probeOldWeightDotComponent D Sc m j Λ h₁ p M (blockSucc D Λ j h₁ β)) ≫ eqToHom _ = _
  rw [probeOldWeightDotComponent_blockSucc]
  exact innerDot_conjugate
    (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ j h₁ β)).toFunctor
    (probeOldInductionComponent_obj_blockSucc D Sc m j Λ h₁ β M) _
    (probeOldWeightPair₂_obj_eq D Sc m i j Λ h₁ h₂ β M) _

end Pair

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (i : I) (Λ : X) {x₀ x₁ x₂ : X}
  (h₁ : x₀ + D.α i = x₁) (h₂ : x₁ + D.α i = x₂)

/-- The outer independently chosen global dot uses the exact pair coordinate equality. -/
theorem probeOldOuterDot_component (β : WeightBlocks D Λ x₀)
    (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    ((probeOldE D Sc m i Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).app p M)
        (blockSucc₂ D i i Λ h₁ h₂ β) =
      eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M) ≫
        (probeOldBlockDot D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)).app p
          ((probeOldBlockInd D Sc m i Λ h₁ β).obj (M β)) ≫
        eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M).symm :=
  probeOldPairOuterDot_component D Sc m i i Λ h₁ h₂ β p M

/-- The inner independently chosen global dot uses the identical pair coordinate equality. -/
theorem probeOldInnerDot_component (β : WeightBlocks D Λ x₀)
    (p : ZMod 2) (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    ((probeOldActionDot D Sc m i Λ h₁ ▷ probeOldE D Sc m i Λ h₂).app p M)
        (blockSucc₂ D i i Λ h₁ h₂ β) =
      eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M) ≫
        (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ i h₁ β)).map
          ((probeOldBlockDot D Sc m i Λ h₁ β).app p (M β)) ≫
        eqToHom (probeOldWeightPair_obj_eq D Sc m i Λ h₁ h₂ β M).symm :=
  probeOldPairInnerDot_component D Sc m i i Λ h₁ h₂ β p M

end OddMath.QuiverHecke
end

end

section

/-! # Distinct-colour slides on every OLD probe weight

Brundan–Ellis (1.8): both independently chosen dots and the positive
crossing are compared through their exact source and target coordinates.
Absent predecessor blocks use their constructed zero object.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open CyclotomicAction
universe u
private theorem distinct_total_smul {k C A : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : Superfunctor k C A} (a : k) (f : F ⟶ G) (N : C) :
    (a • f).total N = a • f.total N := by
  change a • f.app 0 N + a • f.app 1 N = a • (f.app 0 N + f.app 1 N)
  exact (smul_add _ _ _).symm

private theorem distinct_conjugate_slide {k C : Type*} [CommRing k]
    [Category C] [Preadditive C] [Linear k C]
    {A A' B B' : C} (e : A = A') (f : B = B') (c : A' ⟶ B')
    (b : End B') (d : End A') (a : k) (h : c ≫ b = a • (d ≫ c)) :
    (eqToHom e ≫ c ≫ eqToHom f.symm) ≫ (eqToHom f ≫ b ≫ eqToHom f.symm) =
      a • ((eqToHom e ≫ d ≫ eqToHom e.symm) ≫ (eqToHom e ≫ c ≫ eqToHom f.symm)) := by
  cases e
  cases f
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
section Pair
variable (i j : I) (Λ : X) {x₀ x₁ xu : X}
  (h₁ : x₀ + D.α j = x₁) (h₂ : x₁ + D.α i = xu)

private theorem pairUpperDot_eq (β : WeightBlocks D Λ x₀) :
    probeOldPairUpperDot D Sc m i j Λ h₁ h₂ β _ rfl =
      probeOldBlockDot D Sc m i Λ h₂ (blockSucc D Λ j h₁ β) := rfl

private theorem pairOuterDotTo_app (β : WeightBlocks D Λ x₀) (p : ZMod 2)
    (N : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockPairOuterDotTo D Sc m i j Λ h₁ h₂ β _ rfl).app p N =
      (probeOldBlockDot D Sc m i Λ h₂ (blockSucc D Λ j h₁ β)).app p
        ((probeOldBlockInd D Sc m j Λ h₁ β).obj N) := by
  rw [← pairUpperDot_eq]
  rfl

private theorem pairOuterDotTo_total (β : WeightBlocks D Λ x₀)
    (N : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockPairOuterDotTo D Sc m i j Λ h₁ h₂ β _ rfl).total N =
      (probeOldBlockDot D Sc m i Λ h₂ (blockSucc D Λ j h₁ β)).total
        ((probeOldBlockInd D Sc m j Λ h₁ β).obj N) := by
  rw [SuperNatTrans.total, SuperNatTrans.total, pairOuterDotTo_app, pairOuterDotTo_app]

private theorem pairInnerDotTo_app (β : WeightBlocks D Λ x₀) (p : ZMod 2)
    (N : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockPairInnerDotTo D Sc m i j Λ h₁ h₂ β _ rfl).app p N =
      (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ j h₁ β)).map
        ((probeOldBlockDot D Sc m j Λ h₁ β).app p N) := rfl

private theorem pairInnerDotTo_total (β : WeightBlocks D Λ x₀)
    (N : ProbeCanonicalModules D Sc m β.1) :
    (probeOldBlockPairInnerDotTo D Sc m i j Λ h₁ h₂ β _ rfl).total N =
      (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ j h₁ β)).map
        ((probeOldBlockDot D Sc m j Λ h₁ β).app 0 N) +
      (probeOldBlockInd D Sc m i Λ h₂ (blockSucc D Λ j h₁ β)).map
        ((probeOldBlockDot D Sc m j Λ h₁ β).app 1 N) := by
  rw [SuperNatTrans.total, pairInnerDotTo_app, pairInnerDotTo_app]

theorem probeOldPairOuterDotTo_total (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldE D Sc m j Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).total M ε =
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε) M) ≫
        (probeOldBlockPairOuterDotTo D Sc m i j Λ h₁ h₂ β ε hε).total (M β) ≫
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε) M).symm := by
  subst ε
  change (probeOldE D Sc m j Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).app 0 M _ +
    (probeOldE D Sc m j Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).app 1 M _ = _
  rw [probeOldPairOuterDot_component, probeOldPairOuterDot_component,
    ← Preadditive.comp_add, ← Preadditive.add_comp, pairOuterDotTo_total]
  rfl

theorem probeOldPairInnerDotTo_total (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldActionDot D Sc m j Λ h₁ ▷ probeOldE D Sc m i Λ h₂).total M ε =
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε) M) ≫
        (probeOldBlockPairInnerDotTo D Sc m i j Λ h₁ h₂ β ε hε).total (M β) ≫
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε) M).symm := by
  subst ε
  change (probeOldActionDot D Sc m j Λ h₁ ▷ probeOldE D Sc m i Λ h₂).app 0 M _ +
    (probeOldActionDot D Sc m j Λ h₁ ▷ probeOldE D Sc m i Λ h₂).app 1 M _ = _
  rw [probeOldPairInnerDot_component, probeOldPairInnerDot_component,
    ← Preadditive.comp_add, ← Preadditive.add_comp, pairInnerDotTo_total]
end Pair
section Crossing
variable (i j : I) (Λ : X) {x₀ xj xi xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
local notation "sw" => blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄

theorem probeOldActionDistinctCross_total_of (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ xu) (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε)
    (M : ProbeOldWeightProduct D Sc m Λ x₀) :
    (probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).total M ε =
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m i j Λ h₁ h₂ β ε hε) M) ≫
        (probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).total (M β) ≫
      eqToHom (Functor.congr_obj (probeOldEFunctor_comp₂_to D Sc m j i Λ h₃ h₄ β ε (sw hε)) M).symm := by
  change probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ 0 M ε +
    probeOldWeightDistinctCrossComponent D Sc m i j Λ h₁ h₂ h₃ h₄ 1 M ε = _
  rw [probeOldWeightDistinctCrossComponent_of D Sc m i j Λ h₁ h₂ h₃ h₄ 0 M β ε hε,
      probeOldWeightDistinctCrossComponent_of D Sc m i j Λ h₁ h₂ h₃ h₄ 1 M β ε hε,
      probeOldWeightDistinctCrossVia_component, probeOldWeightDistinctCrossVia_component]
  change _ = eqToHom _ ≫
    ((probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app 0 (M β) +
     (probeOldBlockDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hε).app 1 (M β)) ≫ eqToHom _
  rw [Preadditive.add_comp, Preadditive.comp_add]

theorem probeOldActionDistinctCross_slide_inner (hij : i ≠ j) :
    probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ ≫ (probeOldActionDot D Sc m i Λ h₃ ▷ probeOldE D Sc m j Λ h₄) =
      sign k (D.parity i * D.parity j) •
        ((probeOldE D Sc m j Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂) ≫ probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [Superfunctor.comp_total, distinct_total_smul, Superfunctor.comp_total]
  funext ε
  change (probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).total M ε ≫
      (probeOldActionDot D Sc m i Λ h₃ ▷ probeOldE D Sc m j Λ h₄).total M ε =
    sign k (D.parity i * D.parity j) •
      ((probeOldE D Sc m j Λ h₁ ◁ probeOldActionDot D Sc m i Λ h₂).total M ε ≫
        (probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).total M ε)
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [probeOldActionDistinctCross_total_of D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hβ,
      probeOldPairInnerDotTo_total D Sc m j i Λ h₃ h₄ β ε (sw hβ),
      probeOldPairOuterDotTo_total D Sc m i j Λ h₁ h₂ β ε hβ]
    have hb := congrArg (fun f => f.total (M β))
      (probeOldBlockDistinctCross_slide_inner D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hβ)
    rw [Superfunctor.comp_total, distinct_total_smul, Superfunctor.comp_total] at hb
    exact distinct_conjugate_slide _ _ _ _ _ _ hb
  · exact (probeOldEFunctor_comp₂_isZero D Sc m i j Λ h₁ h₂ ε hε M).eq_of_src _ _

theorem probeOldActionDistinctCross_slide_outer (hij : i ≠ j) :
    probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄ ≫ (probeOldE D Sc m i Λ h₃ ◁ probeOldActionDot D Sc m j Λ h₄) =
      sign k (D.parity i * D.parity j) •
        ((probeOldActionDot D Sc m j Λ h₁ ▷ probeOldE D Sc m i Λ h₂) ≫ probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄) := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro M
  rw [Superfunctor.comp_total, distinct_total_smul, Superfunctor.comp_total]
  funext ε
  change (probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).total M ε ≫
      (probeOldE D Sc m i Λ h₃ ◁ probeOldActionDot D Sc m j Λ h₄).total M ε =
    sign k (D.parity i * D.parity j) •
      ((probeOldActionDot D Sc m j Λ h₁ ▷ probeOldE D Sc m i Λ h₂).total M ε ≫
        (probeOldActionDistinctCross D Sc m i j Λ h₁ h₂ h₃ h₄).total M ε)
  by_cases hε : ∃ β, blockSucc₂ D i j Λ h₁ h₂ β = ε
  · obtain ⟨β, hβ⟩ := hε
    rw [probeOldActionDistinctCross_total_of D Sc m i j Λ h₁ h₂ h₃ h₄ β ε hβ,
      probeOldPairOuterDotTo_total D Sc m j i Λ h₃ h₄ β ε (sw hβ),
      probeOldPairInnerDotTo_total D Sc m i j Λ h₁ h₂ β ε hβ]
    have hb := congrArg (fun f => f.total (M β))
      (probeOldBlockDistinctCross_slide_outer D Sc m i j Λ h₁ h₂ h₃ h₄ hij β ε hβ)
    rw [Superfunctor.comp_total, distinct_total_smul, Superfunctor.comp_total] at hb
    exact distinct_conjugate_slide _ _ _ _ _ _ hb
  · exact (probeOldEFunctor_comp₂_isZero D Sc m i j Λ h₁ h₂ ε hε M).eq_of_src _ _

end Crossing
end OddMath.QuiverHecke
end

end
