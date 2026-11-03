import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCrossingComparison

/-! # Triple induction at the actual original-weight successor blocks

Brundan--Ellis (1.9), DeformedActionAssembly §6. The actual three weight
inductions are compared with the canonical content triple without changing
any intermediate block convention. Absent triple predecessors have zero
source. These are the coordinates for the prescribed weight braid.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke.ELVOld
universe u
private theorem tripleComparison_eq_mem
    {k : Type u} [CommRing k] {C B : Type*} [Category* C] [Category* B]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G : C ⥤ B} (e : F = G) (M : C) :
    EvenComparisonAt (k := k) (eqToIso e) M := by
  cases e
  exact ⟨id_mem _, id_mem _⟩

private theorem tripleComparison_trans_mem
    {k : Type u} [CommRing k] {C B : Type*} [Category* C] [Category* B]
    [Preadditive B] [Linear k B] [Supercategory k B]
    {F G H : C ⥤ B} (e : F ≅ G) (f : G ≅ H) (M : C)
    (he : EvenComparisonAt (k := k) e M) (hf : EvenComparisonAt (k := k) f M) :
    EvenComparisonAt (k := k) (e ≪≫ f) M :=
  ⟨comp_mem he.1 hf.1, comp_mem hf.2 he.2⟩

private theorem tripleEvaluationComparison_mem
    {k : Type u} [CommRing k] {C B E : Type*} [Category* C] [Category* B] [Category* E]
    [Preadditive E] [Linear k E] [Supercategory k E]
    (R : C ⥤ B) {F : C ⥤ E} {G H : B ⥤ E} (h : F = R ⋙ G) (e : G ≅ H)
    (he : ∀ N, EvenComparisonAt (k := k) e N) (M : C) :
    EvenComparisonAt (k := k) (eqToIso h ≪≫ Functor.isoWhiskerLeft R e) M :=
  tripleComparison_trans_mem _ _ M (tripleComparison_eq_mem h M) (he (R.obj M))

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (bound : ℕ)

/-- Recast both actual intermediate contents inside the whole composite. -/
theorem contentTripleInductionTo_eq (β : Multiset I) (a b c : I) (δ₁ δ₂ γ : Multiset I)
    (h₁ : β + ([a] : Multiset I) = δ₁)
    (h₂ : δ₁ + ([b] : Multiset I) = δ₂)
    (h₃ : δ₂ + ([c] : Multiset I) = γ)
    (h : β + ([a,b,c] : Multiset I) = γ) :
    (contentInductionTo D Sc cutoff bound β [a] δ₁ h₁ ⋙
      contentInductionTo D Sc cutoff bound δ₁ [b] δ₂ h₂) ⋙
        contentInductionTo D Sc cutoff bound δ₂ [c] γ h₃ =
      contentETripleTo D Sc cutoff bound β a b c γ h := by
  subst δ₁
  subst δ₂
  rfl

variable (i j l : I) (Λ : X) {x₀ x₁ x₂ x₃ : X}
  (h₁ : x₀ + D.α l = x₁) (h₂ : x₁ + D.α j = x₂) (h₃ : x₂ + D.α i = x₃)

/-- The actual block reached by the three indicated successive inductions. -/
abbrev elvBlockSucc₃ (β : WeightBlocks D Λ x₀) : WeightBlocks D Λ x₃ :=
  blockSucc D Λ i h₃ (blockSucc₂ D j l Λ h₁ h₂ β)

theorem elvBlockSucc₃_injective : Function.Injective (elvBlockSucc₃ D i j l Λ h₁ h₂ h₃) :=
  fun _ _ h => blockSucc₂_injective D j l Λ h₁ h₂ (blockSucc_injective D Λ i h₃ h)

/-- All three selected block inductions, retaining both true intermediate blocks. -/
abbrev elvBlockTripleInd (β : WeightBlocks D Λ x₀) :=
  (elvBlockPairInd D Sc cutoff bound j l Λ h₁ h₂ β).comp
    (elvBlockInd D Sc cutoff bound i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β))

theorem elvBlockTriple_content_eq (β : WeightBlocks D Λ x₀) :
    β.1 + ([l,j,i] : Multiset I) = (elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β).1 := by
  change β.1 + (([l] : Multiset I) + (([j] : Multiset I) + ([i] : Multiset I))) =
    ([i] : Multiset I) + (([j] : Multiset I) + (([l] : Multiset I) + β.1))
  ac_rfl

/-- The actual three block functors have the canonical triple endpoint presentation. -/
theorem elvBlockTripleInd_content_eq (β : WeightBlocks D Λ x₀) :
    (elvBlockTripleInd D Sc cutoff bound i j l Λ h₁ h₂ h₃ β).toFunctor =
      contentETripleTo D Sc cutoff bound β.1 l j i
        (elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β).1
        (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β) :=
  contentTripleInductionTo_eq D Sc cutoff bound β.1 l j i _ _ _
    (elvBlockSucc_content_eq D l Λ h₁ β)
    (elvBlockSucc_content_eq D j Λ h₂ (blockSucc D Λ l h₁ β))
    (elvBlockSucc_content_eq D i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β))
    (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β)

/-- Triple product induction at a true triple successor equals the actual block triple. -/
theorem elvEFunctor_comp₃_blockSucc (β : WeightBlocks D Λ x₀) :
    (elvEFunctor D Sc cutoff bound l Λ h₁ ⋙ elvEFunctor D Sc cutoff bound j Λ h₂) ⋙
      (elvInductionComponent D Sc cutoff bound i Λ h₃
        (elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β)).toFunctor =
    (elvBlockEval D Sc cutoff bound Λ β).toFunctor ⋙
      (elvBlockTripleInd D Sc cutoff bound i j l Λ h₁ h₂ h₃ β).toFunctor := by
  rw [elvInductionComponent_blockSucc]
  change (elvEFunctor D Sc cutoff bound l Λ h₁ ⋙
      (elvEFunctor D Sc cutoff bound j Λ h₂ ⋙
        (elvBlockEval D Sc cutoff bound Λ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor)) ⋙
      (elvBlockInd D Sc cutoff bound i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor = _
  change (elvEFunctor D Sc cutoff bound l Λ h₁ ⋙
      (elvInductionComponent D Sc cutoff bound j Λ h₂ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor) ⋙
      (elvBlockInd D Sc cutoff bound i Λ h₃ (blockSucc₂ D j l Λ h₁ h₂ β)).toFunctor = _
  rw [elvEFunctor_comp₂_blockSucc]
  rfl

/-- The actual triple successor has the stated literal word content. -/
theorem elvWeightTriple_content_eq (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε) :
    β.1 + ([l,j,i] : Multiset I) = ε.1 :=
  (elvBlockTriple_content_eq D i j l Λ h₁ h₂ h₃ β).trans (congrArg Subtype.val hε)

/-- The entire supported weight coordinate is the canonical content triple. -/
theorem elvEFunctor_comp₃_contentTriple_eq (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε) :
    (elvEFunctor D Sc cutoff bound l Λ h₁ ⋙ elvEFunctor D Sc cutoff bound j Λ h₂) ⋙
      (elvInductionComponent D Sc cutoff bound i Λ h₃ ε).toFunctor =
    (elvBlockEval D Sc cutoff bound Λ β).toFunctor ⋙
      contentETripleTo D Sc cutoff bound β.1 l j i ε.1
        (elvWeightTriple_content_eq D i j l Λ h₁ h₂ h₃ β ε hε) := by
  subst ε
  exact (elvEFunctor_comp₃_blockSucc D Sc cutoff bound i j l Λ h₁ h₂ h₃ β).trans
    (congrArg (fun F => (elvBlockEval D Sc cutoff bound Λ β).toFunctor ⋙ F)
      (elvBlockTripleInd_content_eq D Sc cutoff bound i j l Λ h₁ h₂ h₃ β))

/-- The actual three E coordinates flatten by the canonical content comparison. -/
def elvWeightTripleComparison (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε) :
    ((elvEFunctor D Sc cutoff bound l Λ h₁ ⋙ elvEFunctor D Sc cutoff bound j Λ h₂) ⋙
      (elvInductionComponent D Sc cutoff bound i Λ h₃ ε).toFunctor) ≅
    ((elvBlockEval D Sc cutoff bound Λ β).toFunctor ⋙
      contentInductionTo D Sc cutoff bound β.1 [l,j,i] ε.1
        (elvWeightTriple_content_eq D i j l Λ h₁ h₂ h₃ β ε hε)) :=
  eqToIso (elvEFunctor_comp₃_contentTriple_eq D Sc cutoff bound i j l Λ h₁ h₂ h₃ β ε hε) ≪≫
    Functor.isoWhiskerLeft (elvBlockEval D Sc cutoff bound Λ β).toFunctor
      (contentETripleComparison D Sc cutoff bound β.1 l j i ε.1
        (elvWeightTriple_content_eq D i j l Λ h₁ h₂ h₃ β ε hε))

/-- Both directions of the selected weight triple comparison are even. -/
theorem elvWeightTripleComparison_mem (β : WeightBlocks D Λ x₀)
    (ε : WeightBlocks D Λ x₃) (hε : elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    EvenComparisonAt (k := k)
      (elvWeightTripleComparison D Sc cutoff bound i j l Λ h₁ h₂ h₃ β ε hε) M :=
  tripleEvaluationComparison_mem (elvBlockEval D Sc cutoff bound Λ β).toFunctor
    (elvEFunctor_comp₃_contentTriple_eq D Sc cutoff bound i j l Λ h₁ h₂ h₃ β ε hε)
    (contentETripleComparison D Sc cutoff bound β.1 l j i ε.1
      (elvWeightTriple_content_eq D i j l Λ h₁ h₂ h₃ β ε hε))
    (contentETripleComparison_mem D Sc cutoff bound β.1 l j i ε.1
      (elvWeightTriple_content_eq D i j l Λ h₁ h₂ h₃ β ε hε)) M

/-- No triple predecessor means the actual source coordinate is zero. -/
theorem elvEFunctor_comp₃_isZero (ε : WeightBlocks D Λ x₃)
    (hε : ¬ ∃ β, elvBlockSucc₃ D i j l Λ h₁ h₂ h₃ β = ε)
    (M : ELVWeightProduct D Sc cutoff bound Λ x₀) :
    Limits.IsZero (((elvEFunctor D Sc cutoff bound l Λ h₁ ⋙
      elvEFunctor D Sc cutoff bound j Λ h₂) ⋙
        (elvInductionComponent D Sc cutoff bound i Λ h₃ ε).toFunctor).obj M) := by
  by_cases hγ : ∃ γ, blockSucc D Λ i h₃ γ = ε
  · obtain ⟨γ, rfl⟩ := hγ
    have hz : Limits.IsZero (((elvEFunctor D Sc cutoff bound l Λ h₁) ⋙
        (elvInductionComponent D Sc cutoff bound j Λ h₂ γ).toFunctor).obj M) :=
      elvEFunctor_comp₂_isZero D Sc cutoff bound j l Λ h₁ h₂ γ
        (fun ⟨β, hβ⟩ => hε ⟨β, by rw [elvBlockSucc₃, hβ]⟩) M
    exact Limits.IsZero.of_iso
      ((elvBlockInd D Sc cutoff bound i Λ h₃ γ).toFunctor.map_isZero hz)
      (eqToIso (elvInductionComponent_obj_blockSucc D Sc cutoff bound i Λ h₃ γ _))
  · exact elvInductionComponent_isZero D Sc cutoff bound i Λ h₃ ε hγ _

end OddMath.QuiverHecke.ELVOld
