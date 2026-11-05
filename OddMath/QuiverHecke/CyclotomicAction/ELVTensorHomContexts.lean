import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumWords

/-! # Outer E contexts on surviving tensor-Hom entries

SwappedVacuumCoordinates §§2–6: apply the prescribed outer reservoir E
functors to the literal whiskered dot or crossing, then postcompose an
arbitrary whole Hom entry. The selected context charts give the extended
signed old-Hom arrow on every source vector. No faithfulness is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.TensorHomContexts
open CyclotomicAction SwappedAssembly
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (cutoff : I → ℕ) (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P₀" => WeightTensorVacuum.regularProbe D Sc m ΛP
local notation "W" => elvRouquierData D Sc cutoff N ΛR

private instance context_additive (x : X) (η : List I) :
    (PowerWordWeightContexts.contextFunctor D Sc cutoff L ΛR x η).Additive := by
  induction η generalizing x with
  | nil => change (𝟭 _).Additive; infer_instance
  | cons i η ih =>
    let := ih (x + D.α i)
    change (elvEFunctor D Sc cutoff N i ΛR rfl ⋙ _).Additive
    infer_instance

private instance context_linear (x : X) (η : List I) :
    (PowerWordWeightContexts.contextFunctor D Sc cutoff L ΛR x η).Linear k := by
  induction η generalizing x with
  | nil => change (𝟭 _).Linear k; infer_instance
  | cons i η ih =>
    let := ih (x + D.α i)
    change (elvEFunctor D Sc cutoff N i ΛR rfl ⋙ _).Linear k
    infer_instance

private instance context_super (x : X) (η : List I) :
    IsSuperfunctor k (PowerWordWeightContexts.contextFunctor D Sc cutoff L ΛR x η) := by
  induction η generalizing x with
  | nil => change IsSuperfunctor k (𝟭 _); infer_instance
  | cons i η ih =>
    let := ih (x + D.α i)
    change IsSuperfunctor k (elvEFunctor D Sc cutoff N i ΛR rfl ⋙ _)
    infer_instance

/-- The already defined context functor, bundled with its given super structure. -/
def context (x : X) (η : List I) : elvWeightSpace D Sc cutoff N ΛR x ⟶
    elvWeightSpace D Sc cutoff N ΛR (PowerWordWeightContexts.contextWeight D x η) :=
  ⟨PowerWordWeightContexts.contextFunctor D Sc cutoff L ΛR x η⟩

private theorem whiskerRight_total {A B C : PiSCat.{u,u,u+1} k}
    {F G : A ⟶ B} (a : F ⟶ G) (K : B ⟶ C) (p : A) :
    (a ▷ K).total p = K.map (a.total p) := by
  change K.map (a.app 0 p) + K.map (a.app 1 p) = K.map (a.app 0 p + a.app 1 p)
  exact (K.toFunctor.map_add).symm

private theorem mapped_square {A B : Type*} [Category* A] [Category* B]
    (F : A ⥤ B) {M N₀ S T : A} {U V : B}
    (e : M ≅ S) (f : N₀ ≅ T) (c : F.obj S ≅ U) (d : F.obj T ≅ V)
    (a : M ⟶ N₀) (b : S ⟶ T) (z : U ⟶ V)
    (ha : a ≫ f.hom = e.hom ≫ b) (hb : F.map b ≫ d.hom = c.hom ≫ z) :
    F.map a ≫ (F.mapIso f ≪≫ d).hom = (F.mapIso e ≪≫ c).hom ≫ z := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, ← F.map_comp, ha, F.map_comp, Category.assoc, hb]

/-- The same append chart followed by the existing outer context chart. -/
def dotChart (ν η : List I) (i : I) :
    (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ≫
      (W).E i (PowerWordWeight.wordWeight_append D ΛR ν i) ≫
      context D Sc cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η).obj P₀ ≅
    PowerWordWeight.wordFamily D Sc cutoff L ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)
      (PowerWordContexts.extendedWord (ν ++ [i]) η) :=
  PowerWordWeightContexts.contextChart D Sc cutoff L ΛR (ν ++ [i]) η _ rfl
    (TensorVacuumWords.dotChart D Sc m cutoff L ΛP ΛR ν i)

omit [Fintype I] in
private theorem pair_weight (ν : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu) :
    xu = PowerWordWeight.wordWeight D ΛR ((ν ++ [j]) ++ [i]) :=
  h₂.symm.trans ((congrArg (fun x => x + D.α i)
    (h₁.symm.trans (PowerWordWeight.wordWeight_append D ΛR ν j))).trans
      (PowerWordWeight.wordWeight_append D ΛR (ν ++ [j]) i))

/-- The same pair chart followed by the existing outer context chart. -/
def pairChart (ν η : List I) (i j : I) {xj xu : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu) :
    (TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ≫ (W).E j h₁ ≫ (W).E i h₂ ≫
      context D Sc cutoff L ΛR xu η).obj P₀ ≅
    PowerWordWeight.wordFamily D Sc cutoff L ΛR (PowerWordWeightContexts.contextWeight D xu η)
      (PowerWordContexts.extendedWord ((ν ++ [j]) ++ [i]) η) :=
  PowerWordWeightContexts.contextChart D Sc cutoff L ΛR ((ν ++ [j]) ++ [i]) η xu
    (pair_weight D ΛR ν i j h₁ h₂) (TensorVacuumWords.pairChart D Sc m cutoff L ΛP ΛR ν i j h₁ h₂)

/-- The literal whiskered dot under an arbitrary outer E-word context. -/
theorem dot (ν η : List I) (i : I) :
    ((TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ◁
      (W).dot i (PowerWordWeight.wordWeight_append D ΛR ν i)) ▷
      context D Sc cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η).total P₀ ≫
      (dotChart D Sc m cutoff L ΛP ΛR ν η i).hom =
    (dotChart D Sc m cutoff L ΛP ΛR ν η i).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR
        (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)
        (PowerWordContexts.extendedWord (ν ++ [i]) η) (PowerWordContexts.extendedWord (ν ++ [i]) η)
        (PowerWordContexts.extendedArrow D Sc cutoff (ν ++ [i]) (ν ++ [i]) η
          (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν))) := by
  rw [whiskerRight_total]
  exact mapped_square _ _ _ _ _ _ _ _
    (TensorVacuumWords.dot D Sc m cutoff L ΛP ΛR ν i)
    (PowerWordWeightContexts.context_family_arrow D Sc cutoff L ΛR (ν ++ [i]) (ν ++ [i]) η _
      rfl rfl rfl (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν)))

/-- The literal crossing under an arbitrary outer E-word context, retaining
the old extended arrow and every actual intermediate original weight. -/
theorem cross (ν η : List I) (i j : I) {xj xu xi : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : PowerWordWeight.wordWeight D ΛR ν + D.α i = xi) (h₄ : xi + D.α j = xu) :
    ((TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ◁ (W).cross i j h₁ h₂ h₃ h₄) ▷
      context D Sc cutoff L ΛR xu η).total P₀ ≫ (pairChart D Sc m cutoff L ΛP ΛR ν η j i h₃ h₄).hom =
    (pairChart D Sc m cutoff L ΛP ΛR ν η i j h₁ h₂).hom ≫
      PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR (PowerWordWeightContexts.contextWeight D xu η)
        (PowerWordContexts.extendedWord ((ν ++ [j]) ++ [i]) η)
        (PowerWordContexts.extendedWord ((ν ++ [i]) ++ [j]) η)
        (PowerWordContexts.extendedArrow D Sc cutoff ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j]) η
          (PowerWordContentCross.normalizedOldCross D Sc cutoff ν i j)) := by
  rw [whiskerRight_total]
  have hst : (((ν ++ [j]) ++ [i] : List I) : Multiset I) = (((ν ++ [i]) ++ [j] : List I) : Multiset I) := by
    rw [← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add]
    ac_rfl
  exact mapped_square _ _ _ _ _ _ _ _
    (TensorVacuumWords.cross D Sc m cutoff L ΛP ΛR ν i j h₁ h₂ h₃ h₄)
    (PowerWordWeightContexts.context_family_arrow D Sc cutoff L ΛR ((ν ++ [j]) ++ [i])
      ((ν ++ [i]) ++ [j]) η xu (pair_weight D ΛR ν i j h₁ h₂) (pair_weight D ΛR ν j i h₃ h₄) hst
      (PowerWordContentCross.normalizedOldCross D Sc cutoff ν i j))

private theorem entry_comp {x : X}
    {G Y Z : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR x}
    (f : G ⟶ Y) (g : Y ⟶ Z) (β : WeightBlocks D ΛR x)
    (c : ContentCategory D Sc cutoff N β.1) (z : ((G.obj P₀) β).obj c) :
    (((f ≫ g).total P₀) β).total c z =
      ((g.total P₀) β).total c (((f.total P₀) β).total c z) := by
  rw [Superfunctor.comp_total]
  change (((f.total P₀) β ≫ (g.total P₀) β).total c) z = _
  rw [Superfunctor.comp_total, SVec.comp_apply]

private theorem square_apply {x : X}
    {A B C E : ELVWeightProduct D Sc cutoff N ΛR x}
    (a : A ⟶ B) (e : A ⟶ C) (f : B ⟶ E) (b : C ⟶ E)
    (h : a ≫ f = e ≫ b) (β : WeightBlocks D ΛR x)
    (c : ContentCategory D Sc cutoff N β.1) (z : (A β).obj c) :
    (f β).total c ((a β).total c z) = (b β).total c ((e β).total c z) := by
  have hs := congrArg (fun g => (g β).total c) h
  change (a β ≫ f β).total c = (e β ≫ b β).total c at hs
  rw [Superfunctor.comp_total, Superfunctor.comp_total] at hs
  exact congrArg (fun g => g z) hs

/-- The outer-context dot entry square for arbitrary whole Hom entries
and every source vector. -/
theorem dot_apply (ν η : List I) (i : I)
    (G : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (f : G ⟶ TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ≫
      (W).E i (PowerWordWeight.wordWeight_append D ΛR ν i) ≫
      context D Sc cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)
    (β : WeightBlocks D ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η))
    (c : ContentCategory D Sc cutoff N β.1) (z : ((G.obj P₀) β).obj c) :
    (((dotChart D Sc m cutoff L ΛP ΛR ν η i).hom β).total c)
      ((((f ≫ ((TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ◁
        (W).dot i (PowerWordWeight.wordWeight_append D ΛR ν i)) ▷
        context D Sc cutoff L ΛR (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)).total P₀) β).total c z) =
    (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR
      (PowerWordWeightContexts.contextWeight D (PowerWordWeight.wordWeight D ΛR (ν ++ [i])) η)
      (PowerWordContexts.extendedWord (ν ++ [i]) η) (PowerWordContexts.extendedWord (ν ++ [i]) η)
      (PowerWordContexts.extendedArrow D Sc cutoff (ν ++ [i]) (ν ++ [i]) η
        (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cutoff i (OldCategory.mk ν))) β).total c
      (((dotChart D Sc m cutoff L ΛP ΛR ν η i).hom β).total c (((f.total P₀) β).total c z)) := by
  rw [entry_comp]
  exact square_apply D Sc cutoff L ΛR _ _ _ _
    (dot D Sc m cutoff L ΛP ΛR ν η i) β c (((f.total P₀) β).total c z)

/-- The outer-context crossing entry square, for arbitrary whole input
transformations and every vector, without a faithfulness premise. -/
theorem cross_apply (ν η : List I) (i j : I) {xj xu xi : X}
    (h₁ : PowerWordWeight.wordWeight D ΛR ν + D.α j = xj) (h₂ : xj + D.α i = xu)
    (h₃ : PowerWordWeight.wordWeight D ΛR ν + D.α i = xi) (h₄ : xi + D.α j = xu)
    (G : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶ elvWeightSpace D Sc cutoff N ΛR
      (PowerWordWeightContexts.contextWeight D xu η))
    (f : G ⟶ TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ≫
      (W).E j h₁ ≫ (W).E i h₂ ≫ context D Sc cutoff L ΛR xu η)
    (β : WeightBlocks D ΛR (PowerWordWeightContexts.contextWeight D xu η))
    (c : ContentCategory D Sc cutoff N β.1) (z : ((G.obj P₀) β).obj c) :
    (((pairChart D Sc m cutoff L ΛP ΛR ν η j i h₃ h₄).hom β).total c)
      ((((f ≫ ((TensorVacuumWords.wordHom D Sc m cutoff L ΛP ΛR ν ◁
        (W).cross i j h₁ h₂ h₃ h₄) ▷ context D Sc cutoff L ΛR xu η)).total P₀) β).total c z) =
    (PowerWordWeightWhiskering.wordFamilyArrow D Sc cutoff L ΛR (PowerWordWeightContexts.contextWeight D xu η)
      (PowerWordContexts.extendedWord ((ν ++ [j]) ++ [i]) η) (PowerWordContexts.extendedWord ((ν ++ [i]) ++ [j]) η)
      (PowerWordContexts.extendedArrow D Sc cutoff ((ν ++ [j]) ++ [i]) ((ν ++ [i]) ++ [j]) η
        (PowerWordContentCross.normalizedOldCross D Sc cutoff ν i j)) β).total c
      (((pairChart D Sc m cutoff L ΛP ΛR ν η i j h₁ h₂).hom β).total c (((f.total P₀) β).total c z)) := by
  rw [entry_comp]
  exact square_apply D Sc cutoff L ΛR _ _ _ _
    (cross D Sc m cutoff L ΛP ΛR ν η i j h₁ h₂ h₃ h₄) β c (((f.total P₀) β).total c z)

end OddMath.QuiverHecke.ELVOld.TensorHomContexts
