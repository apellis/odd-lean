import OddMath.QuiverHecke.CyclotomicAction.PowerWordWhiskering.PowerWordAppendUnits
import OddMath.QuiverHecke.CyclotomicAction.WeightPair.WeightRectangularCross

/-!
# Power word whiskering

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Chosen weight crossings in regular-power word coordinates

SwappedVacuumCoordinates §§4–6: transport the given weight crossing through
the selected content pair comparisons, with both colour cases included.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerWordWeightCross
open CyclotomicAction
universe u
private theorem crossing_paste {C : Type*} [Category* C] {A B E F S T : C}
    (a : A ≅ B) (b : E ≅ F) (s : B ≅ S) (t : F ≅ T)
    (c : B ⟶ F) (w : S ⟶ T) (h : c ≫ t.hom = s.hom ≫ w) :
    ((a.hom ≫ c) ≫ b.inv) ≫ (b ≪≫ t).hom = (a ≪≫ s).hom ≫ w := by
  simp only [Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The existing whole append comparison at equal presentations of its weights. -/
def appendIsoAtWeights (Λ : X) (ν : List I) (i : I) (x y : X)
    (hx : x = PowerWordWeight.wordWeight D Λ ν)
    (hy : y = PowerWordWeight.wordWeight D Λ (ν ++ [i])) (h : x + D.α i = y) :
    (elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h).obj
      (PowerWordWeight.wordFamily D Sc cutoff L Λ x ν) ≅
        PowerWordWeight.wordFamily D Sc cutoff L Λ y (ν ++ [i]) := by
  cases hx
  cases hy
  exact PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i

omit [Fintype I] in
private theorem next_weight (Λ : X) (ν : List I) (i : I) {x y : X}
    (hx : x = PowerWordWeight.wordWeight D Λ ν) (h : x + D.α i = y) :
    y = PowerWordWeight.wordWeight D Λ (ν ++ [i]) :=
  h.symm.trans ((congrArg (fun z => z + D.α i) hx).trans
    (PowerWordWeight.wordWeight_append D Λ ν i))

section Supported
variable (ν : List I) (i j : I) (Λ : X) {x₀ xj xu xi : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (β : WeightBlocks D Λ x₀) (ε : WeightBlocks D Λ xu)
  (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) (hν : (ν : Multiset I) = β.1)

/-- The given supported weight-pair chart followed by the recursively selected
single-append word charts, through the actual first successor block. -/
def pairComponentIso :
    ((elvEFunctor D Sc cutoff (PowerWordContent.powerBound D cutoff L) j Λ h₁ ⋙
      (elvInductionComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h₂ ε).toFunctor).obj
        (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν)) ≅
      PowerWordWeight.wordAt D Sc cutoff L ((ν ++ [j]) ++ [i]) ε.1 :=
  (eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    i j Λ h₁ h₂ β ε hε)).app (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν) ≪≫
      PowerWordContentCross.pairIsoTo D Sc cutoff L ν i j β.1
        (blockSucc D Λ j h₁ β).1 ε.1 hν
        (elvBlockSucc_content_eq D j Λ h₁ β)
        (elvWeightPairUpper_content_eq D i j Λ h₁ h₂ β ε hε)

variable (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
/-- The given weight crossing on its occupied pair component is the full signed
old-Hom word crossing. No comparison of operators is assumed. -/
theorem weight_cross_component :
    elvWeightCrossComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      i j Λ h₁ h₂ h₃ h₄ (D.parity i * D.parity j)
      (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν) ε ≫
        (pairComponentIso D Sc cutoff L ν j i Λ h₃ h₄ β ε
          (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε) hν).hom =
    (pairComponentIso D Sc cutoff L ν i j Λ h₁ h₂ β ε hε hν).hom ≫
      PowerWordContentCross.wordCross D Sc cutoff L ε.1 ν i j := by
  rw [elvWeightCrossComponent_of D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    i j Λ h₁ h₂ h₃ h₄ (D.parity i * D.parity j)
    (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν) β ε hε]
  rw [elvWeightCrossVia_normalized_rectangular D Sc cutoff (PowerWordContent.powerBound D cutoff L)
    i j Λ h₁ h₂ β ε hε h₃ h₄]
  have hc := PowerWordContentCross.selected_pair_cross D Sc cutoff L ν β.1 hν i j
    (blockSucc D Λ j h₁ β).1 (blockSucc D Λ i h₃ β).1 ε.1
    (elvBlockSucc_content_eq D j Λ h₁ β) (elvBlockSucc_content_eq D i Λ h₃ β)
    (elvWeightPairUpper_content_eq D i j Λ h₁ h₂ β ε hε)
    (elvWeightPairUpper_content_eq D j i Λ h₃ h₄ β ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))
  exact crossing_paste
    ((eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      i j Λ h₁ h₂ β ε hε)).app (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν))
    ((eqToIso (elvEFunctor_comp₂_rectangular_eq D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      j i Λ h₃ h₄ β ε (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))).app
        (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν))
    (PowerWordContentCross.pairIsoTo D Sc cutoff L ν i j β.1
      (blockSucc D Λ j h₁ β).1 ε.1 hν
      (elvBlockSucc_content_eq D j Λ h₁ β)
      (elvWeightPairUpper_content_eq D i j Λ h₁ h₂ β ε hε))
    (PowerWordContentCross.pairIsoTo D Sc cutoff L ν j i β.1
      (blockSucc D Λ i h₃ β).1 ε.1 hν
      (elvBlockSucc_content_eq D i Λ h₃ β)
      (elvWeightPairUpper_content_eq D j i Λ h₃ h₄ β ε
        (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε))) _ _ hc
end Supported

/-- The recursive whole-family append comparison, used also to retain all
zero content components of a pair. -/
def recursivePairIso (Λ : X) (ν : List I) (i j : I) {x₀ xj xu : X}
    (hx : x₀ = PowerWordWeight.wordWeight D Λ ν)
    (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu) :
    (elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h₂).obj
      ((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) j Λ h₁).obj
        (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν)) ≅
    PowerWordWeight.wordFamily D Sc cutoff L Λ xu ((ν ++ [j]) ++ [i]) :=
  (elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h₂).toFunctor.mapIso
    (appendIsoAtWeights D Sc cutoff L Λ ν j x₀ xj hx (next_weight D Λ ν j hx h₁) h₁) ≪≫
      appendIsoAtWeights D Sc cutoff L Λ (ν ++ [j]) i xj xu
        (next_weight D Λ ν j hx h₁)
        (next_weight D Λ (ν ++ [j]) i (next_weight D Λ ν j hx h₁) h₂) h₂

section Family
variable (Λ : X) (ν : List I) (i j : I) {x₀ xj xu : X}
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (β : WeightBlocks D Λ x₀) (hν : (ν : Multiset I) = β.1)
omit [Fintype I] in
private theorem initial_weight (β₀ : WeightBlocks D Λ x₀) (h₀ : (ν : Multiset I) = β₀.1) :
    x₀ = PowerWordWeight.wordWeight D Λ ν := by
  exact (congrArg (blockWeight D Λ) h₀).trans β₀.property |>.symm

/-- The selected chart at the occupied output; on other components it uses
the recursive whole-family append charts. -/
def pairFamilyIso :
    (elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h₂).obj
      ((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) j Λ h₁).obj
        (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν)) ≅
    PowerWordWeight.wordFamily D Sc cutoff L Λ xu ((ν ++ [j]) ++ [i]) := by
  classical
  apply Pi.isoMk
  intro ε
  by_cases hε : blockSucc₂ D i j Λ h₁ h₂ β = ε
  · exact pairComponentIso D Sc cutoff L ν i j Λ h₁ h₂ β ε hε hν
  · exact Pi.isoApp (recursivePairIso D Sc cutoff L Λ ν i j
      (initial_weight D Λ ν β hν) h₁ h₂) ε

include hν in
/-- Every nonoccupied component of the given double-E source is zero. -/
theorem pair_source_isZero (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β ≠ ε) :
    Limits.IsZero (((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h₂).obj
      ((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) j Λ h₁).obj
        (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν))) ε) := by
  have hc : ε.1 ≠ (((ν ++ [j]) ++ [i] : List I) : Multiset I) := by
    intro he
    apply hε
    apply Subtype.ext
    change ({i} : Multiset I) + ({j} + β.1) = ε.1
    rw [he, ← hν, ← Multiset.coe_add, ← Multiset.coe_add]
    ac_rfl
  exact (PowerWordWeight.wordAt_isZero D Sc cutoff L ((ν ++ [j]) ++ [i]) ε.1 hc).of_iso
    (Pi.isoApp (recursivePairIso D Sc cutoff L Λ ν i j
      (initial_weight D Λ ν β hν) h₁ h₂) ε)
/-- The chart at every occupied pair block is the given supported chart. -/
theorem pairFamilyIso_hom_of (ε : WeightBlocks D Λ xu)
    (hε : blockSucc₂ D i j Λ h₁ h₂ β = ε) :
    (pairFamilyIso D Sc cutoff L Λ ν i j h₁ h₂ β hν).hom ε =
      (pairComponentIso D Sc cutoff L ν i j Λ h₁ h₂ β ε hε hν).hom := by
  unfold pairFamilyIso
  simp only [Pi.isoMk_hom, dite_eq_left hε]

variable {xi : X} (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
/-- The signed old-Hom crossing on every component of the same word family. -/
def wordFamilyCross :
    PowerWordWeight.wordFamily D Sc cutoff L Λ xu ((ν ++ [j]) ++ [i]) ⟶
      PowerWordWeight.wordFamily D Sc cutoff L Λ xu ((ν ++ [i]) ++ [j]) :=
  fun ε => PowerWordContentCross.wordCross D Sc cutoff L ε.1 ν i j

/-- The chosen weight crossing agrees with the signed old-Hom operator on
all content components, including absent and off-support predecessors. -/
theorem weight_pair_cross :
    (elvActionCross D Sc cutoff (PowerWordContent.powerBound D cutoff L) i j Λ h₁ h₂ h₃ h₄).app
      (D.parity i * D.parity j) (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν) ≫
        (pairFamilyIso D Sc cutoff L Λ ν j i h₃ h₄ β hν).hom =
    (pairFamilyIso D Sc cutoff L Λ ν i j h₁ h₂ β hν).hom ≫
      wordFamilyCross D Sc cutoff L Λ ν i j (xu := xu) := by
  funext ε
  change elvWeightCrossComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L) i j Λ
    h₁ h₂ h₃ h₄ (D.parity i * D.parity j) (PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν) ε ≫
      (pairFamilyIso D Sc cutoff L Λ ν j i h₃ h₄ β hν).hom ε =
    (pairFamilyIso D Sc cutoff L Λ ν i j h₁ h₂ β hν).hom ε ≫
      PowerWordContentCross.wordCross D Sc cutoff L ε.1 ν i j
  classical
  by_cases hε : blockSucc₂ D i j Λ h₁ h₂ β = ε
  · rw [pairFamilyIso_hom_of D Sc cutoff L Λ ν j i h₃ h₄ β hν ε
      (blockSucc₂_swap D i j Λ h₁ h₂ h₃ h₄ hε),
      pairFamilyIso_hom_of D Sc cutoff L Λ ν i j h₁ h₂ β hν ε hε]
    exact weight_cross_component D Sc cutoff L ν i j Λ h₁ h₂ β ε hε hν h₃ h₄
  · exact (pair_source_isZero D Sc cutoff L Λ ν i j h₁ h₂ β hν ε hε).eq_of_src _ _
end Family

end OddMath.QuiverHecke.ELV.PowerWordWeightCross
end

end

section

/-! # Arbitrary-arrow append transport on the weight word family

SwappedVacuumCoordinates §§4–6: preserve the existing whole append chart
while transporting arbitrary full old-Hom maps through the chosen E functor.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerWordWeightWhiskering
open CyclotomicAction CyclotomicCrossingTensor
universe u
private theorem square_paste {C : Type*} [Category* C] {A B E F S T : C}
    (ha : A = B) (hb : E = F) (s : B ≅ S) (t : F ≅ T)
    (c : B ⟶ F) (w : S ⟶ T) (h : c ≫ t.hom = s.hom ≫ w) :
    (eqToHom ha ≫ c ≫ eqToHom hb.symm) ≫ (eqToHom hb ≫ t.hom) =
      (eqToHom ha ≫ s.hom) ≫ w := by
  cases ha
  cases hb
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using h

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

/-- The existing whole append chart at its given supported block. -/
theorem append_component (Λ : X) (ν : List I) (i : I) (x y : X)
    (hx : x = PowerWordWeight.wordWeight D Λ ν)
    (hy : y = PowerWordWeight.wordWeight D Λ (ν ++ [i])) (h : x + D.α i = y)
    (β : WeightBlocks D Λ x) (hν : (ν : Multiset I) = β.1) :
    (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν i x y hx hy h).hom
      (blockSucc D Λ i h β) =
    eqToHom (elvInductionComponent_obj_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L)
      i Λ h β (PowerWordWeight.wordFamily D Sc cutoff L Λ x ν)) ≫
      (PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β.1 (blockSucc D Λ i h β).1 hν
        (elvBlockSucc_content_eq D i Λ h β)).hom := by
  cases hx
  cases hy
  have hβ : β = PowerWordWeight.wordBlock D Λ ν := Subtype.ext hν.symm
  subst β
  change (PowerWordWeight.weightAppendAtIso D Sc cutoff L Λ ν i
    (blockSucc D Λ i h (PowerWordWeight.wordBlock D Λ ν))).hom = _
  unfold PowerWordWeight.weightAppendAtIso
  simp only
  rfl

/-- The full signed old-Hom map on every unchanged content component. -/
def wordFamilyArrow (Λ x : X) (s t : List I)
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    PowerWordWeight.wordFamily D Sc cutoff L Λ x s ⟶ PowerWordWeight.wordFamily D Sc cutoff L Λ x t :=
  fun β => PowerWordContentCross.contentWordArrow D Sc cutoff L β.1 s t g

/-- The single-E source vanishes outside the content of the appended word. -/
theorem append_source_isZero (Λ : X) (ν : List I) (i : I) (x y : X)
    (hx : x = PowerWordWeight.wordWeight D Λ ν)
    (hy : y = PowerWordWeight.wordWeight D Λ (ν ++ [i])) (h : x + D.α i = y)
    (δ : WeightBlocks D Λ y) (hδ : δ.1 ≠ (((ν ++ [i]) : List I) : Multiset I)) :
    Limits.IsZero (((elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h).obj
      (PowerWordWeight.wordFamily D Sc cutoff L Λ x ν)) δ) :=
  (PowerWordWeight.wordAt_isZero D Sc cutoff L (ν ++ [i]) δ.1 hδ).of_iso
    (Pi.isoApp (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν i x y hx hy h) δ)

/-- The given E functor intertwines arbitrary full old-Hom maps through the
existing whole single-append charts, on every content component. -/
theorem append_family_arrow (Λ : X) (s t : List I) (i : I) (x y : X)
    (hxs : x = PowerWordWeight.wordWeight D Λ s)
    (hys : y = PowerWordWeight.wordWeight D Λ (s ++ [i]))
    (hxt : x = PowerWordWeight.wordWeight D Λ t)
    (hyt : y = PowerWordWeight.wordWeight D Λ (t ++ [i]))
    (h : x + D.α i = y) (hst : (s : Multiset I) = (t : Multiset I))
    (g : (OldCategory.mk t : OldCategory D Sc cutoff) ⟶ OldCategory.mk s) :
    (elvE D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h).map
      (wordFamilyArrow D Sc cutoff L Λ x s t g) ≫
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ t i x y hxt hyt h).hom =
    (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ s i x y hxs hys h).hom ≫
      wordFamilyArrow D Sc cutoff L Λ y (s ++ [i]) (t ++ [i]) ((append D Sc cutoff i).map g) := by
  funext δ
  let β : WeightBlocks D Λ x := ⟨s, hxs.symm⟩
  classical
  by_cases he : δ = blockSucc D Λ i h β
  · subst δ
    change (elvInductionComponent D Sc cutoff (PowerWordContent.powerBound D cutoff L) i Λ h
      (blockSucc D Λ i h β)).map (wordFamilyArrow D Sc cutoff L Λ x s t g) ≫
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ t i x y hxt hyt h).hom
          (blockSucc D Λ i h β) =
      (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ s i x y hxs hys h).hom
          (blockSucc D Λ i h β) ≫
        PowerWordContentCross.contentWordArrow D Sc cutoff L (blockSucc D Λ i h β).1
          (s ++ [i]) (t ++ [i]) ((append D Sc cutoff i).map g)
    rw [append_component D Sc cutoff L Λ t i x y hxt hyt h β hst.symm,
      append_component D Sc cutoff L Λ s i x y hxs hys h β rfl,
      elvInductionComponent_map_blockSucc]
    have hc := PowerWordContentWhiskering.append_word_arrow D Sc cutoff L s t i β.1
      (blockSucc D Λ i h β).1 rfl hst.symm (elvBlockSucc_content_eq D i Λ h β) g
    have hp := square_paste
      (elvInductionComponent_obj_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        i Λ h β (PowerWordWeight.wordFamily D Sc cutoff L Λ x s))
      (elvInductionComponent_obj_blockSucc D Sc cutoff (PowerWordContent.powerBound D cutoff L)
        i Λ h β (PowerWordWeight.wordFamily D Sc cutoff L Λ x t))
      (PowerWordWeight.contentAppendIsoTo D Sc cutoff L s i β.1 (blockSucc D Λ i h β).1 rfl
        (elvBlockSucc_content_eq D i Λ h β))
      (PowerWordWeight.contentAppendIsoTo D Sc cutoff L t i β.1 (blockSucc D Λ i h β).1 hst.symm
        (elvBlockSucc_content_eq D i Λ h β)) _ _ hc
    dsimp only [elvBlockInd, elvBlockAppend, wordFamilyArrow, Superfunctor.map]
    simpa only [Category.assoc] using hp
  · have hd : δ.1 ≠ (((s ++ [i]) : List I) : Multiset I) := by
      intro hd
      apply he
      apply Subtype.ext
      change δ.1 = {i} + (s : Multiset I)
      rw [hd, ← Multiset.coe_add]
      exact add_comm _ _
    exact (append_source_isZero D Sc cutoff L Λ s i x y hxs hys h δ hd).eq_of_src _ _

end OddMath.QuiverHecke.ELV.PowerWordWeightWhiskering
end

end

section

/-! # Recursive pair charts for the weight word family

SwappedVacuumCoordinates §§4–6: the supported crossing chart must agree
with the unchanged recursively selected whole single-append comparisons.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerWordPairCoherence
open CyclotomicAction CyclotomicCrossingTensor
universe u
private theorem chart_join {C B : Type*} [Category* C] [Category* B]
    (F : C ⥤ B) {X₀ X₁ Y : C} {A Z W : B}
    (h₀ : A = F.obj X₀) (h₁ : X₀ = X₁) (h₂ : A = F.obj X₁) (h₃ : Z = F.obj Y)
    (e : X₁ ≅ Y) (f : F.obj Y ≅ W) :
    (eqToHom h₀ ≫ F.map (eqToHom h₁ ≫ e.hom) ≫ eqToHom h₃.symm) ≫
      (eqToHom h₃ ≫ f.hom) = eqToHom h₂ ≫ F.map e.hom ≫ f.hom := by
  cases h₁
  cases h₀
  cases h₃
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (Λ : X) (ν : List I) (i j : I) {x₀ xj xu : X}
  (hx : x₀ = PowerWordWeight.wordWeight D Λ ν)
  (h₁ : x₀ + D.α j = xj) (h₂ : xj + D.α i = xu)
  (β : WeightBlocks D Λ x₀) (hν : (ν : Multiset I) = (Subtype.val β))
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "M" => PowerWordWeight.wordFamily D Sc cutoff L Λ x₀ ν
local notation "BJ" => blockSucc D Λ j h₁ β
local notation "BU" => blockSucc₂ D i j Λ h₁ h₂ β
local notation "K" => elvBlockInd D Sc cutoff N j Λ h₁ β
local notation "U" => elvBlockInd D Sc cutoff N i Λ h₂ BJ
local notation "HK" => elvBlockSucc_content_eq D j Λ h₁ β
local notation "HU" => elvWeightPairUpper_content_eq D i j Λ h₁ h₂ β BU rfl
local notation "EK" => PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν j (Subtype.val β) (Subtype.val BJ) hν HK
local notation "EU" => PowerWordWeight.contentAppendIsoTo D Sc cutoff L (ν ++ [j]) i (Subtype.val BJ) (Subtype.val BU)
  (PowerWordContentCross.appendContentEq ν j (Subtype.val β) (Subtype.val BJ) hν HK) HU

/-- The recursively chosen whole pair chart agrees on its occupied component
with the existing rectangular chart and the recursively chosen content chart. -/
theorem recursive_pair_component :
    (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν i j hx h₁ h₂).hom BU =
      (PowerWordWeightCross.pairComponentIso D Sc cutoff L ν i j Λ h₁ h₂ β BU rfl hν).hom := by
  have hxj : xj = PowerWordWeight.wordWeight D Λ (ν ++ [j]) :=
    h₁.symm.trans ((congrArg (fun x => x + D.α j) hx).trans
      (PowerWordWeight.wordWeight_append D Λ ν j))
  have hxu : xu = PowerWordWeight.wordWeight D Λ ((ν ++ [j]) ++ [i]) :=
    h₂.symm.trans ((congrArg (fun x => x + D.α i) hxj).trans
      (PowerWordWeight.wordWeight_append D Λ (ν ++ [j]) i))
  change (elvInductionComponent D Sc cutoff N i Λ h₂ BU).map
      (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν j x₀ xj hx hxj h₁).hom ≫
        (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ (ν ++ [j]) i xj xu hxj hxu h₂).hom BU = _
  rw [elvInductionComponent_map_blockSucc D Sc cutoff N i Λ h₂ BJ,
    PowerWordWeightWhiskering.append_component D Sc cutoff L Λ ν j x₀ xj hx hxj h₁ β hν,
    PowerWordWeightWhiskering.append_component D Sc cutoff L Λ (ν ++ [j]) i xj xu hxj hxu h₂ BJ
      (PowerWordContentCross.appendContentEq ν j (Subtype.val β) (Subtype.val BJ) hν HK)]
  have hp := chart_join (U).toFunctor
    (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ BJ
      ((elvE D Sc cutoff N j Λ h₁).obj M))
    (elvInductionComponent_obj_blockSucc D Sc cutoff N j Λ h₁ β M)
    (Functor.congr_obj (elvEFunctor_comp₂_rectangular_eq D Sc cutoff N i j Λ h₁ h₂ β BU rfl) M)
    (elvInductionComponent_obj_blockSucc D Sc cutoff N i Λ h₂ BJ
      (PowerWordWeight.wordFamily D Sc cutoff L Λ xj (ν ++ [j]))) EK EU
  dsimp only [elvBlockInd, elvBlockAppend, PowerWordWeight.wordFamily, Superfunctor.map] at hp ⊢
  simpa only [PowerWordWeightCross.pairComponentIso, PowerWordContentCross.pairIsoTo,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, eqToIso.hom, eqToHom_app,
    Category.assoc] using hp

/-- The supported crossing chart has exactly the same whole hom as the
unchanged recursive single-append chart, including every zero component. -/
theorem recursive_pair_hom :
    (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν i j hx h₁ h₂).hom =
      (PowerWordWeightCross.pairFamilyIso D Sc cutoff L Λ ν i j h₁ h₂ β hν).hom := by
  funext ε
  classical
  by_cases hε : BU = ε
  · subst ε
    rw [PowerWordWeightCross.pairFamilyIso_hom_of D Sc cutoff L Λ ν i j h₁ h₂ β hν BU rfl]
    exact recursive_pair_component D Sc cutoff L Λ ν i j hx h₁ h₂ β hν
  · exact (PowerWordWeightCross.pair_source_isZero D Sc cutoff L Λ ν i j h₁ h₂ β hν ε hε).eq_of_src _ _

variable {xi : X} (h₃ : x₀ + D.α i = xi) (h₄ : xi + D.α j = xu)
/-- The given whole weight crossing in the unchanged recursively selected
word charts, for both colour cases and all exterior coefficient vectors. -/
theorem recursive_pair_cross :
    (elvActionCross D Sc cutoff N i j Λ h₁ h₂ h₃ h₄).app (D.parity i * D.parity j) M ≫
      (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν j i hx h₃ h₄).hom =
    (PowerWordWeightCross.recursivePairIso D Sc cutoff L Λ ν i j hx h₁ h₂).hom ≫
      PowerWordWeightCross.wordFamilyCross D Sc cutoff L Λ ν i j (xu := xu) := by
  let β₀ : WeightBlocks D Λ x₀ := ⟨ν, hx.symm⟩
  rw [recursive_pair_hom D Sc cutoff L Λ ν j i hx h₃ h₄ β₀ rfl,
    recursive_pair_hom D Sc cutoff L Λ ν i j hx h₁ h₂ β₀ rfl]
  exact PowerWordWeightCross.weight_pair_cross D Sc cutoff L Λ ν i j h₁ h₂ β₀ rfl h₃ h₄
end OddMath.QuiverHecke.ELV.PowerWordPairCoherence
end

end

section

/-! # Evenness of the selected word charts

SwappedVacuumCoordinates §§4–6: unit evaluation and cyclicity detect the
parity of the existing word comparisons before odd generator transport.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.PowerWordChartParity
open CyclotomicAction
universe u
section Generic
variable {k C B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
private theorem even_comp {E : Type*} [Category* E] [Preadditive E] [Linear k E] [Supercategory k E]
    {A Z W : E} {f : A ⟶ Z} {g : Z ⟶ W}
    (hf : f ∈ parity (R := k) _ _ 0) (hg : g ∈ parity (R := k) _ _ 0) :
    f ≫ g ∈ parity (R := k) _ _ 0 := by
  simpa only [zero_add] using comp_mem hf hg

private theorem eq_to_hom_even {E : Type*} [Category* E] [Preadditive E] [Linear k E] [Supercategory k E]
    {A Z : E} (h : A = Z) : eqToHom h ∈ parity (R := k) _ _ 0 := by
  cases h
  exact id_mem _

private theorem even_of_eval {M N : Superfunctor k C (SVec k)} (s : C) (b : M.obj s)
    (H : Function.Injective (fun f : M ⟶ N => f.total s b))
    (hb : b ∈ (M.obj s).part 0) (f : M ⟶ N) (hf : f.total s b ∈ (N.obj s).part 0) :
    f ∈ parity (R := k) _ _ 0 := by
  have h1 := (PowerWordContentCross.even_unit_components f s b (f.total s b) hb hf rfl).2
  have hp : proj k 1 f = 0 := by
    apply H
    simp only [SuperNatTrans.total, Superfunctor.proj_app, Superfunctor.zero_app,
      show (0 : ZMod 2) ≠ 1 from by decide, ite_false, ite_true, zero_add, h1]
    rfl
  have hs : proj k 0 f + proj k 1 f = f := proj_add_proj f
  rw [hp, add_zero] at hs
  rw [← hs]
  exact proj_mem 0 f

variable (J : C ⥤ B) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
private theorem adjunction_evaluate (M : Superfunctor k C (SVec k))
    (N : Superfunctor k B (SVec k)) (s : C) (b : M.obj s)
    (f : BalancedInduction.induced J M ⟶ N) :
    ((BalancedInduction.adjunction J).homEquiv M N f).total s b =
      f.total (J.obj s) (BalancedInduction.unit J M.toFunctor s b) := by
  rw [Adjunction.homEquiv_unit, Superfunctor.comp_total, SVec.comp_apply]
  change ((BalancedInduction.restriction J).map f).total s
    (((BalancedInduction.adjunctionUnit J).app M).total s b) = _
  rw [BalancedInduction.unit_total_apply]
  rfl

private theorem induction_eval_injective (M : Superfunctor k C (SVec k))
    (N : Superfunctor k B (SVec k)) (s : C) (b : M.obj s)
    (H : Function.Injective (fun f : M ⟶ (BalancedInduction.restriction J).obj N => f.total s b)) :
    Function.Injective (fun f : BalancedInduction.induced J M ⟶ N =>
      f.total (J.obj s) (BalancedInduction.unit J M.toFunctor s b)) := by
  intro f g h
  apply ((BalancedInduction.adjunction J).homEquiv M N).injective
  apply H
  change ((BalancedInduction.adjunction J).homEquiv M N f).total s b =
    ((BalancedInduction.adjunction J).homEquiv M N g).total s b
  exact (adjunction_evaluate J M N s b f).trans (h.trans (adjunction_evaluate J M N s b g).symm)
private theorem unit_even (M : Superfunctor k C (SVec k)) (s : C) (b : M.obj s)
    (hb : b ∈ (M.obj s).part 0) :
    (show (BalancedInduction.induced J M).obj (J.obj s) from
      BalancedInduction.unit J M.toFunctor s b) ∈
      ((BalancedInduction.induced J M).obj (J.obj s)).part 0 := by
  change BalancedInduction.unit J M.toFunctor s b ∈
    (BalancedInduction.superspace J M.toFunctor (J.obj s)).part 0
  simpa only [zero_add] using SVec.apply_mem_part (BalancedInduction.unit_mem J M s) hb

end Generic

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (ν : List I) (i : I) (β γ : Multiset I)
  (hν : (ν : Multiset I) = β) (hi : β + ([i] : Multiset I) = γ)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "J" => contentAppendTo D Sc cutoff N β [i] γ hi
local notation "M" => PowerWordWeight.wordAt D Sc cutoff L ν β
local notation "P" => PowerWordWeight.wordAt D Sc cutoff L (ν ++ [i]) γ
local notation "S" => PowerWordContentCyclicity.wordObject D Sc cutoff L ν β hν
local notation "B" => PowerWordContentCyclicity.wordUnit D Sc cutoff L ν β hν
local notation "W" => CategoryTheory.Functor.obj J S
local notation "HI" => PowerWordContentCross.appendContentEq ν i β γ hν hi
local notation "E" => PowerWordWeight.contentAppendIsoTo D Sc cutoff L ν i β γ hν hi

/-- The given exact-content append comparison is even at every valid content
presentation, detected from its unit image and the cyclic source adjunction. -/
theorem content_append_to_even :
    (E).hom ∈ parity (R := k) _ _ 0 := by
  have H : Function.Injective (fun f : BalancedInduction.induced J M ⟶ P =>
      f.total W (BalancedInduction.unit J (M).toFunctor S B)) := by
    apply induction_eval_injective
    intro f g h
    exact PowerWordContentCyclicity.hom_ext D Sc cutoff L ν β hν
      ((BalancedInduction.restriction J).obj P) f g h
  apply even_of_eval W (BalancedInduction.unit J (M).toFunctor S B) H
  · exact unit_even J M S B (PowerWordContentCyclicity.wordUnit_even D Sc cutoff L ν β hν)
  · rw [PowerWordContentCross.append_unit_to D Sc cutoff L ν i β γ hν hi]
    exact PowerWordContentCyclicity.wordUnit_even D Sc cutoff L (ν ++ [i]) γ HI

/-- The existing whole single-append weight chart is even on all components. -/
theorem weight_append_even (Λ : X) :
    (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom ∈ parity (R := k) _ _ 0 := by
  intro δ
  classical
  by_cases hδ : δ = blockSucc D Λ i (PowerWordWeight.wordWeight_append D Λ ν i)
      (PowerWordWeight.wordBlock D Λ ν)
  · subst δ
    change (PowerWordWeightCross.appendIsoAtWeights D Sc cutoff L Λ ν i _ _ rfl rfl
      (PowerWordWeight.wordWeight_append D Λ ν i)).hom _ ∈ _
    rw [PowerWordWeightWhiskering.append_component D Sc cutoff L Λ ν i _ _ rfl rfl
      (PowerWordWeight.wordWeight_append D Λ ν i) (PowerWordWeight.wordBlock D Λ ν) rfl]
    exact even_comp (eq_to_hom_even _) (content_append_to_even D Sc cutoff L ν i _ _ rfl
      (elvBlockSucc_content_eq D i Λ (PowerWordWeight.wordWeight_append D Λ ν i)
        (PowerWordWeight.wordBlock D Λ ν)))
  · have hz : (PowerWordWeight.weightAppendIso D Sc cutoff L Λ ν i).hom δ = 0 :=
      (PowerWordWeight.weightAppend_isZero D Sc cutoff L Λ ν i δ hδ).eq_of_src _ _
    rw [hz]
    exact Submodule.zero_mem _

end OddMath.QuiverHecke.ELV.PowerWordChartParity
end

end
