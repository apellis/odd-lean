import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordContentCross
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightNormalizedRectangularCross

/-! # Chosen weight crossings in regular-power word coordinates

SwappedVacuumCoordinates §§4–6: transport the given weight crossing through
the selected content pair comparisons, with both colour cases included.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerWordWeightCross
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

end OddMath.QuiverHecke.ELVOld.PowerWordWeightCross
