/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedAppend
import OddMath.QuiverHecke.CyclotomicAction.AppendBalance

/-! # Appended affine transformations

Affine morphisms on the appended word act by left whiskering. Their
supernaturality uses total coefficient-plus-diagram parity.
-/
noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The prescribed affine morphism on the right of a word. -/
def appendComponent {σ τ : List I}
    (h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)) (v : List I) :
    hom D Sc cutoff (v ++ σ) (v ++ τ) :=
  (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
    ((pres D Sc).obj (ob D v) ◁ h)

theorem appendComponent_mem {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) (v : List I) :
    appendComponent D Sc cutoff h v ∈ parity (R := k)
      (obj D Sc cutoff (v ++ σ)) (obj D Sc cutoff (v ++ τ)) p := by
  have he := BoxProd.tmul_mem_parity (X := obj D Sc cutoff (v ++ σ))
    (Y := obj D Sc cutoff (v ++ τ))
    (Supercategory.id_mem (R := k) (obj D Sc cutoff v).fst)
    (MonoidalSupercategory.whiskerLeft_mem ((pres D Sc).obj (ob D v)) hh)
  rw [zero_add] at he
  exact he

private theorem box_append_naturality
    {A : Type*} {C : Type u} [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [MonoidalCategoryStruct C] [MonoidalSupercategory k C]
    (a₀ : A) {V W S T : C} {p q r : ZMod 2}
    {h : S ⟶ T} (hh : h ∈ parity (R := k) _ _ p)
    (a : a₀ ⟶ a₀) (g : V ⟶ W)
    (ha : a ∈ parity (R := k) _ _ q) (hg : g ∈ parity (R := k) _ _ r) :
    BoxProd.tmulHom (k := k) (X := ⟨a₀, V ⊗ S⟩) (Y := ⟨a₀, W ⊗ S⟩) a (g ▷ S) ≫
      BoxProd.tmulHom (k := k) (X := ⟨a₀, W ⊗ S⟩) (Y := ⟨a₀, W ⊗ T⟩) (𝟙 a₀) (W ◁ h) =
    koszulSign p (q + r) • (BoxProd.tmulHom (k := k)
      (X := ⟨a₀, V ⊗ S⟩) (Y := ⟨a₀, V ⊗ T⟩) (𝟙 a₀) (V ◁ h) ≫
      BoxProd.tmulHom (k := k) (X := ⟨a₀, V ⊗ T⟩) (Y := ⟨a₀, W ⊗ T⟩) a (g ▷ T)) := by
  rw [BoxProd.tmulHom_comp_tmulHom ha _ _
    (MonoidalSupercategory.whiskerLeft_mem _ hh),
    BoxProd.tmulHom_comp_tmulHom (X := ⟨a₀, V ⊗ S⟩)
      (Y := ⟨a₀, V ⊗ T⟩) (Z := ⟨a₀, W ⊗ T⟩)
      (Supercategory.id_mem (R := k) a₀) _ _
      (MonoidalSupercategory.whiskerRight_mem _ hg),
    koszulSign_zero_left, one_smul, Category.comp_id, Category.id_comp,
    MonoidalSupercategory.super_interchange hg hh]
  simp only [BoxProd.tmulHom_def, TensorProduct.tmul_smul, smul_smul]
  congr 1
  rw [koszulSign_add_right, koszulSign_comm p q, koszulSign_comm p r]

/-- The sign includes exterior coefficient parity, not only affine parity. -/
theorem appendComponent_naturality_tmul {σ τ v w : List I} {p q r : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p)
    (a : (obj D Sc cutoff v).fst ⟶ (obj D Sc cutoff w).fst)
    (g : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w))
    (ha : a ∈ parity (R := k) _ _ q) (hg : g ∈ parity (R := k) _ _ r) :
    rightContext D Sc cutoff σ v w (a ⊗ₜ[k] g) ≫ appendComponent D Sc cutoff h w =
      koszulSign p (q + r) • (appendComponent D Sc cutoff h v ≫
        rightContext D Sc cutoff τ v w (a ⊗ₜ[k] g)) := by
  have he := box_append_naturality
    (C := H D Sc) (obj D Sc cutoff v).fst
    (V := (pres D Sc).obj (ob D v)) (W := (pres D Sc).obj (ob D w))
    (S := (pres D Sc).obj (ob D σ)) (T := (pres D Sc).obj (ob D τ)) hh a g ha hg
  exact he

theorem appendComponent_naturality_proj {σ τ v w : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) (s : ZMod 2) (f : hom D Sc cutoff v w) :
    rightContext D Sc cutoff σ v w (proj k s f) ≫ appendComponent D Sc cutoff h w =
      koszulSign p s • (appendComponent D Sc cutoff h v ≫
        rightContext D Sc cutoff τ v w (proj k s f)) := by
  induction f using BoxProd.induction_on_homogeneous with
  | zero => simp only [map_zero, Limits.zero_comp, Limits.comp_zero, smul_zero]
  | add f g hf hg =>
    simp only [map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg, smul_add]
  | tmul q r a g ha hg =>
    have ht := BoxProd.tmul_mem_parity ha hg
    by_cases hs : q + r = s
    · subst s
      rw [proj_of_mem ht]
      exact appendComponent_naturality_tmul D Sc cutoff hh a g ha hg
    · rw [proj_of_mem_ne ht hs]
      simp only [map_zero, Limits.zero_comp, Limits.comp_zero, smul_zero]

theorem appendComponent_naturality {σ τ v w : List I} {p q : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) {f : hom D Sc cutoff v w}
    (hf : f ∈ parity (R := k) (obj D Sc cutoff v) (obj D Sc cutoff w) q) :
    rightContext D Sc cutoff σ v w f ≫ appendComponent D Sc cutoff h w =
      koszulSign p q • (appendComponent D Sc cutoff h v ≫
        rightContext D Sc cutoff τ v w f) := by
  have he := appendComponent_naturality_proj D Sc cutoff hh q f
  rwa [proj_of_mem hf] at he

variable (N : ℕ)

/-- The quotient class of the appended affine morphism. -/
def truncatedAppendComponent {σ τ : List I}
    (h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ))
    (v : TruncatedCategory D Sc cutoff N) :
    (truncatedAppend D Sc cutoff N σ).obj v ⟶
      (truncatedAppend D Sc cutoff N τ).obj v :=
  (truncatedIdeal D Sc cutoff N _ _).mkQ (appendComponent D Sc cutoff h v.word)

/-- Every homogeneous affine morphism gives a supernatural right-append transformation. -/
theorem truncatedAppendComponent_supernatural {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) :
    IsSupernatural k p (truncatedAppendComponent D Sc cutoff N h) where
  mem v := Submodule.mem_map_of_mem (appendComponent_mem D Sc cutoff hh v.word)
  naturality := by
    rintro v w q f ⟨a, ha, rfl⟩
    have he := congrArg (truncatedIdeal D Sc cutoff N (v.word ++ σ) (w.word ++ τ)).mkQ
      (appendComponent_naturality D Sc cutoff hh ha)
    rw [map_zsmul, koszulSign_smul (R := k)] at he
    exact he

/-- The affine right-append transformation, retaining its specified parity. -/
def truncatedAppendTransform {σ τ : List I} {p : ZMod 2}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ parity (R := k) _ _ p) :
    SuperNatTrans k (truncatedAppend D Sc cutoff N σ) (truncatedAppend D Sc cutoff N τ) :=
  (truncatedAppendComponent_supernatural D Sc cutoff N hh).toSuperNatTrans

/-- The appended dot is the prescribed last-strand affine dot. -/
def truncatedAppendDot (i : I) :
    SuperNatTrans k (truncatedAppend D Sc cutoff N [i]) (truncatedAppend D Sc cutoff N [i]) :=
  truncatedAppendTransform D Sc cutoff N (by
    simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)

/-- The appended crossing retains the source and target colour order. -/
def truncatedAppendCross (i j : I) :
    SuperNatTrans k (truncatedAppend D Sc cutoff N [i, j])
      (truncatedAppend D Sc cutoff N [j, i]) :=
  truncatedAppendTransform D Sc cutoff N (crossTwo_mem D Sc i j)

@[simp] theorem truncatedAppendDot_app (i : I) (v : TruncatedCategory D Sc cutoff N) :
    (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v =
      truncatedAppendComponent D Sc cutoff N (dotE D Sc [i] 0) v := by
  simp only [truncatedAppendDot, truncatedAppendTransform,
    IsSupernatural.toSuperNatTrans, ↓reduceIte]

@[simp] theorem truncatedAppendCross_app (i j : I) (v : TruncatedCategory D Sc cutoff N) :
    (truncatedAppendCross D Sc cutoff N i j).app (D.parity i * D.parity j) v =
      truncatedAppendComponent D Sc cutoff N (crossTwo D Sc i j) v := by
  simp only [truncatedAppendCross, truncatedAppendTransform,
    IsSupernatural.toSuperNatTrans, ↓reduceIte]

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)

theorem appendComponent_mem_degree {σ τ : List I} {n : ℤ}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ homDegree D sy Sc σ τ n) (v : List I) :
    appendComponent D Sc cutoff h v ∈
      elvHomDegree D sy Sc hc cutoff (v ++ σ) (v ++ τ) n := by
  let _ := elvCoefficientCategoryGrading (k := k) D sy cutoff
  let _ := gradedSupercategory D sy Sc hc
  let _ := gradedMonoidalSupercategory D sy Sc hc
  have he := BoxProd.tmulHom_mem_degree (X := obj D Sc cutoff (v ++ σ))
    (Y := obj D Sc cutoff (v ++ τ))
    (GradedSupercategory.id_mem_degree (R := k) (obj D Sc cutoff v).fst)
    (GradedMonoidalSupercategory.whiskerLeft_mem_degree ((pres D Sc).obj (ob D v)) hh)
  rw [zero_add] at he
  exact he

theorem truncatedAppendComponent_mem_degree {σ τ : List I} {n : ℤ}
    {h : (pres D Sc).obj (ob D σ) ⟶ (pres D Sc).obj (ob D τ)}
    (hh : h ∈ homDegree D sy Sc σ τ n) (v : TruncatedCategory D Sc cutoff N) :
    truncatedAppendComponent D Sc cutoff N h v ∈
      truncatedDegree D Sc cutoff sy hc N (v.word ++ σ) (v.word ++ τ) n :=
  Submodule.mem_map_of_mem (appendComponent_mem_degree D Sc cutoff sy hc hh v.word)

theorem truncatedAppendDot_degree (i : I) (v : TruncatedCategory D Sc cutoff N) :
    (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v ∈
      truncatedDegree D Sc cutoff sy hc N (v.word ++ [i]) (v.word ++ [i])
        (2 * sy.d i) := by
  rw [truncatedAppendDot_app]
  apply truncatedAppendComponent_mem_degree
  unfold dotE genE
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_gdeg_mkD]
    simp [pl, PG.ld, gdeg]
  · exact Submodule.zero_mem _

theorem truncatedAppendCross_degree (i j : I) (v : TruncatedCategory D Sc cutoff N) :
    (truncatedAppendCross D Sc cutoff N i j).app (D.parity i * D.parity j) v ∈
      truncatedDegree D Sc cutoff sy hc N (v.word ++ [i, j]) (v.word ++ [j, i])
        (sy.d i * D.d i j) := by
  rw [truncatedAppendCross_app]
  apply truncatedAppendComponent_mem_degree
  apply Presentation.diag_mem_homDeg'
  rw [degree_gdeg_mkD]
  simp [pl, PG.ld, gdeg]

end OddMath.QuiverHecke.ELVOld
