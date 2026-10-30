/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentPureReservoir

/-! # Repeated-outer reservoir factor braid

The dotted correction in the factor relation is transported through the
prescribed three reservoir parity shifts. This is a normalized factor identity;
identification with the literal path-matrix dot polynomial is separate.
-/

noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u,u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {D : Datum I X} {Sc : Scalars D k}

variable [∀ a b : B, PiSupercategory k (a ⟶ b)]
namespace ProbeReservoir

/-- The dotted correction of the reservoir factor on the repeated-outer triple. -/
def repeatedOuterReservoirCorrection (P : ProbeReservoir k B D Sc)
    (i j : I) {a b c d : X}
    (hab : a + D.α i = b) (hbc : b + D.α j = c) (hcd : c + D.α i = d) :
    End (P.W.E i hab ≫ P.W.E j hbc ≫ P.W.E i hcd) :=
      ∑ s ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
          (rouquierPower (P.W.dot i hab) s ▷ (P.W.E j hbc ≫ P.W.E i hcd) ≫
            P.W.E i hab ◁ P.W.E j hbc ◁ rouquierPower (P.W.dot i hcd) (D.dn i j - 1 - s)) +
      ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i), ∑ s ∈ Finset.range p,
        (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p q) •
          (rouquierPower (P.W.dot i hab) s ▷ (P.W.E j hbc ≫ P.W.E i hcd) ≫
            P.W.E i hab ◁ (rouquierPower (P.W.dot j hbc) q ▷ P.W.E i hcd) ≫
            P.W.E i hab ◁ P.W.E j hbc ◁ rouquierPower (P.W.dot i hcd) (p - 1 - s))

/-- Corrected braid for the normalized reservoir cores, with their content shifts. -/
theorem repeatedOuterPureReservoir_factor_braid (P : ProbeReservoir k B D Sc)
    (i j : I) (hne : i ≠ j) (β : I →₀ ℕ) {a bi bj cij cii d : X}
    (hi : a + D.α i = bi) (hj : a + D.α j = bj)
    (hij : bi + D.α j = cij) (hji : bj + D.α i = cij)
    (hii : bi + D.α i = cii)
    (hd12 : cij + D.α i = d) (hd13 : cii + D.α j = d) {e : B} (Z : e ⟶ P.W.obj a) :
    let pi := homContentShift D i β
    let pj := homContentShift D j β
    (homParityShift (k := k) pi).map
      (resCore P.W j i pj pi hi hij hj hji Z ▷ P.W.E i hd12) ≫
      resCore P.W i i pi pi hji hd12 hji hd12
        ((homParityShift (k := k) pj).obj (Z ≫ P.W.E j hj)) ≫
      (homParityShift (k := k) pi).map
        (resCore P.W i j pi pj hj hji hi hij Z ▷ P.W.E i hd12) - (
    resCore P.W i j pi pj hij hd12 hii hd13
        ((homParityShift (k := k) pi).obj (Z ≫ P.W.E i hi)) ≫
      (homParityShift (k := k) pj).map
        (resCore P.W i i pi pi hi hii hi hii Z ▷ P.W.E j hd13) ≫
      resCore P.W j i pj pi hii hd13 hij hd12
        ((homParityShift (k := k) pi).obj (Z ≫ P.W.E i hi))) =
    -(sign k (homContentShift D i β * (D.parity j * D.parity i)) •
      ((reservoirTotalIso Z (P.W.E i hi) (P.W.E j hij) (P.W.E i hd12) pi pj pi).hom ≫
        Z ◁ P.repeatedOuterReservoirCorrection i j hi hij hd12 ≫
        (reservoirTotalIso Z (P.W.E i hi) (P.W.E j hij) (P.W.E i hd12) pi pj pi).inv)) := by
  dsimp only
  simp only [resCore_content_eq]
  apply (cancel_mono (reservoirTotalIso Z (P.W.E i hi) (P.W.E j hij) (P.W.E i hd12)
    (homContentShift D i β) (homContentShift D j β) (homContentShift D i β)).hom).mp
  have inner := @reservoirTotal_inner k _ B _ _ _ _ _ _
  have outer := @reservoirTotal_outer k _ B _ _ _ _ _ _
  have h1 := inner Z _ _ _ _ (P.W.E i hd12)
    (homContentShift D i β) (homContentShift D j β) (homContentShift D i β) _ _
    (P.W.cross_mem j i hi hij hj hji)
  have h2 := outer Z (P.W.E j hj) _ _ _ _
    (homContentShift D j β) (homContentShift D i β) (homContentShift D i β) _ _
    (P.W.cross_mem i i hji hd12 hji hd12)
  have h3 := inner Z _ _ _ _ (P.W.E i hd12)
    (homContentShift D j β) (homContentShift D i β) (homContentShift D i β) _ _
    (P.W.cross_mem i j hj hji hi hij)
  have h4 := outer Z (P.W.E i hi) _ _ _ _
    (homContentShift D i β) (homContentShift D j β) (homContentShift D i β) _ _
    (P.W.cross_mem i j hij hd12 hii hd13)
  have h5 := inner Z _ _ _ _ (P.W.E j hd13)
    (homContentShift D i β) (homContentShift D i β) (homContentShift D j β) _ _
    (P.W.cross_mem i i hi hii hi hii)
  have h6 := outer Z (P.W.E i hi) _ _ _ _
    (homContentShift D i β) (homContentShift D i β) (homContentShift D j β) _ _
    (P.W.cross_mem j i hii hd13 hij hd12)
  simp only [Category.assoc] at h1 h2 h3 h4 h5 h6 ⊢
  simp only [Preadditive.sub_comp, Preadditive.neg_comp, Linear.smul_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [h3, h6]
  simp only [Linear.comp_smul]
  rw [reassoc_of% h2, reassoc_of% h5]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h4]
  simp only [Linear.smul_comp, smul_smul, Category.assoc]
  have hs (u v w : I) : homContentShift D u β * (D.parity v * D.parity w) =
      contentParity D β * (D.parity u * D.parity v * D.parity w) :=
    reservoir_content_sign u v w β
  have hb := P.reservoirRel.braidEq i j hne hi hj hij hii hji hd12 hd13
  have hs2 : homContentShift D j β * (D.parity i * D.parity i) =
      homContentShift D i β * (D.parity j * D.parity i) := by rw [hs, hs]; ring
  simp only [hs2, mul_comm (D.parity i) (D.parity j), ← mul_assoc,
    Supercategory.sign_mul_self, mul_one]
  rw [← smul_sub, ← Preadditive.comp_sub]
  have hb' : _ = -P.repeatedOuterReservoirCorrection i j hi hij hd12 :=
    (neg_sub _ _).symm.trans (congrArg Neg.neg hb)
  have hw := congrArg (fun f => Z ◁ f) hb'
  simp only [sub_eq_add_neg, TwoSupercategory.whiskerLeft_add (R := k),
    TwoSupercategory.whiskerLeft_neg (R := k),
    TwoSupercategory.whiskerLeft_comp (R := k)] at hw
  simp only [TwoSupercategory.whiskerLeft_comp (R := k), Category.assoc]
  rw [sub_eq_add_neg, hw]
  simp only [Preadditive.comp_neg, smul_neg]

/-- Subtraction of two three-edge composites is compatible with transport
of all six objects. -/
theorem repeatedOuterHexagon_difference_heq {C : Type*} [Category C] [Preadditive C]
    {A B₁ B₂ D₀ C₁ C₂ A' B₁' B₂' D' C₁' C₂' : C}
    (hA : A = A') (hB₁ : B₁ = B₁') (hB₂ : B₂ = B₂') (hD : D₀ = D')
    (hC₁ : C₁ = C₁') (hC₂ : C₂ = C₂')
    {f : A ⟶ B₁} {g : B₁ ⟶ B₂} {h : B₂ ⟶ D₀}
    {l : A ⟶ C₁} {m : C₁ ⟶ C₂} {n : C₂ ⟶ D₀}
    {f' : A' ⟶ B₁'} {g' : B₁' ⟶ B₂'} {h' : B₂' ⟶ D'}
    {l' : A' ⟶ C₁'} {m' : C₁' ⟶ C₂'} {n' : C₂' ⟶ D'}
    (ef : HEq f f') (eg : HEq g g') (eh : HEq h h')
    (el : HEq l l') (em : HEq m m') (en : HEq n n')
    {δ : A' ⟶ D'} (hb : f' ≫ g' ≫ h' - l' ≫ m' ≫ n' = δ) :
    HEq ((f ≫ g) ≫ h - (l ≫ m) ≫ n) δ := by
  subst hA hB₁ hB₂ hD hC₁ hC₂
  cases ef; cases eg; cases eh; cases el; cases em; cases en
  exact heq_of_eq (by simpa only [Category.assoc] using hb)

/-- The diagonal repeated-outer reservoir path braid, expressed in normalized
factor coordinates. The right side retains the full dotted correction and its
content-dependent shift sign. -/
theorem repeatedOuterPureReservoir_canonical_heq (P : ProbeReservoir k B D Sc)
    (ν : X) (i j : I) (s : Sector I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hne : i ≠ j)
    (hi : StepValid (true, i) false s)
    (hj : StepValid (true, j) false (nextSector (true, i) false s))
    (hr : StepValid (true, i) false (nextSector (true, j) false
      (nextSector (true, i) false s)))
    (Z : P.H (nextSector (true, i) false (nextSector (true, j) false
      (nextSector (true, i) false s)))) :
    let p := distinctPureReservoirPath (D := D) ν i j i s hi hj hr rfl
    let Θ := reservoirTotalIso (k := k) Z (P.W.E i (P.muM_postE i hr))
      (P.W.E j (P.muM_postE j hj)) (P.W.E i (P.muM_postE i hi))
      (homContentShift D i s.1) (homContentShift D j s.1) (homContentShift D i s.1)
    HEq (braidLeft (P.swappedGens c L) i j i ν p p Z -
      braidRight (P.swappedGens c L) i j i ν p p Z)
      (sign k (homContentShift D i s.1 * (D.parity j * D.parity i)) •
        (Θ.hom ≫ Z ◁ P.repeatedOuterReservoirCorrection i j
          (P.muM_postE i hr) (P.muM_postE j hj) (P.muM_postE i hi) ≫ Θ.inv)) := by
  classical
  dsimp only
  have e : nextSector (true, i) false (nextSector (true, j) false
      (nextSector (true, i) false s)) =
      nextSector (true, i) false (nextSector (true, j) false
      (nextSector (true, i) false s)) := rfl
  have hr' := hi
  have hj' := hj
  have hi' := hr
  let t := nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) false s))
  have valid_swap (i j : I) (s : Sector I)
      (hi : StepValid (true, i) false s)
      (hj : StepValid (true, j) false (nextSector (true, i) false s)) :
      StepValid (true, j) false s ∧
        StepValid (true, i) false (nextSector (true, j) false s) := by
    by_cases hij : i = j
    · subst j; exact ⟨hi, hj⟩
    exact ⟨(pureReservoir_valid_iff i j hij s).mp hj,
      (pureReservoir_valid_iff j i (Ne.symm hij) s).mpr hi⟩
  obtain ⟨vj, vji⟩ := valid_swap i j s hi hj
  have vjir : StepValid (true, i) false
      (nextSector (true, i) false (nextSector (true, j) false s)) := by
    rw [← pureReservoir_swap i j s]; exact hr
  obtain ⟨vjr, vjri⟩ := valid_swap i i _ vji vjir
  obtain ⟨vir, virj⟩ := valid_swap j i _ hj hr
  obtain ⟨_, vri⟩ := valid_swap i i s hi vir
  have vrij : StepValid (true, j) false
      (nextSector (true, i) false (nextSector (true, i) false s)) := by
    rw [← pureReservoir_swap i i s]; exact virj
  have e213 : nextSector (true, i) false (nextSector (true, i) false (nextSector (true, j) false s)) = t :=
    (congrArg (nextSector (true, i) false) (pureReservoir_swap j i s)).trans e
  have e231 : nextSector (true, i) false (nextSector (true, i) false (nextSector (true, j) false s)) = t :=
    (pureReservoir_swap i i _).trans e213
  have e132 : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) false s)) = t :=
    (pureReservoir_swap i j _).trans e
  have e312 : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) false s)) = t :=
    (pureReservoir_swap i j _).trans rfl
  let : Subsingleton (SPath (wd D ν [up j, up i, up i]) s t) :=
    ⟨fun p q => (pureReservoirPath_unique vj vji vjir e213 p).trans
      (pureReservoirPath_unique vj vji vjir e213 q).symm⟩
  let : Subsingleton (SPath (wd D ν [up j, up i, up i]) s t) :=
    ⟨fun p q => (pureReservoirPath_unique vj vjr vjri e231 p).trans
      (pureReservoirPath_unique vj vjr vjri e231 q).symm⟩
  let : Subsingleton (SPath (wd D ν [up i, up i, up j]) s t) :=
    ⟨fun p q => (pureReservoirPath_unique hi vir virj e132 p).trans
      (pureReservoirPath_unique hi vir virj e132 q).symm⟩
  let : Subsingleton (SPath (wd D ν [up i, up i, up j]) s t) :=
    ⟨fun p q => (pureReservoirPath_unique hr' vri vrij e312 p).trans
      (pureReservoirPath_unique hr' vri vrij e312 q).symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up i]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up j, up i, up i]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up i, up i, up j]) s t)
  let := Fintype.ofFinite (SPath (wd D ν [up i, up i, up j]) s t)
  unfold braidLeft braidRight
  rw [Fintype.sum_subsingleton _ (distinctPureReservoirPath (D := D) ν j i i s vj vjr vjri e231),
    Fintype.sum_subsingleton _ (distinctPureReservoirPath (D := D) ν j i i s vj vji vjir e213),
    Fintype.sum_subsingleton _ (distinctPureReservoirPath (D := D) ν i i j s hr' vri vrij e312),
    Fintype.sum_subsingleton _ (distinctPureReservoirPath (D := D) ν i i j s hi vir virj e132)]
  have wji := congrArg P.muM (pureReservoir_swap i j s)
  have wri := congrArg P.muM (pureReservoir_swap i i s)
  have wrj := congrArg P.muM (pureReservoir_swap j i s)
  have hji : P.muM (nextSector (true, j) false (nextSector (true, i) false s)) + D.α i =
      P.muM (nextSector (true, j) false s) := by
    rw [wji]; exact P.muM_postE i vji
  have hri : P.muM (nextSector (true, i) false (nextSector (true, i) false s)) + D.α i =
      P.muM (nextSector (true, i) false s) := by
    rw [wri]; exact P.muM_postE i vri
  have hrj : P.muM (nextSector (true, i) false (nextSector (true, j) false s)) + D.α j =
      P.muM (nextSector (true, i) false s) := by
    rw [wrj]; exact P.muM_postE j hj'
  have hd12 : P.muM t + D.α i =
      P.muM (nextSector (true, j) false (nextSector (true, i) false s)) := by
    dsimp only [t]
    rw [← e]; exact P.muM_postE i hr
  have hd13 : P.muM t + D.α j =
      P.muM (nextSector (true, i) false (nextSector (true, i) false s)) := by
    rw [← e132]; exact P.muM_postE j virj
  have hd23 : P.muM t + D.α i =
      P.muM (nextSector (true, i) false (nextSector (true, j) false s)) := by
    rw [← e231]; exact P.muM_postE i vjri
  exact repeatedOuterHexagon_difference_heq
    (eq_of_heq (P.distinctPureReservoir_obj ν i j i s hi hj hr e Z rfl rfl rfl rfl
      (P.muM_postE i hi) (P.muM_postE j hj) hd12 Z HEq.rfl))
    (eq_of_heq (P.distinctPureReservoir_obj ν j i i s vj vji vjir e213 Z rfl wji rfl rfl
      (P.muM_postE j vj) hji hd12 Z HEq.rfl))
    (eq_of_heq (P.distinctPureReservoir_obj ν j i i s vj vjr vjri e231 Z rfl wji rfl rfl
      (P.muM_postE j vj) hji hd12 Z HEq.rfl))
    (eq_of_heq (P.distinctPureReservoir_obj ν i j i s hr' hj' hi' rfl Z rfl rfl rfl rfl
      (P.muM_postE i hr') (P.muM_postE j hj) hd12 Z HEq.rfl))
    (eq_of_heq (P.distinctPureReservoir_obj ν i i j s hi vir virj e132 Z rfl rfl rfl rfl
      (P.muM_postE i hi) (P.muM_postE i vir) hd13 Z HEq.rfl))
    (eq_of_heq (P.distinctPureReservoir_obj ν i i j s hr' vri vrij e312 Z rfl wri rfl rfl
      (P.muM_postE i hr') hri hd13 Z HEq.rfl))
    (P.distinctPureReservoir_left_core ν i j i s c L hi hj hr vj vji vjir
      (pureReservoir_swap i j s) e e213 Z rfl rfl rfl rfl
      (P.muM_postE i hi) (P.muM_postE j hj) (P.muM_postE j vj) hji hd12)
    (P.distinctPureReservoir_right_core ν j i i s c L vj vji vjir vjr vjri e213 e231 Z
      rfl wji wji rfl (P.muM_postE j vj) hji hji hd12 hd12)
    (P.distinctPureReservoir_left_core ν j i i s c L
      vj vjr vjri hr' hj' hi' (pureReservoir_swap j i s) e231 rfl Z rfl rfl wji rfl
      (P.muM_postE j vj) hji (P.muM_postE i hr') (P.muM_postE j hj) hd12)
    (P.distinctPureReservoir_right_core ν i j i s c L hi hj hr vir virj e e132 Z
      rfl rfl rfl rfl (P.muM_postE i hi) (P.muM_postE j hj) (P.muM_postE i vir) hd12 hd13)
    (P.distinctPureReservoir_left_core ν i i j s c L hi vir virj hr' vri vrij
      (pureReservoir_swap i i s) e132 e312 Z rfl rfl rfl rfl
      (P.muM_postE i hi) (P.muM_postE i vir) (P.muM_postE i hr') hri hd13)
    (P.distinctPureReservoir_right_core ν i i j s c L hr' vri vrij hj' hi' e312 rfl Z
      rfl wri rfl rfl (P.muM_postE i hr') hri (P.muM_postE j hj) hd13 hd12)
    (by
      have hf := P.repeatedOuterPureReservoir_factor_braid i j hne s.1
        hd12 hd13 (P.muM_postE j hj) hri hji
        (P.muM_postE i hi) (P.muM_postE j vj) Z
      have hn := congrArg Neg.neg hf
      simpa only [neg_sub, neg_neg] using hn)

/-- At a pure-reservoir endpoint the repeated-outer word has only one path. -/
theorem repeatedOuterPureReservoir_path_eq (ν : X) (i j : I) {s t : Sector I}
    (ht : t.1 = s.1)
    (p q : SPath (wd D ν [up i, up j, up i]) s t) : p = q := by
  obtain ⟨hi, hj, hr, e, rfl⟩ := pureReservoirPath_cases ht p
  exact (pureReservoirPath_unique hi hj hr e q).symm

/-- Off-diagonal entries in a pure-reservoir sector are zero: distinct paths
cannot have such an endpoint. -/
theorem repeatedOuterPureReservoir_offdiag (P : ProbeReservoir k B D Sc)
    (ν : X) (i j : I) {s t : Sector I} (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (ht : t.1 = s.1) (p q : SPath (wd D ν [up i, up j, up i]) s t)
    (hpq : p ≠ q) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j i ν p q Z = 0 ∧
      braidRight (P.swappedGens c L) i j i ν p q Z = 0 := by
  exact (hpq (repeatedOuterPureReservoir_path_eq ν i j ht p q)).elim

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
