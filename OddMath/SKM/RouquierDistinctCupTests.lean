import OddMath.SKM.RouquierDistinctCupDetection
import OddMath.SKM.RouquierDistinctCapMonomials

/-!
# The distinct cup words and their strict principal tests

Brundan–Ellis, Lemma 7.1, `pcu_a_gt`: the actual cup words are tested
through the specified distinct right mate and the positive augmented
inverse. In the strict range, every mixed-braid correction meets a
lower cup below its boundary, and both principal tests vanish.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
namespace RouquierFamily
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) {Sc : Scalars D k}
  (M : RouquierMulticolour T Sc) {i j : I} (hne : i ≠ j)
  {a b c d e f : X}
  (hi : a + D.α i = b) (hj : a + D.α j = c)
  (hij : b + D.α j = d) (hji : c + D.α i = d)
  (hupper : b + D.α i = e) (hnext : d + D.α i = f) (hej : e + D.α j = f)

/-- The lower raw left cup followed by the prescribed upward crossing. -/
def distinctCupLeft : T.E j hij ⟶ (T.F i hi ≫ T.E j hj) ≫ T.E i hji :=
  (leftUnitor (T.E j hij)).inv ≫ (T.loc i hi hupper).cupL ▷ T.E j hij ≫
    (associator (T.F i hi) (T.E i hi) (T.E j hij)).hom ≫
    T.F i hi ◁ T.cross j i hi hij hj hji ≫
    (associator (T.F i hi) (T.E j hj) (T.E i hji)).inv

/-- The upper raw cup, transported backwards through the actual distinct
right mate. The local cup is centered at `d`. -/
def distinctCupRight : T.E j hij ⟶ (T.F i hi ≫ T.E j hj) ≫ T.E i hji := by
  have := T.distinctCupTarget_isIso M hne hi hj hij hji
  exact (rightUnitor (T.E j hij)).inv ≫ T.E j hij ◁ (T.loc i hji hnext).cupL ≫
    inv (T.distinctCupTarget hi hj hij hji)

/-- The target chart cancels the prescribed inverse before any local test. -/
theorem distinctCupRight_target :
    T.distinctCupRight M hne hi hj hij hji hnext ≫ T.distinctCupTarget hi hj hij hji =
      (rightUnitor (T.E j hij)).inv ≫ T.E j hij ◁ (T.loc i hji hnext).cupL := by
  have := T.distinctCupTarget_isIso M hne hi hj hij hji
  unfold distinctCupRight
  simp only [Category.assoc]
  rw [IsIso.inv_hom_id, Category.comp_id]

/-- The upper right-hand principal test vanishes at positive shifted height. -/
theorem distinctCupRight_principal_of_pos (hh : 0 < D.h i d) :
    T.distinctCupRight M hne hi hj hij hji hnext ≫ T.distinctCupTarget hi hj hij hji ≫
      T.E j hij ◁ (T.loc i hji hnext).sig = 0 := by
  rw [← Category.assoc, T.distinctCupRight_target M hne hi hj hij hji hnext,
    Category.assoc, ← TwoSupercategory.whiskerLeft_comp (R := k),
    (T.loc i hji hnext).cupL_sig hh, TwoSupercategory.whiskerLeft_zero (R := k),
    Limits.comp_zero]

/-- The first mixed word starts with the local equal-colour mate, so a
positive lower cup kills it. -/
theorem distinctMixedBraidLeft_cup_of_pos (hh : 0 < D.h i b) :
    (leftUnitor (T.E j hij)).inv ≫ (T.loc i hi hupper).cupL ▷ T.E j hij ≫
      T.distinctMixedBraidLeft i j hi hij hupper hnext hej = 0 := by
  have hs : crossMate (T.adj i hi) (T.adj i hupper)
      (T.cross i i hi hupper hi hupper) = (T.loc i hi hupper).sig := by
    rw [crossMate_eq_rouquierMate]
    rfl
  have hw := congrArg (fun z => z ▷ T.E j hij) ((T.loc i hi hupper).cupL_sig hh)
  simp only [TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.zero_whiskerRight (R := k)] at hw
  unfold distinctMixedBraidLeft
  rw [hs]
  rw [reassoc_of% hw]
  simp only [Limits.zero_comp, Limits.comp_zero]

include hne in
/-- In the strict cup range every leading-dot exponent in the mixed-braid
correction lies below the lower cup's Kronecker boundary. -/
theorem distinctMixedBraidOuterMate_cup_zero (hh : D.d i j < D.h i b)
    (s q n : ℕ) (hs : s < D.dn i j) :
    (leftUnitor (T.E j hij)).inv ≫ (T.loc i hi hupper).cupL ▷ T.E j hij ≫
      T.distinctMixedBraidOuterMate i j hi hij hnext
        (rouquierPower (T.dot i hi) s ▷ (T.E j hij ≫ T.E i hnext) ≫
          T.E i hi ◁ (rouquierPower (T.dot j hij) q ▷ T.E i hnext) ≫
          T.E i hi ◁ T.E j hij ◁ rouquierPower (T.dot i hnext) n) = 0 := by
  have hd := D.dn_cast hne
  have hb : 0 < D.h i b := lt_of_le_of_lt (D.d_nonneg hne) hh
  have hs' : s < (D.h i b).toNat := by omega
  have hs'' : (D.h i b - 1).toNat ≠ s := by omega
  have hz := (T.loc i hi hupper).cupL_capD hb hs'
  rw [ite_eq_right hs''] at hz
  have hw := congrArg (fun z => z ▷ T.E j hij) hz
  simp only [TwoSupercategory.comp_whiskerRight (R := k),
    TwoSupercategory.zero_whiskerRight (R := k)] at hw
  change (T.loc i hi hupper).cupL ▷ T.E j hij ≫
    (T.F i hi ◁ rouquierPower (T.dot i hi) s ≫ (T.adj i hi).counit) ▷ T.E j hij = 0 at hw
  rw [T.distinctMixedBraidOuterMate_monomial i j hi hij hnext]
  rw [reassoc_of% hw]
  simp only [Limits.zero_comp, Limits.comp_zero]

include M hne hej in
/-- The corrected mixed braid has zero cup composite in the strict
height range; no cup cyclicity hypothesis is used. -/
theorem distinctMixedBraidRight_cup_of_gt (hh : D.d i j < D.h i b) :
    (leftUnitor (T.E j hij)).inv ≫ (T.loc i hi hupper).cupL ▷ T.E j hij ≫
      T.distinctMixedBraidRight i j hi hj hij hji hnext = 0 := by
  have hb : 0 < D.h i b := lt_of_le_of_lt (D.d_nonneg hne) hh
  have he := congrArg (fun z => (leftUnitor (T.E j hij)).inv ≫
      (T.loc i hi hupper).cupL ▷ T.E j hij ≫ z)
    (T.distinctMixedBraid_correction i j hi hj hij hupper hji hnext hej M hne)
  simp only [Preadditive.comp_sub,
    T.distinctMixedBraidLeft_cup_of_pos hi hij hupper hnext hej hb, zero_sub] at he
  have hz : (leftUnitor (T.E j hij)).inv ≫ (T.loc i hi hupper).cupL ▷ T.E j hij ≫
      ((∑ s ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * s) * (Sc.t i j : k)) •
          T.distinctMixedBraidOuterMate i j hi hij hnext
            (rouquierPower (T.dot i hi) s ▷ (T.E j hij ≫ T.E i hnext) ≫
              T.E i hi ◁ T.E j hij ◁ rouquierPower (T.dot i hnext) (D.dn i j - 1 - s))) +
      ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i), ∑ s ∈ Finset.range p,
        (zsign k (D.parity i * s) * Sc.s i j p q) •
          T.distinctMixedBraidOuterMate i j hi hij hnext
            (rouquierPower (T.dot i hi) s ▷ (T.E j hij ≫ T.E i hnext) ≫
              T.E i hi ◁ (rouquierPower (T.dot j hij) q ▷ T.E i hnext) ≫
              T.E i hi ◁ T.E j hij ◁ rouquierPower (T.dot i hnext) (p - 1 - s))) = 0 := by
    simp only [Preadditive.comp_add, Preadditive.comp_sum, Linear.comp_smul]
    refine (congrArg₂ (fun x y => x + y) ?_ ?_).trans (zero_add (0 : _))
    · apply Finset.sum_eq_zero
      intro s hs
      have hz := T.distinctMixedBraidOuterMate_cup_zero hne hi hij hupper hnext hh
        s 0 (D.dn i j - 1 - s) (Finset.mem_range.mp hs)
      simp only [rouquierPower_zero, TwoSupercategory.id_whiskerRight (R := k),
        TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp] at hz
      rw [hz, smul_zero]
    · apply Finset.sum_eq_zero
      intro p hp
      apply Finset.sum_eq_zero
      intro q _
      apply Finset.sum_eq_zero
      intro s hs
      have hp' := Finset.mem_range.mp hp
      have hs' := Finset.mem_range.mp hs
      rw [T.distinctMixedBraidOuterMate_cup_zero hne hi hij hupper hnext hh
        s q (p - 1 - s) (by omega), smul_zero]
  exact neg_eq_zero.mp (he.trans hz)

omit [TwoSupercategory k B] in
/-- The literal lower cup test is exactly the second mixed word. -/
theorem distinctCupLeft_principal_eq :
    T.distinctCupLeft hi hj hij hji hupper ≫ T.distinctCupTarget hi hj hij hji ≫
      T.E j hij ◁ (T.loc i hji hnext).sig =
    (leftUnitor (T.E j hij)).inv ≫ (T.loc i hi hupper).cupL ▷ T.E j hij ≫
      T.distinctMixedBraidRight i j hi hj hij hji hnext := by
  have hs : crossMate (T.adj i hji) (T.adj i hnext)
      (T.cross i i hji hnext hji hnext) = (T.loc i hji hnext).sig := by
    rw [crossMate_eq_rouquierMate]
    rfl
  unfold distinctCupLeft distinctCupTarget distinctMixedBraidRight
  rw [hs]
  simp only [Category.assoc]

include M hne hej in
/-- The actual lower cup word has zero principal test strictly above
`d_ij`, the `pcu_a_gt` input for the positive cup detection. -/
theorem distinctCupLeft_principal_of_gt (hh : D.d i j < D.h i b) :
    T.distinctCupLeft hi hj hij hji hupper ≫ T.distinctCupTarget hi hj hij hji ≫
      T.E j hij ◁ (T.loc i hji hnext).sig = 0 := by
  rw [T.distinctCupLeft_principal_eq hi hj hij hji hupper hnext]
  exact T.distinctMixedBraidRight_cup_of_gt M hne hi hj hij hji hupper hnext hej hh

end RouquierFamily
end OddMath.SKM
