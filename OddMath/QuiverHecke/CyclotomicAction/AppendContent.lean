import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import OddMath.QuiverHecke.CyclotomicAction.EndpointPolynomials
import OddMath.QuiverHecke.CyclotomicAction.CyclotomicQuotientTop
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend
import OddMath.QuiverHecke.CyclotomicAction.MovingShiftRelations
import OddMath.QuiverHecke.CyclotomicAction.AppendMackey
import OddMath.QuiverHecke.CyclotomicAction.ContentModules
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Preorder.Finite
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRight
import OddMath.QuiverHecke.AppendShuffleRuns
import OddMath.QuiverHecke.CyclotomicAction.AppendBalance

/-!
# Append content

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The actual odd dot on the old append superfunctor
The same full-coefficient appended component used by the truncated action
descends to the existing old quotient and is supernatural there.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def oldAppendDotComponent (i : I) (s : OldCategory D Sc cutoff) :
    (append D Sc cutoff i).obj s ⟶ (append D Sc cutoff i).obj s :=
  (ideal D Sc cutoff _ _).mkQ
    (appendComponent D Sc cutoff (dotE D Sc [i] 0) s.word)

theorem oldAppendDotComponent_eq (i : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i s =
      (ideal D Sc cutoff _ _).mkQ (appendMovingPower D Sc cutoff i s.word 1) := by
  simp only [oldAppendDotComponent, appendMovingPower_whisker, pow_one,
    appendComponent]
  rfl

theorem oldAppendDot_supernatural (i : I) :
    IsSupernatural k (D.parity i) (oldAppendDotComponent D Sc cutoff i) where
  mem s := Submodule.mem_map_of_mem (appendComponent_mem D Sc cutoff
    (by simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1) s.word)
  naturality := by
    rintro s t q f ⟨a, ha, rfl⟩
    have h := congrArg (ideal D Sc cutoff (s.word ++ [i]) (t.word ++ [i])).mkQ
      (appendComponent_naturality D Sc cutoff
        (by simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1) ha)
    rw [map_zsmul, koszulSign_smul (R := k)] at h
    exact h

def inductionDot (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (t : OldCategory D Sc cutoff) :
    BalancedInduction.Obj (append D Sc cutoff i) M.toFunctor t →ₗ[k]
      BalancedInduction.Obj (append D Sc cutoff i) M.toFunctor t :=
  BalancedInduction.transformLinear (oldAppendDot_supernatural D Sc cutoff i) M t

@[simp] theorem inductionDot_tensor (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (s t : OldCategory D Sc cutoff)
    (g : (append D Sc cutoff i).obj s ⟶ t) (b : M.obj s) :
    inductionDot D Sc cutoff i M t
      (BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s g b) =
      BalancedInduction.tensor (append D Sc cutoff i) M.toFunctor s
        (oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g) b :=
  BalancedInduction.transformLinear_tensor _ _ _ _ _ _

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # The signed equal-colour crossing on double old induction

The full-coefficient last crossing defines a supernatural transformation
of the twice-appended old category. Induction is contravariant in this
transformation. Its transport through the existing even induction-composition
isomorphism, with the prescribed extra minus, is the double-induction
crossing used by DeformedMatrixComparison (2), (4). No presentation relation
or matrix inverse is assumed here.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

def equalCrossComponent (i : I) (s : OldCategory D Sc cutoff) :
    ((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s ⟶
      ((append D Sc cutoff i) ⋙ (append D Sc cutoff i)).obj s :=
  (ideal D Sc cutoff _ _).mkQ
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i))

theorem equalCross_supernatural (i : I) :
    IsSupernatural k (D.parity i * D.parity i)
      (F := (append D Sc cutoff i) ⋙ (append D Sc cutoff i))
      (G := (append D Sc cutoff i) ⋙ (append D Sc cutoff i))
      (equalCrossComponent D Sc cutoff i) := by
  apply IsSupernatural.of_twist
  · intro s
    exact Submodule.mem_map_of_mem
      (ELVPScalar.affineUnit_mem D Sc cutoff (crossLast_mem D Sc s.word i i))
  · intro s t f
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff s.word t.word).mkQ_surjective f
    have htw : twist k (D.parity i * D.parity i) (X := s) (Y := t)
        (((ideal D Sc cutoff s.word t.word).mkQ r) : s ⟶ t) =
        ((ideal D Sc cutoff s.word t.word).mkQ (twist k (D.parity i * D.parity i) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r) : s ⟶ t) := by
      rw [twist_apply, oldCategory_proj, oldCategory_proj]
      change (ideal D Sc cutoff s.word t.word).mkQ (proj k 0 r) +
        sign k (D.parity i * D.parity i) • (ideal D Sc cutoff s.word t.word).mkQ (proj k 1 r) =
        (ideal D Sc cutoff s.word t.word).mkQ (twist k (D.parity i * D.parity i) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r)
      rw [twist_apply, map_add, map_smul]
    rw [htw]
    change (ideal D Sc cutoff (s.word ++ [i] ++ [i]) (t.word ++ [i] ++ [i])).mkQ
      (rightContext D Sc cutoff [i] _ _ (rightContext D Sc cutoff [i] _ _ r) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc t.word i i)) =
      (ideal D Sc cutoff (s.word ++ [i] ++ [i]) (t.word ++ [i] ++ [i])).mkQ
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word i i) ≫
          rightContext D Sc cutoff [i] _ _
            (rightContext D Sc cutoff [i] _ _ (twist k (D.parity i * D.parity i) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r)))
    have h := crossLast_comp_rightContext D Sc cutoff i i
      (twist k (D.parity i * D.parity i) (X := obj D Sc cutoff s.word) (Y := obj D Sc cutoff t.word) r)
    rw [twist_twist] at h
    exact congrArg
      (ideal D Sc cutoff (s.word ++ [i] ++ [i]) (t.word ++ [i] ++ [i])).mkQ h.symm

def doubleInductionFunctor (i : I) :
    Superfunctor k (Superfunctor k (OldCategory D Sc cutoff) (SVec k))
      (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  ⟨BalancedInduction.induction (append D Sc cutoff i) ⋙
    BalancedInduction.induction (append D Sc cutoff i)⟩

/-- The canonical even flattening is used in both directions. -/
def equalCrossOnDoubleInduction (i : I)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (doubleInductionFunctor D Sc cutoff i).obj M ⟶
      (doubleInductionFunctor D Sc cutoff i).obj M :=
  (BalancedInduction.inductionComp (k := k) (append D Sc cutoff i) (append D Sc cutoff i)).hom.app M ≫
    BalancedInduction.transformComponent (equalCross_supernatural D Sc cutoff i) M ≫
      (BalancedInduction.inductionComp (k := k) (append D Sc cutoff i) (append D Sc cutoff i)).inv.app M

theorem equalCrossOnDoubleInduction_supernatural (i : I) :
    IsSupernatural k (D.parity i * D.parity i)
      (F := (doubleInductionFunctor D Sc cutoff i).toFunctor)
      (G := (doubleInductionFunctor D Sc cutoff i).toFunctor)
      (equalCrossOnDoubleInduction D Sc cutoff i) := by
  have hL := isSupernatural_of_natTrans
    (BalancedInduction.inductionComp (k := k) (append D Sc cutoff i) (append D Sc cutoff i)).hom
    (fun M => BalancedInduction.inductionComp_hom_mem
      (append D Sc cutoff i) (append D Sc cutoff i) M)
  have hT := BalancedInduction.transformComponent_supernatural
    (equalCross_supernatural D Sc cutoff i)
  have hR := isSupernatural_of_natTrans
    (BalancedInduction.inductionComp (k := k) (append D Sc cutoff i) (append D Sc cutoff i)).inv
    (fun M => BalancedInduction.inductionComp_inv_mem
      (append D Sc cutoff i) (append D Sc cutoff i) M)
  change IsSupernatural k (D.parity i * D.parity i)
    (F := BalancedInduction.induction (append D Sc cutoff i) ⋙
      BalancedInduction.induction (append D Sc cutoff i))
    (G := BalancedInduction.induction (append D Sc cutoff i) ⋙
      BalancedInduction.induction (append D Sc cutoff i))
    (fun M =>
      (BalancedInduction.inductionComp (k := k) (append D Sc cutoff i)
        (append D Sc cutoff i)).hom.app M ≫
        BalancedInduction.transformComponent (equalCross_supernatural D Sc cutoff i) M ≫
          (BalancedInduction.inductionComp (k := k) (append D Sc cutoff i)
            (append D Sc cutoff i)).inv.app M)
  simpa only [zero_add, add_zero, Category.assoc] using hL.comp (hT.comp hR)

/-- The prescribed extra minus is retained, as in the signed action crossing. -/
def signedEqualInductionCross (i : I) :
    doubleInductionFunctor D Sc cutoff i ⟶ doubleInductionFunctor D Sc cutoff i :=
  -Superfunctor.homMk (equalCrossOnDoubleInduction_supernatural D Sc cutoff i).toSuperNatTrans

@[simp] theorem signedEqualInductionCross_app (i : I) (q : ZMod 2)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :
    (signedEqualInductionCross D Sc cutoff i).app q M =
      if q = D.parity i * D.parity i then -equalCrossOnDoubleInduction D Sc cutoff i M else 0 := by
  rw [signedEqualInductionCross, Superfunctor.neg_app]
  change -(if q = D.parity i * D.parity i then equalCrossOnDoubleInduction D Sc cutoff i M else 0) =
    if q = D.parity i * D.parity i then -equalCrossOnDoubleInduction D Sc cutoff i M else 0
  split_ifs <;> simp

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-!
# Full-coefficient append crossing triangularity

The local crossing/output-polynomial separation needed for
`DeformedMackeyBoundary.md` (4)–(5). Every input moving-dot power across
an equal-colour final crossing is a signed old-output-dot crossing plus an
explicit identity output-row polynomial. Arbitrary old input and output
arrows carry the full ELV coefficient algebra; the correction retains the
total-Hom parity twist. The equality projects to the actual append-old
quotient. Canonical castSucc word tails are factored explicitly; global
nonidentity-coordinate assembly, directness, and C0 are not asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The one-dot triangular slide with arbitrary full-coefficient old arrows.
The correction is exactly the identity append row, not an input-tail projection. -/
theorem appendCrossing_dot_triangular (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    rightContext D Sc cutoff [i] _ _ r ≫
        affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ g =
      SKM.zsign k (D.parity i * D.parity i) •
        (rightContext D Sc cutoff [i] _ _ r ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] _ _
            (affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length) ≫ g)) -
      SKM.zsign k (D.parity i * D.parity i) •
        rightContext D Sc cutoff [i] _ _ (r ≫ g) := by
  have hd : rightContext D Sc cutoff [i] (s ++ [i]) (s ++ [i])
      (affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i]) s.length)) =
      affineUnit D Sc cutoff (s ++ [i] ++ [i]) (s ++ [i] ++ [i])
        (dotE D Sc (s ++ [i] ++ [i]) s.length) := by
    apply congrArg (affineUnit D Sc cutoff (s ++ [i] ++ [i]) (s ++ [i] ++ [i]))
    exact dotE_whiskerRight D Sc (s ++ [i]) [i] s.length (by simp)
  rw [rightContext_comp, hd,
    ← Category.assoc (affineUnit D Sc cutoff _ _ _), ← affineUnit_comp,
    lastDotE_comp_crossLast_self, map_sub, map_smul, map_smul, affineUnit_comp, affineUnit_id]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp,
    Linear.comp_smul, Category.assoc, Category.id_comp, rightContext_comp]

/-- Output-polynomial reconstruction on raw full-coefficient Homs. -/
def appendOutputPolynomial (i : I) (v t : List I) :
    (ℕ →₀ hom D Sc cutoff v t) →ₗ[k] hom D Sc cutoff (v ++ [i]) (t ++ [i]) :=
  Finsupp.lsum k fun d =>
    (Linear.rightComp k _ (appendMovingPower D Sc cutoff i t d)).comp
      (rightContext D Sc cutoff [i] v t)

@[simp] theorem appendOutputPolynomial_single (i : I) (v t : List I)
    (d : ℕ) (g : hom D Sc cutoff v t) :
    appendOutputPolynomial D Sc cutoff i v t (Finsupp.single d g) =
      rightContext D Sc cutoff [i] v t g ≫ appendMovingPower D Sc cutoff i t d := by
  simp only [appendOutputPolynomial, Finsupp.lsum_single, LinearMap.comp_apply,
    Linear.rightComp_apply]

/-- Moving powers retain the total parity of the old Hom, including exterior coefficients. -/
theorem appendMovingPower_twisted_rightContext (i : I) (v t : List I) (d : ℕ)
    (g : hom D Sc cutoff v t) :
    appendMovingPower D Sc cutoff i v d ≫ rightContext D Sc cutoff [i] v t g =
      rightContext D Sc cutoff [i] v t (twist k (d • D.parity i) g) ≫
        appendMovingPower D Sc cutoff i t d := by
  rw [appendMovingPower_whisker, appendMovingPower_whisker]
  exact trailing_comp_rightContext D Sc cutoff (firstDot_pow_parity D Sc i [] d) g

/-- Coefficients of the identity-row correction, recursively computed rather than assumed. -/
def appendCrossingCorrection (i : I) (s t : List I) :
    ℕ → hom D Sc cutoff (s ++ [i]) t → (ℕ →₀ hom D Sc cutoff (s ++ [i]) t)
  | 0, _ => 0
  | m + 1, g =>
      SKM.zsign k (D.parity i * D.parity i) •
        appendCrossingCorrection i s t m
          (appendMovingPower D Sc cutoff i s 1 ≫ g) -
      Finsupp.single m (SKM.zsign k (D.parity i * D.parity i) •
        twist k (m • D.parity i) g)

/-- All moving-dot powers across the final equal-colour crossing have an
explicit identity append-row correction over the full ELV coefficient algebra. -/
theorem appendCrossing_power_triangular (i : I) (s t : List I) (m : ℕ)
    (g : hom D Sc cutoff (s ++ [i]) t) :
    appendMovingPower D Sc cutoff i (s ++ [i]) m ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ g =
      SKM.zsign k (D.parity i * D.parity i) ^ m •
        (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s m ≫ g)) +
      appendOutputPolynomial D Sc cutoff i (s ++ [i]) t
        (appendCrossingCorrection D Sc cutoff i s t m g) := by
  induction m generalizing g with
  | zero =>
    simp [appendCrossingCorrection, appendMovingPower, affineUnit_id, End.one_def]
  | succ m ih =>
    have hp (v : List I) : appendMovingPower D Sc cutoff i v (m + 1) =
        appendMovingPower D Sc cutoff i v m ≫ appendMovingPower D Sc cutoff i v 1 := by
      unfold appendMovingPower
      rw [pow_one, pow_succ', End.mul_def, affineUnit_comp]
    have slide : appendMovingPower D Sc cutoff i (s ++ [i]) 1 ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ g =
        SKM.zsign k (D.parity i * D.parity i) •
          (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
            rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s 1 ≫ g)) -
        SKM.zsign k (D.parity i * D.parity i) • rightContext D Sc cutoff [i] _ _ g := by
      simpa only [appendMovingPower, pow_one, List.length_append, List.length_singleton,
        appendRightContext_id, Category.id_comp] using
        appendCrossing_dot_triangular D Sc cutoff i (s ++ [i]) s t (𝟙 _) g
    rw [hp, Category.assoc, slide]
    simp only [Preadditive.comp_sub, Linear.comp_smul]
    rw [ih, appendMovingPower_twisted_rightContext]
    rw [appendCrossingCorrection, map_sub, map_smul, appendOutputPolynomial_single,
      map_smul, Linear.smul_comp, smul_add, smul_smul, hp]
    simp only [Category.assoc]
    rw [pow_succ']
    abel

/-- The same triangular identity with an arbitrary full-coefficient old input arrow. -/
theorem appendCrossing_power_triangular_comp (i : I) (v s t : List I) (m : ℕ)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    rightContext D Sc cutoff [i] _ _ r ≫
        appendMovingPower D Sc cutoff i (s ++ [i]) m ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ g =
      SKM.zsign k (D.parity i * D.parity i) ^ m •
        (rightContext D Sc cutoff [i] _ _ r ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s m ≫ g)) +
      rightContext D Sc cutoff [i] _ _ r ≫
        appendOutputPolynomial D Sc cutoff i (s ++ [i]) t
          (appendCrossingCorrection D Sc cutoff i s t m g) := by
  rw [appendCrossing_power_triangular, Preadditive.comp_add, Linear.comp_smul]

/-- Projection to the actual append-old quotient preserves the explicit correction.
No quotient by the crossing span, or splitting of that span, is assumed. -/
theorem appendProjection_crossing_power_triangular (i : I) (v s t : List I) (m : ℕ)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendProjection D Sc cutoff i v (t ++ [i])
      (rightContext D Sc cutoff [i] _ _ r ≫
        appendMovingPower D Sc cutoff i (s ++ [i]) m ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ g) =
      SKM.zsign k (D.parity i * D.parity i) ^ m •
        appendProjection D Sc cutoff i v (t ++ [i])
          (rightContext D Sc cutoff [i] _ _ r ≫
            affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
            rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s m ≫ g)) +
      appendProjection D Sc cutoff i v (t ++ [i])
        (rightContext D Sc cutoff [i] _ _ r ≫
          appendOutputPolynomial D Sc cutoff i (s ++ [i]) t
            (appendCrossingCorrection D Sc cutoff i s t m g)) := by
  rw [appendCrossing_power_triangular_comp, map_add, map_smul]

/-- Every correction coefficient remains in the identity output row after an old prefix. -/
theorem appendOutputPolynomial_precomp (i : I) (v s t : List I)
    (r : hom D Sc cutoff v s) (f : ℕ →₀ hom D Sc cutoff s t) :
    rightContext D Sc cutoff [i] _ _ r ≫ appendOutputPolynomial D Sc cutoff i s t f =
      appendOutputPolynomial D Sc cutoff i v t
        (Finsupp.lsum k (fun d => (Finsupp.lsingle d).comp (Linear.leftComp k _ r)) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Preadditive.comp_add, hf, hg]
  | single d g =>
    simp only [Finsupp.lsum_single, LinearMap.comp_apply, Linear.leftComp_apply,
      Finsupp.lsingle_apply, appendOutputPolynomial_single, rightContext_comp, Category.assoc]

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Output polynomials and the append crossing dot defect

The output maps in `DeformedMackeyBoundary.md` (4) and the local dot identity
preceding (8), over the full ELV old quotient. These use postcomposition by
the output moving dot, not the input moving-dot operator. The crossing
formula retains total old-Hom parity, including exterior coefficients.
This module does not assert the global corrected polynomial projection.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Output polynomial reconstruction with coefficients in the old quotient. -/
def appendOutputEmbedding (i : I) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] AppendTarget D Sc cutoff i v (t ++ [i]) :=
  Finsupp.lsum k fun m => appendPair D Sc cutoff 0 i
    (appendMovingPower D Sc cutoff i t m)

@[simp] theorem appendOutputEmbedding_single (i : I) (v t : List I)
    (m : ℕ) (g : hom D Sc cutoff v t) :
    appendOutputEmbedding D Sc cutoff i v t
      (Finsupp.single m ((ideal D Sc cutoff v t).mkQ g)) =
    appendProjection D Sc cutoff i v (t ++ [i])
      (rightContext D Sc cutoff [i] v t g ≫ appendMovingPower D Sc cutoff i t m) := by
  simp only [appendOutputEmbedding, Finsupp.lsum_single, appendPair_mk, twist_zero]

/-- The prescribed output polynomial map descends coefficientwise. -/
theorem appendOutputEmbedding_map (i : I) (v t : List I)
    (f : ℕ →₀ hom D Sc cutoff v t) :
    appendOutputEmbedding D Sc cutoff i v t
      (Finsupp.mapRange.linearMap (ideal D Sc cutoff v t).mkQ f) =
    appendProjection D Sc cutoff i v (t ++ [i]) (appendOutputPolynomial D Sc cutoff i v t f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m g =>
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      appendOutputEmbedding_single, appendOutputPolynomial_single]

private theorem append_postcomp_relations (i : I) (v w z : List I)
    (a : hom D Sc cutoff w z) :
    appendRelations D Sc cutoff i v w ≤
      (appendRelations D Sc cutoff i v z).comap (Linear.rightComp k _ a) := by
  intro h hh
  exact appendRelations_comp D Sc cutoff i hh a

/-- Output postcomposition preserves all append-old relations. -/
def appendOutputDot (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) →ₗ[k]
      AppendTarget D Sc cutoff i v (t ++ [i]) :=
  (appendRelations D Sc cutoff i v (t ++ [i])).mapQ
    (appendRelations D Sc cutoff i v (t ++ [i]))
    (Linear.rightComp k _ (appendMovingPower D Sc cutoff i t 1))
    (append_postcomp_relations D Sc cutoff i v _ _ _)

@[simp] theorem appendOutputDot_projection (i : I) (v t : List I)
    (h : hom D Sc cutoff (v ++ [i]) (t ++ [i])) :
    appendOutputDot D Sc cutoff i v t (appendProjection D Sc cutoff i v (t ++ [i]) h) =
      appendProjection D Sc cutoff i v (t ++ [i])
        (h ≫ appendMovingPower D Sc cutoff i t 1) := rfl

/-- Exponent translation on output coefficients. -/
def appendOutputShift (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.lsum k fun m => Finsupp.lsingle (m + 1)

/-- The output polynomial map intertwines the specified output dot. -/
theorem appendOutputDot_embedding (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    appendOutputDot D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) =
      appendOutputEmbedding D Sc cutoff i v t (appendOutputShift D Sc cutoff v t f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    rw [appendOutputEmbedding_single, appendOutputDot_projection]
    simp only [appendOutputShift, Finsupp.lsum_single, Finsupp.lsingle_apply,
      appendOutputEmbedding_single]
    congr 1
    rw [Category.assoc]
    congr 1
    unfold appendMovingPower
    rw [pow_one, ← affineUnit_comp]
    congr 1
    exact (pow_succ' (dotE D Sc (t ++ [i]) t.length) m).symm

/-- The crossing generator with arbitrary old input and output arrows. -/
def appendCrossingClass (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    AppendTarget D Sc cutoff i v (t ++ [i]) :=
  appendProjection D Sc cutoff i v (t ++ [i])
    (rightContext D Sc cutoff [i] _ _ r ≫ affineUnit D Sc cutoff _ _
      (crossLast D Sc s i i) ≫ rightContext D Sc cutoff [i] _ _ g)

/-- Crossing followed by the output moving dot, before the old quotient. -/
theorem appendCrossing_output_dot (i : I) (s : List I) :
    affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        appendMovingPower D Sc cutoff i (s ++ [i]) 1 =
      SKM.zsign k (D.parity i * D.parity i) •
        (rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s 1) ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i)) -
      SKM.zsign k (D.parity i * D.parity i) • 𝟙 _ := by
  have hd : rightContext D Sc cutoff [i] _ _ (appendMovingPower D Sc cutoff i s 1) =
      affineUnit D Sc cutoff _ _ (dotE D Sc (s ++ [i] ++ [i]) s.length) := by
    simp only [appendMovingPower, pow_one, rightContext_affineUnit]
    congr 1
    exact dotE_whiskerRight D Sc (s ++ [i]) [i] s.length (by simp)
  rw [hd, ← affineUnit_comp, dotE_comp_crossLast_self, map_add, map_smul,
    affineUnit_comp, affineUnit_id, smul_add, zsign_smul_zsign_smul,
    add_sub_cancel_right]
  simp only [appendMovingPower, pow_one, List.length_append, List.length_singleton]

/-- The full-coefficient output-dot defect on every crossing generator.
For odd moving colour the constant term has positive sign. -/
theorem appendOutputDot_crossingClass (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendOutputDot D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g) =
      SKM.zsign k (D.parity i * D.parity i) •
        appendCrossingClass D Sc cutoff i v s t
          (r ≫ appendMovingPower D Sc cutoff i s 1) (twist k (D.parity i) g) -
      SKM.zsign k (D.parity i * D.parity i) •
        appendOutputEmbedding D Sc cutoff i v t
          (Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (r ≫ twist k (D.parity i) g))) := by
  have ht := appendMovingPower_twisted_rightContext D Sc cutoff i (s ++ [i]) t 1
    (twist k (D.parity i) g)
  simp only [one_smul, twist_twist] at ht
  simp only [appendCrossingClass, appendOutputDot_projection, Category.assoc]
  rw [← ht, ← Category.assoc (affineUnit D Sc cutoff _ _ _), appendCrossing_output_dot]
  simp only [Preadditive.sub_comp, Preadditive.comp_sub, Linear.smul_comp,
    Linear.comp_smul, Category.assoc, Category.id_comp, ← rightContext_comp,
    map_sub, map_smul, appendOutputEmbedding_single, appendMovingPower,
    pow_zero, End.one_def, affineUnit_id, Category.comp_id]
  simp only [rightContext_comp, Category.assoc]

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# The append Mackey map on a cyclotomic content corner

This instantiates the source coefficient module of `AppendMackeySource.md` §4 and
restricts the map to the left append idempotent, as required by
`DeformedMackeyBoundary.md` (1). The cyclotomic annihilation and constant-parity
conditions are proved for the content corner, not supplied as hypotheses.
The unchanged right coefficient action satisfies the source transport field `P_r`.
These are ordinary cyclotomic polynomial coefficients; no exterior deformation is asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Categorification.InductionAlong Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
open SKM (zsign)
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I) (i : I)

/-- The parity of the moving cyclotomic crossing on content `β`. -/
def appendContentParity : ZMod 2 :=
  (a i).natDegree • D.parity i + D.parity i * (β.map D.parity).sum

omit [Fintype I] in
/-- The corrected source-dot sign depends only on content, not on the cutoff. -/
@[simp] theorem appendSourceSign_contentParity :
    appendSourceSign D a i (appendContentParity D a β i) =
      D.parity i * (β.map D.parity).sum := by
  simp [appendSourceSign, appendContentParity]

local notation "B" => CyclotomicContentCorner D Sc a n β
local notation "eps" => appendContentParity D a β i
local notation "ψ" =>
  (appendAlgebra D Sc i (n + 1) : Hn D Sc (n + 1) →ₙ+* Hn D Sc (n + 1 + 1))
local notation "L" => Ind B (prependTwist D Sc i n eps)

/-- The left append-idempotent part of twisted prepend induction. -/
def appendContentSource : AddSubgroup L where
  carrier := {z | (ψ 1 : Hn D Sc (n + 1 + 1)) • z = z}
  zero_mem' := smul_zero _
  add_mem' hz hw := (smul_add _ _ _).trans (congrArg₂ (· + ·) hz hw)
  neg_mem' hz := (smul_neg _ _).trans (congrArg Neg.neg hz)

variable (ha : CyclotomicPolynomialParity D a)

end OddMath.QuiverHecke
end

end

section

/-!
# Moving-shuffle extraction on the append content source

The source decomposition needed for `DeformedMackeyBoundary.md` (2) and (7),
in the ordinary cyclotomic polynomial setting. Coordinates are the proved
balanced prepend PBW coordinates, not an inverse chosen by dimension counting.
The full moving shuffle lands in the append corner at every old height.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Categorification.InductionAlong
open Categorification.TypeA Equiv
open scoped Classical
namespace OddMath.QuiverHecke

private theorem rotate_inv_block_inr (r : ℕ) (y : Fin r) :
    (finRotate (r + 1))⁻¹
        (blockEquiv (Nat.add_comm 1 r) (Sum.inr y)) = y.castSucc := by
  change (finRotate (r + 1)).symm _ = _
  apply (finRotate (r + 1)).symm_apply_eq.mpr
  change _ = (finRotate (r + 1)) ⟨y.val, by omega⟩
  rw [finRotate_of_lt y.isLt]
  apply Fin.ext
  change 1 + y.val = y.val + 1
  omega

/-- The inverse shuffle moves the first strand to the last position. -/
def longPrependShuffle (r : ℕ) : PrependShuffle r :=
  ⟨finRotate (r + 1), by
    constructor
    · intro x y hxy
      have hx := x.isLt
      have hy := y.isLt
      change x.val < y.val at hxy
      omega
    · intro x y hxy
      dsimp only
      rw [rotate_inv_block_inr, rotate_inv_block_inr]
      exact hxy⟩

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

omit [Fintype I] in
/-- The full moving shuffle has exactly the append target word. -/
theorem prependShuffleTarget_long (i : I) {r : ℕ} (s : Word I r) :
    prependShuffleTarget i (longPrependShuffle r) s = appendWord i s := by
  apply Subtype.ext
  change tgt (i :: s.1) (cw (canWord (r + 1) (finRotate (r + 1))⁻¹)) = s.1 ++ [i]
  refine List.ext_getElem (by simp [s.2]) ?_
  intro p hp₁ hp₂
  have hp : p < r + 1 := by simpa [s.2] using hp₁
  have hq := tgt_cw_getElem
    (validWord_canWord (r + 1) (finRotate (r + 1))⁻¹)
    (t := i :: s.1) (by simp [s.2]) ⟨p, hp⟩
  simp only [wordProd_canWord, inv_inv] at hq
  rw [hq]
  by_cases hpr : p < r
  · simp only [finRotate_of_lt hpr, List.getElem_cons_succ]
    rw [List.getElem_append_left (by simpa [s.2] using hpr)]
  · have he : p = r := by omega
    subst p
    simp only [finRotate_last', List.getElem_cons_zero]
    rw [List.getElem_append_right (by simp [s.2])]
    simp [s.2]

/-- The append projector fixes the moving crossing matrix. -/
theorem appendOne_mul_longPrependShuffleElement (i : I) (r : ℕ) :
    appendAlgebra D Sc i r 1 * prependShuffleElement D Sc i (longPrependShuffle r) =
      prependShuffleElement D Sc i (longPrependShuffle r) := by
  have hs (s : Word I r) (t : Word I (r + 1)) (ht : t = appendWord i s)
      (f : wordObj D Sc (prependWord i s) ⟶ wordObj D Sc t) :
      appendAlgebra D Sc i r 1 * FiniteHomMatrix.single t (prependWord i s) f =
        FiniteHomMatrix.single t (prependWord i s) f := by
    subst t
    exact appendOne_mul_single D Sc i s (prependWord i s) f
  rw [prependShuffleElement, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => hs s _ (prependShuffleTarget_long i s) _

/-- All first-dot powers of the moving shuffle remain in the append corner. -/
theorem appendOne_mul_longPrependPBWTerm (i : I) (r m : ℕ) (b : Hn D Sc r) :
    appendAlgebra D Sc i r 1 * prependPBWTerm D Sc i (longPrependShuffle r) m b =
      prependPBWTerm D Sc i (longPrependShuffle r) m b := by
  simp only [prependPBWTerm, ← mul_assoc, appendOne_mul_longPrependShuffleElement]

variable (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I) (i : I)
local notation "B" => CyclotomicContentCorner D Sc a n β
local notation "eps" => appendContentParity D a β i
local notation "C" => (PrependShuffle (n + 1) × ℕ) →₀ B
local notation "L" => Ind B (prependTwist D Sc i n eps)
local notation "coord" => prependTwistCoordinates D Sc i n eps B

/-- Read the full moving-shuffle row of the balanced PBW coordinates.
These are input-first-dot coordinates, before the corrected-ρ sign normalization. -/
def appendContentLongExtract : appendContentSource D Sc a n β i →+ (ℕ →₀ B) :=
  (Finsupp.comapDomain.addMonoidHom
    (f := fun m : ℕ => (longPrependShuffle (n + 1), m))
    (fun _ _ h => congrArg Prod.snd h)).comp
      ((coord).symm.toAddMonoidHom.comp (appendContentSource D Sc a n β i).subtype)

/-- Extraction is the literal long-shuffle coefficient. -/
theorem appendContentLongExtract_apply (z : appendContentSource D Sc a n β i) (m : ℕ) :
    appendContentLongExtract D Sc a n β i z m =
      (coord).symm z.1 (longPrependShuffle (n + 1), m) := rfl

/-- A moving PBW tensor satisfies the left append projector without any cutoff assumption. -/
theorem appendContentLong_mem (m : ℕ) (b : B) :
    coord (Finsupp.single (longPrependShuffle (n + 1), m) b) ∈
      appendContentSource D Sc a n β i := by
  change appendAlgebra D Sc i (n + 1) 1 • _ = _
  rw [prependTwistCoordinates_single, Ind.smul_tmul]
  congr 1
  apply Subtype.ext
  exact appendOne_mul_longPrependPBWTerm D Sc i (n + 1) m 1

/-- The prescribed moving crossing followed by input-first-dot powers. -/
def appendContentLongLift : (ℕ →₀ B) →+ appendContentSource D Sc a n β i :=
  Finsupp.liftAddHom fun m =>
    { toFun := fun b => ⟨coord (Finsupp.single (longPrependShuffle (n + 1), m) b),
        appendContentLong_mem D Sc a n β i m b⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun b c => Subtype.ext (by simp) }

/-- On each monomial the lift is the specified PBW tensor, not an arbitrary section. -/
theorem appendContentLongLift_single (m : ℕ) (b : B) :
    (appendContentLongLift D Sc a n β i (Finsupp.single m b)).1 =
      coord (Finsupp.single (longPrependShuffle (n + 1), m) b) := by
  exact congrArg Subtype.val (Finsupp.liftAddHom_apply_single _ m b)

/-- All long-shuffle coefficients are recovered, over the cyclotomic content ring. -/
theorem appendContentLongExtract_lift (f : ℕ →₀ B) :
    appendContentLongExtract D Sc a n β i (appendContentLongLift D Sc a n β i f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    ext l
    rw [appendContentLongExtract_apply, appendContentLongLift_single,
      AddEquiv.symm_apply_apply]
    simp [Finsupp.single_apply]

end OddMath.QuiverHecke
end

end

section

/-!
# Canonical short prepend words

The short-shuffle step of `DeformedMackeyBoundary.md` (4): the literal canonical
word of a non-long prepend shuffle omits the last crossing. This is a statement
about the chosen code word, not just its permutation or braid class. It permits
right whiskering of the moving diagram without equal-colour braid corrections.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA Equiv MonoidalCategory
namespace OddMath.QuiverHecke

/-- Fixing the last position makes the top run of the chosen code empty. -/
theorem canWord_eq_short_codeWord (n : ℕ) (w : Perm (Fin (n + 2)))
    (hw : w (Fin.last (n + 1)) = Fin.last (n + 1)) :
    ∃ c : List ℕ, IsCode c ∧ c.length = n ∧ canWord (n + 2) w = codeWord c := by
  have hc := isCode_code (n + 2) w
  have hl := length_code (n + 2) w
  have hp := wordProd_canWord (n + 2) w
  unfold canWord at hp ⊢
  cases he : code (n + 2) w with
  | nil => simp [he] at hl
  | cons b c =>
    rw [he] at hc hl hp
    have hcl : c.length = n := by simp only [List.length_cons] at hl; omega
    have hb := (isCode_cons.mp hc).1
    have ht := wordProd_codeWord_cons_apply (m := n + 2) hb (by omega)
    rw [hp] at ht
    have heq : (⟨c.length + 1, by omega⟩ : Fin (n + 2)) = Fin.last (n + 1) :=
      Fin.ext (by simp [hcl])
    rw [heq, ← hw] at ht
    have hbn : b = n + 1 := congrArg Fin.val (w.injective ht)
    subst b
    refine ⟨c, (isCode_cons.mp hc).2, hcl, ?_⟩
    simp only [codeWord_cons, hcl, Nat.sub_self, descRun_zero, List.append_nil]

/-- The only prepend shuffle whose inverse does not fix the last position is the long one. -/
theorem prependShuffle_inv_last_of_ne_long (n : ℕ) (u : PrependShuffle (n + 1))
    (hu : u ≠ longPrependShuffle (n + 1)) :
    u.1⁻¹ (Fin.last (n + 1)) = Fin.last (n + 1) := by
  by_contra hlast
  have hmono : StrictMono (fun x : Fin (n + 1) => u.1⁻¹ x.succ) := by
    intro x y hxy
    have he (z : Fin (n + 1)) :
        blockEquiv (Nat.add_comm 1 (n + 1)) (Sum.inr z) = z.succ := by
      apply Fin.ext
      simp [blockEquiv_inr_val, Nat.add_comm]
    simpa only [he] using u.2.2 hxy
  have hbound (x : Fin (n + 1)) : (u.1⁻¹ x.succ).val < n + 1 := by
    have hm := hmono.monotone (Fin.le_last x)
    have ht := (u.1⁻¹ (Fin.last (n + 1))).isLt
    have hn : (u.1⁻¹ (Fin.last (n + 1))).val ≠ n + 1 := by
      intro h; exact hlast (Fin.ext h)
    change (u.1⁻¹ x.succ).val ≤ (u.1⁻¹ (Fin.last (n + 1))).val at hm
    omega
  let f : Fin (n + 1) → Fin (n + 1) := fun x => ⟨(u.1⁻¹ x.succ).val, hbound x⟩
  have hf : StrictMono f := fun x y hxy => hmono hxy
  have hx (x : Fin (n + 1)) : u.1⁻¹ x.succ = x.castSucc := by
    apply Fin.ext
    exact congrArg (fun z : Fin (n + 1) => z.val) (hf.apply_eq (x := x))
  apply hu
  apply Subtype.ext
  apply inv_injective
  apply Equiv.ext
  intro x
  refine Fin.cases ?_ (fun y => ?_) x
  · have hz : u.1⁻¹ 0 = Fin.last (n + 1) := by
      by_contra h
      have hlt : (u.1⁻¹ 0).val < n + 1 := by
        have := (u.1⁻¹ 0).isLt
        have hn : (u.1⁻¹ 0).val ≠ n + 1 := fun he => h (Fin.ext he)
        omega
      let y : Fin (n + 1) := ⟨(u.1⁻¹ 0).val, hlt⟩
      have hy : u.1⁻¹ y.succ = u.1⁻¹ 0 := (hx y).trans (Fin.ext rfl)
      have he := congrArg Fin.val (u.1⁻¹.injective hy)
      simp at he
    rw [hz]
    change Fin.last (n + 1) = (finRotate (n + 1 + 1)).symm 0
    exact ((finRotate (n + 1 + 1)).symm_apply_eq.mpr (finRotate_last').symm).symm
  · rw [hx]
    change y.castSucc = (finRotate (n + 1 + 1)).symm y.succ
    apply (finRotate (n + 1 + 1)).eq_symm_apply.mpr
    apply Fin.ext
    simp

/-- Shortness bounds the literal canonical crossings, so none meets the final strand. -/
theorem canWord_prependShort_lt (n : ℕ) (u : PrependShuffle (n + 1))
    (hu : u ≠ longPrependShuffle (n + 1)) :
    ∀ x ∈ canWord (n + 2) u.1⁻¹, x < n := by
  obtain ⟨c, -, hl, he⟩ := canWord_eq_short_codeWord n u.1⁻¹
    (prependShuffle_inv_last_of_ne_long n u hu)
  rw [he]
  intro x hx
  simpa only [hl] using lt_of_mem_codeWord hx

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

end OddMath.QuiverHecke
end

end

section

/-!
# Corrected-rho coordinates of the moving source coset

The ordinary-polynomial specialization of `DeformedMackeyBoundary.md` (6)–(7).
The prescribed full moving shuffle is normalized by the content sign in each
input-dot degree. This supplies compatible lifts for the source of the Mackey
boundary, without assuming an identification of the short image with crossings.
The content corner has old height `n + 1`; `n = 0` is not old height zero.
No restriction on the cyclotomic cutoff is imposed.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification Categorification.InductionAlong Supercategory
open scoped Classical
namespace OddMath.QuiverHecke
open SKM (zsign)

/-- Degreewise sign normalization, leaving the right coefficient in its original order. -/
def movingSignNormalize {M : Type*} [AddCommGroup M] (p : ZMod 2) :
    (ℕ →₀ M) →+ (ℕ →₀ M) where
  toFun f := Finsupp.onFinset f.support (fun m => (zsign ℤ p) ^ m • f m)
    (fun m h => Finsupp.mem_support_iff.mpr (fun hz => h (by rw [hz, smul_zero])))
  map_zero' := by ext m; simp
  map_add' f g := by ext m; simp [smul_add]

@[simp] theorem movingSignNormalize_apply {M : Type*} [AddCommGroup M]
    (p : ZMod 2) (f : ℕ →₀ M) (m : ℕ) :
    movingSignNormalize p f m = (zsign ℤ p) ^ m • f m := rfl

@[simp] theorem movingSignNormalize_single {M : Type*} [AddCommGroup M]
    (p : ZMod 2) (m : ℕ) (b : M) :
    movingSignNormalize p (Finsupp.single m b) =
      Finsupp.single m ((zsign ℤ p) ^ m • b) := by
  ext l
  by_cases h : m = l
  · subst l; simp
  · simp [h]

/-- The sign correction is its own inverse, including degree zero. -/
@[simp] theorem movingSignNormalize_twice {M : Type*} [AddCommGroup M]
    (p : ZMod 2) (f : ℕ →₀ M) :
    movingSignNormalize p (movingSignNormalize p f) = f := by
  ext m
  simp only [movingSignNormalize_apply, smul_smul, ← mul_pow,
    ← zsign_add_eq, CharTwo.add_self_eq_zero]
  simp [zsign]

/-- Degree raising with the coefficient parity retained. -/
def movingParityRaise {M : Type*} [AddCommGroup M] (θ : M →+ M) :
    (ℕ →₀ M) →+ (ℕ →₀ M) :=
  (Finsupp.embDomain.addMonoidHom ⟨Nat.succ, Nat.succ_injective⟩).comp
    (Finsupp.mapRange.addMonoidHom θ)

@[simp] theorem movingParityRaise_single {M : Type*} [AddCommGroup M]
    (θ : M →+ M) (m : ℕ) (b : M) :
    movingParityRaise θ (Finsupp.single m b) = Finsupp.single (m + 1) (θ b) := by
  simp [movingParityRaise]

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

variable (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I) (i : I)
local notation "B" => CyclotomicContentCorner D Sc a n β
local notation "eps" => appendContentParity D a β i
local notation "p" => D.parity i * Multiset.sum (Multiset.map D.parity β)
local notation "coord" => prependTwistCoordinates D Sc i n eps B

/-- The normalized lift is the full moving PBW lift with its exact degreewise sign. -/
def appendContentRhoLift : (ℕ →₀ B) →+ appendContentSource D Sc a n β i :=
  (appendContentLongLift D Sc a n β i).comp (movingSignNormalize p)

/-- Extraction in the corrected-rho normalization. -/
def appendContentRhoExtract : appendContentSource D Sc a n β i →+ (ℕ →₀ B) :=
  (movingSignNormalize p).comp (appendContentLongExtract D Sc a n β i)

@[simp] theorem appendContentRhoLift_single (m : ℕ) (b : B) :
    (appendContentRhoLift D Sc a n β i (Finsupp.single m b)).1 =
      coord (Finsupp.single (longPrependShuffle (n + 1), m) ((zsign ℤ p) ^ m • b)) := by
  simp only [appendContentRhoLift, AddMonoidHom.comp_apply, movingSignNormalize_single,
    appendContentLongLift_single]

@[simp] theorem appendContentRhoExtract_lift (f : ℕ →₀ B) :
    appendContentRhoExtract D Sc a n β i (appendContentRhoLift D Sc a n β i f) = f := by
  simp [appendContentRhoExtract, appendContentRhoLift, appendContentLongExtract_lift]

variable (ha : CyclotomicPolynomialParity D a)
local notation "θ" => RingHom.toAddMonoidHom (contentCornerParity D Sc a n β i ha)

/-- The parity raising operator has zero constant term. -/
@[simp] theorem movingParityRaise_zero {M : Type*} [AddCommGroup M]
    (τ : M →+ M) (f : ℕ →₀ M) : movingParityRaise τ f 0 = 0 := by
  exact Finsupp.embDomain_of_notMem_range _ _ _ (by simp)

/-- Its successor coefficient is exactly the parity of the previous coefficient. -/
@[simp] theorem movingParityRaise_succ {M : Type*} [AddCommGroup M]
    (τ : M →+ M) (f : ℕ →₀ M) (m : ℕ) :
    movingParityRaise τ f (m + 1) = τ (f m) :=
  Finsupp.embDomain_apply_self _ _ m

end OddMath.QuiverHecke
end

end

section

/-!
# Moving-chain tensors and their prepend coordinates

The source lift needed for the longest-coset calculation in
`DeformedBoundaryDivision.md` (6). The chain is the prescribed `contentMove`;
its tensor belongs to the existing append content source. Extraction retains
both the twisted old coefficient and corrected-rho degree sign.

The filtration lemmas discard lower-crossing terms in the full moving row.
The canonical word is identified literally, without an unspecified braid unit.
Evaluation of the chain's leading polynomial and its total sign remains open.
-/
noncomputable section
open CategoryTheory StringDiagrams Categorification Categorification.InductionAlong
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]

variable (a : I → _root_.Polynomial k) (n : ℕ) (β : Multiset I) (i : I)
local notation "B" => CyclotomicContentCorner D Sc a n β
local notation "eps" => appendContentParity D a β i

end OddMath.QuiverHecke

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Lower-crossing diagrams are spanned by lower-length prepend basis elements. -/
theorem low_le_span_prepend (i : I) (s t : List I) (N : ℕ) :
    Low D Sc (i :: s) t N ≤
      Submodule.span k (prependElt D Sc ''
        {x : PrependIdx i s t | length (s.length + 1) x.perm < N}) := by
  let S := Submodule.span k (prependElt D Sc ''
    {x : PrependIdx i s t | length (s.length + 1) x.perm < N})
  have he : ∀ d, ∀ y : NFIdx (i :: s) t,
      length (s.length + 1) y.1.2 = d → d < N → basisNF D Sc (i :: s) t y ∈ S := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro y hy hd
      obtain ⟨c, hc, hm⟩ := exists_unit_prependElt D Sc y
      have hlow : Submodule.span k
          (basisNF D Sc (i :: s) t ''
            {z | length (s.length + 1) z.1.2 < length (s.length + 1) y.1.2}) ≤ S := by
        apply Submodule.span_le.mpr
        rintro _ ⟨z, hz, rfl⟩
        exact ih _ (hy ▸ hz) z rfl (lt_trans (hy ▸ hz) hd)
      have hp : length (s.length + 1) (PrependIdx.leadEquiv.symm y).perm < N := by
        have h := congrArg (fun z : NFIdx (i :: s) t => z.1.2)
          (PrependIdx.leadEquiv.apply_symm_apply y)
        change (PrependIdx.leadEquiv.symm y).perm = y.1.2 at h
        rw [h, hy]
        exact hd
      have hb : prependElt D Sc (PrependIdx.leadEquiv.symm y) ∈ S :=
        Submodule.subset_span ⟨_, hp, rfl⟩
      obtain ⟨u, hu⟩ := hc
      have hEq : basisNF D Sc (i :: s) t y = (↑u⁻¹ : k) •
          (prependElt D Sc (PrependIdx.leadEquiv.symm y) -
            (prependElt D Sc (PrependIdx.leadEquiv.symm y) - c • basisNF D Sc (i :: s) t y)) := by
        rw [sub_sub_cancel, smul_smul, ← hu, Units.inv_mul, one_smul]
      rw [hEq]
      exact S.smul_mem _ (S.sub_mem hb (hlow hm))
  refine (low_le_span_nf D Sc (i :: s) t N).trans (Submodule.span_le.mpr ?_)
  rintro _ ⟨y, hy, rfl⟩
  exact he _ y rfl hy

/-- Prepend coordinates of length at least the filtration bound vanish. -/
theorem prependBasis_repr_eq_zero_of_low (i : I) (s t : List I) (N : ℕ)
    (h : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t))
    (hh : h ∈ Low D Sc (i :: s) t N) (x : PrependIdx i s t)
    (hx : N ≤ length (s.length + 1) x.perm) :
    (prependBasis D Sc).repr h x = 0 := by
  apply repr_eq_zero_of_mem_span_image (prependBasis D Sc)
    (S := {x : PrependIdx i s t | length (s.length + 1) x.perm < N})
  · simpa only [prependBasis_apply] using low_le_span_prepend D Sc i s t N hh
  · exact not_lt.mpr hx
end OddMath.QuiverHecke

noncomputable section
open Categorification.TypeA Equiv
namespace OddMath.QuiverHecke

/-- The ascending full run is the cyclic rotation. -/
theorem runPerm_zero_eq_rotate (r : ℕ) : runPerm r 0 = finRotate (r + 1) := by
  ext x
  rw [runPerm_val r 0 (Nat.zero_le _)]
  by_cases hx : x.val < r
  · rw [finRotate_of_lt hx]
    simp [hx]
  · have he : x = Fin.last r := Fin.ext (by simp only [Fin.val_last]; omega)
    subst x
    simp

/-- The canonical long word is literally the descending run. -/
theorem canWord_longPrependShuffle (r : ℕ) :
    canWord (r + 1) (longPrependShuffle r).1⁻¹ = descRun 0 r := by
  have he : wordProd (r + 1) (descRun 0 r) = (finRotate (r + 1))⁻¹ := by
    rw [descRun, wordProd_reverse, ← runPerm_zero_eq_rotate]
    rfl
  change canWord (r + 1) (finRotate (r + 1))⁻¹ = _
  rw [← he]
  cases r with
  | zero =>
    apply List.length_eq_zero_iff.mp
    rw [descRun_zero, wordProd, List.map_nil, List.prod_nil,
      length_canWord, Categorification.TypeA.length_one]
  | succ r =>
    have hc : IsCode (0 :: idCode r) := ⟨by simp, isCode_idCode r⟩
    have hw : codeWord (0 :: idCode r) = descRun 0 (r + 1) := by simp [codeWord_cons]
    rw [← hw, canWord_wordProd_codeWord hc (by simp)]

/-- The full moving shuffle has one crossing per old strand. -/
theorem length_longPrependShuffle (r : ℕ) :
    length (r + 1) (longPrependShuffle r).1 = r := by
  rw [← length_inv, ← length_canWord, canWord_longPrependShuffle, length_descRun]

end OddMath.QuiverHecke
namespace OddMath.QuiverHecke

/-- Source crossing substitution at even colour: `τ = -T`. This is a
local polynomial identity, not an assertion about descended extraction. -/
theorem movingEven_sourceCrossing {R : Type*} [Ring R] (u v T : R) :
    SignedNilHecke.gEven u v T = (v - u) * (1 - (v - u) * (-T)) := by
  unfold SignedNilHecke.gEven SignedNilHecke.phiEven
  noncomm_ring

/-- Source crossing substitution at odd colour: `τ = T`. -/
theorem movingOdd_sourceCrossing {R : Type*} [Ring R] (u v T : R) :
    OddNilHecke.Intertwiner.element u v T =
      (v ^ 2 - u ^ 2) * ((v - u) - (v ^ 2 - u ^ 2) * T) := by
  unfold OddNilHecke.Intertwiner.element OddNilHecke.Intertwiner.squareDiff
  noncomm_ring

/-- Library even crossing coefficient, obtained from the source comparison. -/
theorem movingEven_crossingCoefficient {R : Type*} [Ring R] (u v T : R) :
    SignedNilHecke.gEven u v T = (v - u) + (v - u) ^ 2 * T := by
  rw [movingEven_sourceCrossing]
  noncomm_ring

/-- Library odd crossing coefficient, obtained from the source comparison. -/
theorem movingOdd_crossingCoefficient {R : Type*} [Ring R] (u v T : R) :
    OddNilHecke.Intertwiner.element u v T =
      (v ^ 2 - u ^ 2) * (v - u) - (v ^ 2 - u ^ 2) ^ 2 * T := by
  rw [movingOdd_sourceCrossing]
  noncomm_ring

open CategoryTheory StringDiagrams Categorification.TypeA
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Every lower-crossing error has zero full moving-shuffle coordinate,
including coordinates with nontrivial old permutations. -/
theorem prependBasis_long_repr_eq_zero_of_low (i : I) (s t : List I)
    (h : (pres D Sc).obj (ob D (i :: s)) ⟶ (pres D Sc).obj (ob D t))
    (hh : h ∈ Low D Sc (i :: s) t s.length) (x : PrependIdx i s t)
    (hx : x.1.2.2.2 = longPrependShuffle s.length) :
    (prependBasis D Sc).repr h x = 0 := by
  apply prependBasis_repr_eq_zero_of_low D Sc i s t s.length h hh x
  rw [PrependIdx.perm, length_prependPermutation]
  simp only [hx, length_longPrependShuffle]
  omega
end OddMath.QuiverHecke
end
end
end

end

section

/-!
# Corrected polynomial projection and splitting of the full ELV append target

The explicit coordinate candidate uses the all-power crossing correction on
each nonidentity input tail. After recovery on the actual output embedding and
annihilation of the entire crossing image are proved, it is exported as
`appendC0`. Its kernel is exactly the crossing span. The resulting splitting
has augmented inverse `z ↦ (z - j(C0 z), C0 z)` and reconstruction `(c,f) ↦ c+j(f)`.

The output-dot commutator is globally concentrated in polynomial degree zero.
On a crossing it is minus the self-crossing sign times the twisted old
composition; in the odd case this is a positive constant. No polynomial
linearity, old-quotient flatness, or finite-colour assumption is used.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped Classical DirectSum TensorProduct
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The polynomial prescribed by a moving exponent and crossing word. -/
def appendTailPolynomialData (i : I) (s t : List I) (L : List PG) (m : ℕ) :
    ℕ →₀ hom D Sc cutoff s t := by
  by_cases hL : L = []
  · by_cases ht : s = t
    · exact Finsupp.single m (eqToHom (congrArg (obj D Sc cutoff) ht))
    · exact 0
  · by_cases hs : s = s.dropLast ++ [i]
    · by_cases ht : SChain (s.dropLast ++ [i]) (pl (s.dropLast ++ [i]) L.tail) t
      · exact Finsupp.mapRange.linearMap
          (Linear.leftComp k _ (eqToHom (congrArg (obj D Sc cutoff) hs)))
          (appendCrossingCorrection D Sc cutoff i s.dropLast t m
            (affineUnit D Sc cutoff _ _ (cl D Sc _ _ L.tail ht)))
      · exact 0
    · exact 0

/-- The polynomial part prescribed by the input moving tail. -/
def appendTailPolynomialCandidate (i : I) (v t : List I)
    (x : AppendIdx i v (t ++ [i])) :
    ℕ →₀ hom D Sc cutoff x.oldTarget t :=
  appendTailPolynomialData D Sc cutoff i x.oldTarget t
    (cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹)) x.1.1

/-- Compose a finite old output row with an arbitrary old quotient input. -/
def appendPolynomialOldPair (v s t : List I)
    (f : ℕ →₀ hom D Sc cutoff s t) :
    Old D Sc cutoff v s →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  f.sum fun m g => (Finsupp.lsingle m).comp
    ((oldComp D Sc cutoff v s t).flip ((ideal D Sc cutoff s t).mkQ g))

/-- A corrected coordinate candidate on the actual append-old quotient.
The crossing and recovery laws are proved below before exporting `appendC0`. -/
def appendC0Candidate (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  (DirectSum.toModule k _ _ fun q : AppendIdx.Tail i v (t ++ [i]) =>
    appendPolynomialOldPair D Sc cutoff v q.representative.oldTarget t
      (appendTailPolynomialCandidate D Sc cutoff i v t q.representative)).comp
    (appendOldCoordinateEquiv D Sc cutoff 0 i v (t ++ [i])).toLinearMap

@[simp] theorem appendC0Candidate_reconstruct_lof (i : I) (v t : List I)
    (q : AppendIdx.Tail i v (t ++ [i]))
    (b : Old D Sc cutoff v q.representative.oldTarget) :
    appendC0Candidate D Sc cutoff i v t
      (appendOldReconstruct D Sc cutoff 0 i v (t ++ [i]) (DirectSum.lof k _ _ q b)) =
    appendPolynomialOldPair D Sc cutoff v q.representative.oldTarget t
      (appendTailPolynomialCandidate D Sc cutoff i v t q.representative) b := by
  simp only [appendC0Candidate, LinearMap.comp_apply, LinearEquiv.coe_coe,
    appendOldCoordinateEquiv_reconstruct, DirectSum.toModule_lof]

@[simp] theorem appendPolynomialOldPair_single (v s t : List I) (m : ℕ)
    (g : hom D Sc cutoff s t) (b : Old D Sc cutoff v s) :
    appendPolynomialOldPair D Sc cutoff v s t (Finsupp.single m g) b =
      Finsupp.single m (oldComp D Sc cutoff v s t b ((ideal D Sc cutoff s t).mkQ g)) := by
  simp [appendPolynomialOldPair]

@[simp] theorem appendTailPolynomialData_nil (i : I) (t : List I) (m : ℕ) :
    appendTailPolynomialData D Sc cutoff i t t [] m = Finsupp.single m (𝟙 _) := by
  simp [appendTailPolynomialData]

private theorem appendCorrection_transport (i : I) (s s' t : List I)
    (e : s' = s) (L : List PG) (m : ℕ)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (h' : SChain (s' ++ [i]) (pl (s' ++ [i]) L) t) :
    Finsupp.mapRange.linearMap
      (Linear.leftComp k _ (eqToHom (congrArg (fun a => obj D Sc cutoff (a ++ [i])) e.symm)))
      (appendCrossingCorrection D Sc cutoff i s' t m
        (affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h'))) =
    appendCrossingCorrection D Sc cutoff i s t m
      (affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) := by
  subst s'
  ext d
  simp [Finsupp.mapRange.linearMap_apply, Linear.leftComp_apply]

/-- The candidate uses the nonzero triangular correction on a crossing row. -/
theorem appendTailPolynomialData_cross (i : I) (s t : List I) (L : List PG) (m : ℕ)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t) :
    appendTailPolynomialData D Sc cutoff i (s ++ [i]) t (PG.cross s.length :: L) m =
      appendCrossingCorrection D Sc cutoff i s t m
        (affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) := by
  dsimp only [appendTailPolynomialData]
  rw [dite_eq_right (List.cons_ne_nil _ _)]
  have he : (s ++ [i]).dropLast = s := List.dropLast_concat
  rw [dite_eq_left (congrArg (· ++ [i]) he).symm]
  have ht : SChain ((s ++ [i]).dropLast ++ [i])
      (pl ((s ++ [i]).dropLast ++ [i]) (PG.cross s.length :: L).tail) t := by
    simpa only [he, List.tail_cons] using h
  rw [dite_eq_left ht]
  exact appendCorrection_transport D Sc cutoff i s _ t he L m h ht

theorem appendC0Candidate_pair_representative (i : I) (v t : List I)
    (q : AppendIdx.Tail i v (t ++ [i]))
    (b : Old D Sc cutoff v q.representative.oldTarget) :
    appendC0Candidate D Sc cutoff i v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _
        (appendTail D Sc q.representative)) b) =
    appendPolynomialOldPair D Sc cutoff v q.representative.oldTarget t
      (appendTailPolynomialCandidate D Sc cutoff i v t q.representative) b := by
  have he : affineUnit D Sc cutoff _ _ (appendTail D Sc q.representative) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        appendTail D Sc q.representative : hom D Sc cutoff
          (q.representative.oldTarget ++ [i]) (t ++ [i])) := rfl
  rw [he]
  simpa only [appendOldReconstruct, DirectSum.toModule_lof] using
    appendC0Candidate_reconstruct_lof D Sc cutoff i v t q b

private theorem appendTailPair_transport {i : I} {v s s' w : List I}
    (e : s = s') (r : hom D Sc cutoff v s)
    (a : (pres D Sc).obj (ob D (s ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (b : (pres D Sc).obj (ob D (s' ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (hab : HEq a b) :
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ a)
      ((ideal D Sc cutoff v s).mkQ r) =
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ b)
      ((ideal D Sc cutoff v s').mkQ (e ▸ r)) := by
  subst s'
  cases hab
  rfl

private theorem appendDataPair_transport (i : I) {v s s' t : List I}
    (e : s = s') (L : List PG) (m : ℕ) (r : hom D Sc cutoff v s) :
    appendPolynomialOldPair D Sc cutoff v s t
      (appendTailPolynomialData D Sc cutoff i s t L m) ((ideal D Sc cutoff v s).mkQ r) =
    appendPolynomialOldPair D Sc cutoff v s' t
      (appendTailPolynomialData D Sc cutoff i s' t L m)
        ((ideal D Sc cutoff v s').mkQ (e ▸ r)) := by
  subst s'
  rfl

/-- Readback of the corrected candidate on every existing input PBW tail. -/
theorem appendC0Candidate_pair (i : I) (v t : List I)
    (x : AppendIdx i v (t ++ [i])) (r : hom D Sc cutoff v x.oldTarget) :
    appendC0Candidate D Sc cutoff i v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ (appendTail D Sc x))
        ((ideal D Sc cutoff v x.oldTarget).mkQ r)) =
    appendPolynomialOldPair D Sc cutoff v x.oldTarget t
      (appendTailPolynomialCandidate D Sc cutoff i v t x)
        ((ideal D Sc cutoff v x.oldTarget).mkQ r) := by
  let q : AppendIdx.Tail i v (t ++ [i]) := ⟨x.tailKey, x, rfl⟩
  have hk : x.tailKey = q.representative.tailKey := q.representative_tailKey.symm
  have ht := x.oldTarget_eq_of_tailKey_eq q.representative hk
  rw [appendTailPair_transport D Sc cutoff ht r _ _
    (appendTail_heq_of_tailKey_eq D Sc x q.representative hk)]
  rw [appendC0Candidate_pair_representative]
  have hm := congrArg Prod.fst hk
  have hd := congrArg Prod.snd hk
  change x.1.1 = q.representative.1.1 at hm
  change x.1.2.2.2 = q.representative.1.2.2.2 at hd
  unfold appendTailPolynomialCandidate
  rw [← hm, ← hd]
  exact (appendDataPair_transport D Sc cutoff i ht _ _ r).symm

private def appendIdentityShuffle (i : I) (v : List I) : AppendShuffle (appendLen v i) :=
  AppendShuffle.cast rfl (appendLen v i) (appendRun v.length (Fin.last v.length))

private theorem appendIdentityShuffle_word (i : I) (v : List I) :
    Categorification.TypeA.canWord (v ++ [i]).length (appendIdentityShuffle i v).1⁻¹ = [] := by
  rw [appendIdentityShuffle, AppendShuffle.canWord_cast, canWord_appendRun]
  simp

private def appendIdentityIndex (i : I) {v t : List I} (y : NFIdx v t) (m : ℕ) :
    AppendIdx i v (t ++ [i]) :=
  ⟨(m, y.1.1, y.1.2, appendIdentityShuffle i v), y.2.1, y.2.2.1, by
    have he := tgt_append_right [i] (t := v)
      (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2))
    simpa only [appendCrossingWord, appendIdentityShuffle_word, List.append_nil,
      cw_append, tgt_append, cw, List.reverse_nil, List.map_nil,
      List.nil_append] using he.trans (congrArg (· ++ [i]) y.tgt_cw)⟩

private theorem appendIdentityIndex_target (i : I) {v t : List I} (y : NFIdx v t) (m : ℕ) :
    (appendIdentityIndex i y m).oldTarget = t := y.tgt_cw

private theorem append_cl_heq {s s' t t' : List I} {L L' : List PG}
    (hs : s = s') (ht : t = t') (hL : L = L')
    (h : SChain s (pl s L) t) (h' : SChain s' (pl s' L') t') :
    HEq (cl D Sc s t L h) (cl D Sc s' t' L' h') := by
  subst s'
  subst t'
  subst L'
  rfl

private theorem appendIdentityIndex_tail (i : I) {v t : List I}
    (y : NFIdx v t) (m : ℕ) :
    HEq (appendTail D Sc (appendIdentityIndex i y m))
      ((dotE D Sc (t ++ [i]) t.length) ^ m) := by
  have ht := appendIdentityIndex_target i y m
  have hl : v.length = t.length := by
    have he := congrArg List.length y.tgt_cw
    simpa only [length_tgt] using he
  unfold appendTail
  rw [dotE_pow]
  apply append_cl_heq D Sc (congrArg (· ++ [i]) ht) rfl
  simp only [appendIdentityIndex, appendIdentityShuffle_word, cw,
    List.reverse_nil, List.map_nil, List.append_nil, List.map_replicate, hl]

private theorem appendDataPair_nil (i : I) {v s t : List I}
    (e : s = t) (m : ℕ) (r : hom D Sc cutoff v s) :
    appendPolynomialOldPair D Sc cutoff v s t
      (appendTailPolynomialData D Sc cutoff i s t [] m)
      ((ideal D Sc cutoff v s).mkQ r) =
    Finsupp.single m ((ideal D Sc cutoff v t).mkQ (e ▸ r)) := by
  subst t
  rw [appendTailPolynomialData_nil, appendPolynomialOldPair_single, oldComp_mk,
    Category.comp_id]

/-- Recovery on the specified output embedding, not on a newly chosen section. -/
theorem appendC0Candidate_embedding_single (i : I) (v t : List I) (m : ℕ)
    (g : hom D Sc cutoff v t) :
    appendC0Candidate D Sc cutoff i v t
      (appendOutputEmbedding D Sc cutoff i v t
        (Finsupp.single m ((ideal D Sc cutoff v t).mkQ g))) =
    Finsupp.single m ((ideal D Sc cutoff v t).mkQ g) := by
  by_cases hg : g = 0
  · simp [hg]
  obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff g hg
  let x := appendIdentityIndex i y m
  have ht : x.oldTarget = t := appendIdentityIndex_target i y m
  let r : hom D Sc cutoff v x.oldTarget := ht.symm ▸ g
  have hr : ht ▸ r = g := by
    exact (show ∀ {a b : List I} (e : a = b) (z : hom D Sc cutoff v b),
      e ▸ (e.symm ▸ z : hom D Sc cutoff v a) = z from
        by intro a b e z; cases e; rfl) ht g
  have he := appendTailPair_transport D Sc cutoff ht r
    (appendTail D Sc x) ((dotE D Sc (t ++ [i]) t.length) ^ m)
    (appendIdentityIndex_tail D Sc i y m)
  rw [hr] at he
  have hc := appendC0Candidate_pair D Sc cutoff i v t x r
  rw [he] at hc
  have hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) = [] := by
    simp only [x, appendIdentityIndex, appendIdentityShuffle_word, cw,
      List.reverse_nil, List.map_nil]
  unfold appendTailPolynomialCandidate at hc
  rw [hw, appendDataPair_nil D Sc cutoff i ht, hr] at hc
  simpa only [appendOutputEmbedding_single, appendPair_mk, twist_zero,
    appendMovingPower, x, appendIdentityIndex] using hc

theorem appendC0Candidate_embedding (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    appendC0Candidate D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    exact appendC0Candidate_embedding_single D Sc cutoff i v t m g

private theorem appendPolynomialOldPair_mk (v s t : List I)
    (f : ℕ →₀ hom D Sc cutoff s t) (r : hom D Sc cutoff v s) :
    appendPolynomialOldPair D Sc cutoff v s t f ((ideal D Sc cutoff v s).mkQ r) =
    Finsupp.mapRange.linearMap (ideal D Sc cutoff v t).mkQ
      (Finsupp.lsum k (fun d => (Finsupp.lsingle d).comp (Linear.leftComp k _ r)) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [appendPolynomialOldPair]
  | add f g hf hg =>
    have hadd : appendPolynomialOldPair D Sc cutoff v s t (f + g) =
        appendPolynomialOldPair D Sc cutoff v s t f + appendPolynomialOldPair D Sc cutoff v s t g := by
      unfold appendPolynomialOldPair
      apply Finsupp.sum_add_index
      · intro m; simp
      · intro m a b; simp [map_add, LinearMap.comp_add]
    rw [hadd, LinearMap.add_apply, hf, hg, map_add, map_add]
  | single m g =>
    simp only [appendPolynomialOldPair_single, oldComp_mk, Finsupp.lsum_single,
      LinearMap.comp_apply, Linear.leftComp_apply, Finsupp.lsingle_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]

private theorem appendC0Candidate_outputPolynomial_precomp (i : I) (v s t : List I)
    (r : hom D Sc cutoff v s) (f : ℕ →₀ hom D Sc cutoff s t) :
    appendC0Candidate D Sc cutoff i v t
      (appendProjection D Sc cutoff i v (t ++ [i])
        (rightContext D Sc cutoff [i] _ _ r ≫ appendOutputPolynomial D Sc cutoff i s t f)) =
    appendPolynomialOldPair D Sc cutoff v s t f ((ideal D Sc cutoff v s).mkQ r) := by
  rw [appendOutputPolynomial_precomp, ← appendOutputEmbedding_map,
    appendC0Candidate_embedding, appendPolynomialOldPair_mk]

private theorem appendTail_cross_heq (i : I) (v s t : List I)
    (x : AppendIdx i v (t ++ [i])) (e : x.oldTarget = s ++ [i])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t) :
    HEq (appendTail D Sc x)
      (((dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) ^ x.1.1) ≫
        crossLast D Sc s i i ≫ affineRightContext D Sc [i] _ _ (cl D Sc _ _ L h)) := by
  have hl : v.length = s.length + 1 := by
    have hh := congrArg List.length e
    simpa only [AppendIdx.oldTarget, length_tgt, List.length_append,
      List.length_singleton] using hh
  change HEq (appendTail D Sc x)
    (_ ≫ crossLast D Sc s i i ≫ (cl D Sc _ _ L h ▷ (pres D Sc).obj (ob D [i])))
  rw [dotE_pow, crossLast, cl_whiskerRight D Sc _ _ [i] hf, cl_comp, cl_comp]
  unfold appendTail
  apply append_cl_heq D Sc (congrArg (· ++ [i]) e) rfl
  simp only [hw, hl, List.map_replicate, List.singleton_append]

/-- The corrected functional annihilates every canonical crossing row, with
an arbitrary full old input coefficient and every moving power. -/
theorem appendC0Candidate_canonical_crossing (i : I) (v s t : List I)
    (x : AppendIdx i v (t ++ [i])) (e : x.oldTarget = s ++ [i])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (r : hom D Sc cutoff v x.oldTarget) :
    appendC0Candidate D Sc cutoff i v t
      (appendCrossingClass D Sc cutoff i v s t (e ▸ r)
        (appendMovingPower D Sc cutoff i s x.1.1 ≫
          affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))) = 0 := by
  have he := appendTailPair_transport D Sc cutoff e r _ _
    (appendTail_cross_heq D Sc i v s t x e L hw hf h)
  have hc := appendC0Candidate_pair D Sc cutoff i v t x r
  rw [he] at hc
  unfold appendTailPolynomialCandidate at hc
  rw [hw, appendDataPair_transport D Sc cutoff i e] at hc
  rw [appendTailPolynomialData_cross D Sc cutoff i s t L x.1.1 h] at hc
  simp only [appendPair_mk, twist_zero, affineUnit_comp,
    ← rightContext_affineUnit] at hc
  have hp : appendMovingPower D Sc cutoff i (s ++ [i]) x.1.1 =
      affineUnit D Sc cutoff _ _ ((dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) ^ x.1.1) := by
    simp only [appendMovingPower, List.length_append, List.length_singleton]
  rw [← hp] at hc
  rw [appendProjection_crossing_power_triangular, map_add, map_smul,
    appendC0Candidate_outputPolynomial_precomp] at hc
  have hz := add_right_cancel (hc.trans (zero_add _).symm)
  change SKM.zsign k (D.parity i * D.parity i) ^ x.1.1 • _ = 0 at hz
  have hu : IsUnit (SKM.zsign k (D.parity i * D.parity i) ^ x.1.1) := by
    apply IsUnit.pow
    unfold SKM.zsign
    split <;> simp
  exact (hu.smul_eq_zero).mp hz

private def appendShuffleSizeCast {n n' : ℕ} (e : n = n') :
    AppendShuffle (show n + 1 = n + 1 from rfl) ≃
      AppendShuffle (show n' + 1 = n' + 1 from rfl) := by
  subst n'
  exact Equiv.refl _

private theorem appendShuffleSizeCast_word {n n' : ℕ} (e : n = n')
    (d : AppendShuffle (show n + 1 = n + 1 from rfl)) :
    Categorification.TypeA.canWord (n' + 1) (appendShuffleSizeCast e d).1⁻¹ =
    Categorification.TypeA.canWord (n + 1) d.1⁻¹ := by
  subst n'
  rfl

private def appendIndexWithTail (i : I) {v u w : List I} (y : NFIdx v u)
    (d : AppendShuffle (appendLen v i)) (m : ℕ)
    (h : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = w) :
    AppendIdx i v w :=
  ⟨(m, y.1.1, y.1.2, d), y.2.1, y.2.2.1, by
    rw [appendCrossingWord, cw_append, tgt_append,
      tgt_append_right [i] (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2)),
      y.tgt_cw]
    exact h⟩

private theorem appendIndexWithTail_target (i : I) {v u w : List I} (y : NFIdx v u)
    (d : AppendShuffle (appendLen v i)) (m : ℕ)
    (h : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = w) :
    (appendIndexWithTail i y d m h).oldTarget = u := y.tgt_cw

private theorem appendTail_cross_chain {i : I} {s t : List I} (z : AppendIdx i s t) :
    SChain (z.oldTarget ++ [i])
      (pl (z.oldTarget ++ [i]) (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))) t := by
  have hz := z.2.2.2
  rw [appendCrossingWord, cw_append, tgt_append,
    tgt_append_right [i] (fits_cw (Categorification.TypeA.validWord_canWord s.length z.1.2.2.1))] at hz
  change tgt (z.oldTarget ++ [i])
    (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)) = t at hz
  simpa only [hz] using sChain_pl (z.oldTarget ++ [i])
    (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))

private theorem appendTail_cross_fits {i : I} {s t : List I} (z : AppendIdx i s t) :
    Fits (z.oldTarget ++ [i]).length
      (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)) := by
  simpa only [AppendIdx.oldTarget, List.length_append, length_tgt] using
    fits_cw (Categorification.TypeA.validWord_canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)

private theorem appendRunWord_castSucc (n : ℕ) (j : Fin (n + 1)) :
    cw (Categorification.TypeA.canWord (n + 2) (appendRun (n + 1) j.castSucc).1⁻¹) =
      PG.cross n :: cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹) := by
  rw [canWord_appendRun, canWord_appendRun, Fin.val_castSucc]
  have hj : j.val ≤ n := Nat.lt_succ_iff.mp j.2
  rw [show n + 1 - j.val = (n - j.val) + 1 by omega, List.range'_concat, cw_append]
  simp only [cw, List.reverse_singleton, List.map_singleton, List.cons_append, List.nil_append]
  congr 2
  omega

private theorem appendCrossingShuffle_exists (i : I) (v s t : List I)
    (z : AppendIdx i s t) (hv : s.length + 1 = v.length) :
    ∃ d : AppendShuffle (appendLen v i),
      cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹) =
        PG.cross s.length ::
          cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹) := by
  let d0 := AppendShuffle.cast (appendLen s i) rfl z.1.2.2.2
  let j := (appendRunEquiv s.length).symm d0
  let d1 := appendShuffleSizeCast hv (appendRun (s.length + 1) j.castSucc)
  refine ⟨AppendShuffle.cast rfl (appendLen v i) d1, ?_⟩
  rw [AppendShuffle.canWord_cast, appendShuffleSizeCast_word]
  rw [appendRunWord_castSucc]
  have hj : appendRun s.length j = d0 := (appendRunEquiv s.length).apply_symm_apply d0
  rw [hj, AppendShuffle.canWord_cast]

private theorem appendTail_power_cross (i : I) (s t : List I) (z : AppendIdx i s t) :
    affineUnit D Sc cutoff _ _ (appendTail D Sc z) =
      appendMovingPower D Sc cutoff i z.oldTarget z.1.1 ≫
        affineUnit D Sc cutoff _ _
          (cl D Sc _ _ (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))
            (appendTail_cross_chain z)) := by
  have hl : z.oldTarget.length = s.length := by simp only [AppendIdx.oldTarget, length_tgt]
  unfold appendMovingPower
  rw [← affineUnit_comp]
  apply congrArg (affineUnit D Sc cutoff _ _)
  unfold appendTail
  rw [dotE_pow, cl_comp]
  apply eq_of_heq
  apply append_cl_heq D Sc rfl rfl
  simp only [hl, List.map_replicate]

/-- All actual old append tails are annihilated after the final crossing. -/
theorem appendC0Candidate_crossing_tail (i : I) (v s t : List I)
    (z : AppendIdx i s t) (r : hom D Sc cutoff v (z.oldTarget ++ [i])) :
    appendC0Candidate D Sc cutoff i v t
      (appendCrossingClass D Sc cutoff i v z.oldTarget t r
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z))) = 0 := by
  by_cases hr : r = 0
  · simp [hr, appendCrossingClass]
  obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff r hr
  have hv : s.length + 1 = v.length := by
    have hh := congrArg List.length y.tgt_cw
    simpa only [length_tgt, List.length_append, List.length_singleton,
      AppendIdx.oldTarget] using hh.symm
  obtain ⟨d, hd⟩ := appendCrossingShuffle_exists i v s t z hv
  have hzlen : z.oldTarget.length = s.length := by simp only [AppendIdx.oldTarget, length_tgt]
  let L := cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)
  have hc := appendTail_cross_chain z
  have hf := appendTail_cross_fits z
  have htarget : tgt (z.oldTarget ++ [i] ++ [i])
      (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = t ++ [i] := by
    rw [hd, show PG.cross s.length = PG.cross z.oldTarget.length from congrArg PG.cross hzlen.symm,
      tgt_cons]
    have hcross : tgt (z.oldTarget ++ [i] ++ [i]) [PG.cross z.oldTarget.length] =
        z.oldTarget ++ [i] ++ [i] := tgt_eq (by simpa using sChain_crossAt z.oldTarget [] i i)
    simp only [tgt_cons, tgt_nil] at hcross
    rw [hcross]
    exact (tgt_append_right [i] hf).trans (congrArg (· ++ [i]) (tgt_eq hc))
  let x := appendIndexWithTail i y d z.1.1 htarget
  have he : x.oldTarget = z.oldTarget ++ [i] := appendIndexWithTail_target i y d z.1.1 htarget
  let r' : hom D Sc cutoff v x.oldTarget := he.symm ▸ r
  have hr' : he ▸ r' = r := by
    exact (show ∀ {a b : List I} (e : a = b) (q : hom D Sc cutoff v b),
      e ▸ (e.symm ▸ q : hom D Sc cutoff v a) = q from
        by intro a b e q; cases e; rfl) he r
  have hword : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross z.oldTarget.length :: L := by simpa only [x, appendIndexWithTail, hzlen] using hd
  have hh := appendC0Candidate_canonical_crossing D Sc cutoff i v z.oldTarget t
    x he L hword hf hc r'
  rw [hr'] at hh
  rw [appendTail_power_cross]
  exact hh

private theorem appendCrossingClass_prefix (i : I) (v s u t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (b : hom D Sc cutoff s u)
    (g : hom D Sc cutoff (u ++ [i]) t) :
    appendCrossingClass D Sc cutoff i v s t r (rightContext D Sc cutoff [i] _ _ b ≫ g) =
      appendCrossingClass D Sc cutoff i v u t
        (r ≫ rightContext D Sc cutoff [i] _ _ (twist k (D.parity i * D.parity i) b)) g := by
  simp only [appendCrossingClass, rightContext_comp, Category.assoc]
  rw [← Category.assoc (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i)),
    crossLast_comp_rightContext, Category.assoc]

/-- The actual corrected functional annihilates the entire crossing image,
with arbitrary full old arrows on both sides. -/
theorem appendC0Candidate_crossing (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendC0Candidate D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g) = 0 := by
  suffices hh : ∀ f : AppendIdx i s t →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff,
      appendC0Candidate D Sc cutoff i v t
        (appendCrossingClass D Sc cutoff i v s t r ((appendAffineEquiv D Sc cutoff i s t).symm f)) = 0 by
    simpa only [LinearEquiv.symm_apply_apply] using hh ((appendAffineEquiv D Sc cutoff i s t) g)
  intro f
  induction f using Finsupp.induction_linear with
  | zero => simp [appendCrossingClass]
  | add f g hf hg =>
    simpa only [map_add, appendCrossingClass, rightContext_comp, Preadditive.comp_add,
      map_add, add_zero] using congrArg₂ (· + ·) hf hg
  | single z a =>
    rw [appendAffineEquiv_symm_single]
    have hfactor : (a ⊗ₜ[k] appendElt D Sc z : hom D Sc cutoff (s ++ [i]) t) =
        rightContext D Sc cutoff [i] _ _ (coefficientTwist D cutoff (appendTailParity D z) a ⊗ₜ[k] z.old.nf) ≫
          affineUnit D Sc cutoff _ _ (appendTail D Sc z) := by
      have he : affineUnit D Sc cutoff _ _ (appendTail D Sc z) =
          ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc z :
            hom D Sc cutoff (z.oldTarget ++ [i]) t) := rfl
      rw [he]
      exact (append_insert_twisted_coefficient D Sc cutoff z a).symm
    rw [hfactor, appendCrossingClass_prefix]
    exact appendC0Candidate_crossing_tail D Sc cutoff i v s t z _

/-- The corrected polynomial projection, with recovery and entire-crossing
annihilation now proved for its explicit coordinate construction. -/
def appendC0 (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  appendC0Candidate D Sc cutoff i v t

@[simp] theorem appendC0_embedding (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    appendC0 D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) = f :=
  appendC0Candidate_embedding D Sc cutoff i v t f

@[simp] theorem appendC0_crossing (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendC0 D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g) = 0 :=
  appendC0Candidate_crossing D Sc cutoff i v s t r g

/-- The genuine full crossing span, with arbitrary old arrows on both sides. -/
def appendCrossingSpan (i : I) (v t : List I) :
    Submodule k (AppendTarget D Sc cutoff i v (t ++ [i])) :=
  Submodule.span k {z | ∃ (s : List I) (r : hom D Sc cutoff v (s ++ [i]))
    (g : hom D Sc cutoff (s ++ [i]) t), z = appendCrossingClass D Sc cutoff i v s t r g}

theorem appendCrossingSpan_le_ker (i : I) (v t : List I) :
    appendCrossingSpan D Sc cutoff i v t ≤ LinearMap.ker (appendC0 D Sc cutoff i v t) := by
  apply Submodule.span_le.mpr
  rintro z ⟨s, r, g, rfl⟩
  exact appendC0_crossing D Sc cutoff i v s t r g

/-- The global constant defect on every genuine crossing, not merely a local
identity or an assumed polynomial-linear projection. -/
theorem appendC0_outputDot_crossing (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendC0 D Sc cutoff i v t
      (appendOutputDot D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g)) =
    -SKM.zsign k (D.parity i * D.parity i) •
      Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (r ≫ twist k (D.parity i) g)) := by
  rw [appendOutputDot_crossingClass, map_sub, map_smul, map_smul,
    appendC0_crossing, appendC0_embedding, smul_zero, zero_sub, neg_smul]

private theorem appendRunWord_shape (i : I) (u t : List I) (n : ℕ) (hn : u.length = n)
    (j : Fin (n + 1))
    (ht : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹)) = t ++ [i]) :
    (cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹) = [] ∧ u = t) ∨
    ∃ (s : List I) (L : List PG), u = s ++ [i] ∧
      cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹) = PG.cross s.length :: L ∧
      Fits (s ++ [i]).length L ∧ SChain (s ++ [i]) (pl (s ++ [i]) L) t := by
  cases n with
  | zero =>
    have hj : j = Fin.last 0 := by apply Fin.ext; have := j.2; simp only [Fin.val_last]; omega
    have hw : cw (Categorification.TypeA.canWord 1 (appendRun 0 j).1⁻¹) = [] := by
      rw [hj, canWord_appendRun]
      simp [cw]
    rw [hw, tgt_nil] at ht
    exact Or.inl ⟨hw, List.append_cancel_right ht⟩
  | succ n =>
    revert ht
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro ht
      have hw : cw (Categorification.TypeA.canWord (n + 1 + 1)
          (appendRun (n + 1) (Fin.last (n + 1))).1⁻¹) = [] := by
        rw [canWord_appendRun]
        simp [cw]
      rw [hw, tgt_nil] at ht
      exact Or.inl ⟨hw, List.append_cancel_right ht⟩
    · intro ht
      have hu : u ≠ [] := by intro h; simp [h] at hn
      obtain ⟨s, c, rfl⟩ := (List.eq_nil_or_concat' u).resolve_left hu
      have hs : s.length = n := by simpa only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] using hn
      let L := cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹)
      have hw : cw (Categorification.TypeA.canWord (n + 2) (appendRun (n + 1) j.castSucc).1⁻¹) =
          PG.cross s.length :: L := by simpa only [hs] using appendRunWord_castSucc n j
      have hf : Fits (s ++ [i]).length L := by
        simpa only [List.length_append, List.length_singleton, hs] using
          fits_cw (Categorification.TypeA.validWord_canWord (n + 1) (appendRun n j).1⁻¹)
      rw [hw, tgt_cons] at ht
      have hcross : (PG.cross s.length).act (s ++ [c] ++ [i]) = s ++ [i] ++ [c] := by
        have hc : tgt (s ++ [c] ++ [i]) [PG.cross s.length] = s ++ [i] ++ [c] :=
          tgt_eq (by simpa using sChain_crossAt s [] c i)
        simpa only [tgt_cons, tgt_nil] using hc
      rw [hcross, tgt_append_right [c] hf] at ht
      have hci : c = i := by
        have he := congrArg List.getLast? ht
        simpa using he
      subst c
      have ht' := List.append_cancel_right ht
      exact Or.inr ⟨s, L, rfl, hw, hf, by rw [← ht']; exact sChain_pl _ _⟩

private theorem appendTail_shape (i : I) (v t : List I) (x : AppendIdx i v (t ++ [i])) :
    (cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) = [] ∧ x.oldTarget = t) ∨
    ∃ (s : List I) (L : List PG), x.oldTarget = s ++ [i] ∧
      cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) = PG.cross s.length :: L ∧
      Fits (s ++ [i]).length L ∧ SChain (s ++ [i]) (pl (s ++ [i]) L) t := by
  let d0 := AppendShuffle.cast (appendLen v i) rfl x.1.2.2.2
  let j := (appendRunEquiv v.length).symm d0
  have hj : appendRun v.length j = d0 := (appendRunEquiv v.length).apply_symm_apply d0
  have hw : cw (Categorification.TypeA.canWord (v.length + 1) (appendRun v.length j).1⁻¹) =
      cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) := by
    rw [hj, AppendShuffle.canWord_cast]
  have hl : x.oldTarget.length = v.length := by simp only [AppendIdx.oldTarget, length_tgt]
  have ht : tgt (x.oldTarget ++ [i])
      (cw (Categorification.TypeA.canWord (v.length + 1) (appendRun v.length j).1⁻¹)) = t ++ [i] := by
    rw [hw]
    exact tgt_eq (appendTail_cross_chain x)
  simpa only [hw] using appendRunWord_shape i x.oldTarget t v.length hl j ht

private theorem appendTail_nil_heq (i : I) (v t : List I)
    (x : AppendIdx i v (t ++ [i])) (e : x.oldTarget = t)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) = []) :
    HEq (appendTail D Sc x) ((dotE D Sc (t ++ [i]) t.length) ^ x.1.1) := by
  have hl : v.length = t.length := by
    have hh := congrArg List.length e
    simpa only [AppendIdx.oldTarget, length_tgt] using hh
  unfold appendTail
  rw [dotE_pow]
  apply append_cl_heq D Sc (congrArg (· ++ [i]) e) rfl
  simp only [hw, hl, List.map_replicate, List.append_nil]

private theorem appendPair_mem_crossing_sup_output (i : I) (v t : List I)
    (x : AppendIdx i v (t ++ [i])) (r : hom D Sc cutoff v x.oldTarget) :
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ (appendTail D Sc x))
      ((ideal D Sc cutoff v x.oldTarget).mkQ r) ∈
      appendCrossingSpan D Sc cutoff i v t ⊔ LinearMap.range (appendOutputEmbedding D Sc cutoff i v t) := by
  rcases appendTail_shape i v t x with ⟨hw, e⟩ | ⟨s, L, e, hw, hf, h⟩
  · rw [appendTailPair_transport D Sc cutoff e r _ _ (appendTail_nil_heq D Sc i v t x e hw),
      appendPair_mk, twist_zero]
    apply Submodule.mem_sup_right
    refine ⟨Finsupp.single x.1.1 ((ideal D Sc cutoff v t).mkQ (e ▸ r)), ?_⟩
    exact appendOutputEmbedding_single D Sc cutoff i v t x.1.1 (e ▸ r)
  · rw [appendTailPair_transport D Sc cutoff e r _ _
      (appendTail_cross_heq D Sc i v s t x e L hw hf h), appendPair_mk, twist_zero]
    simp only [affineUnit_comp, ← rightContext_affineUnit]
    have hp : appendMovingPower D Sc cutoff i (s ++ [i]) x.1.1 =
        affineUnit D Sc cutoff _ _ ((dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) ^ x.1.1) := by
      simp only [appendMovingPower, List.length_append, List.length_singleton]
    rw [← hp, appendProjection_crossing_power_triangular]
    apply Submodule.add_mem
    · apply Submodule.smul_mem
      apply Submodule.mem_sup_left
      apply Submodule.subset_span
      exact ⟨s, e ▸ r, appendMovingPower D Sc cutoff i s x.1.1 ≫
        affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h), rfl⟩
    · apply Submodule.mem_sup_right
      rw [appendOutputPolynomial_precomp, ← appendOutputEmbedding_map]
      exact LinearMap.mem_range_self _ _

/-- The polynomial row and actual crossing span exhaust the append target,
including the separate height-zero case in the canonical run analysis. -/
theorem appendCrossingSpan_sup_output (i : I) (v t : List I) :
    appendCrossingSpan D Sc cutoff i v t ⊔ LinearMap.range (appendOutputEmbedding D Sc cutoff i v t) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨f, rfl⟩ := (appendOldCoordinateEquiv D Sc cutoff 0 i v (t ++ [i])).symm.surjective z
  change appendOldReconstruct D Sc cutoff 0 i v (t ++ [i]) f ∈ _
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | of q b =>
    change appendOldReconstruct D Sc cutoff 0 i v (t ++ [i]) (DirectSum.lof k _ _ q b) ∈ _
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v q.representative.oldTarget).mkQ_surjective b
    have he : affineUnit D Sc cutoff _ _ (appendTail D Sc q.representative) =
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc q.representative :
          hom D Sc cutoff (q.representative.oldTarget ++ [i]) (t ++ [i])) := rfl
    simpa only [appendOldReconstruct, DirectSum.toModule_lof, he] using
      appendPair_mem_crossing_sup_output D Sc cutoff i v t q.representative r

/-- The kernel is exactly the genuine entire crossing image. -/
theorem appendC0_ker (i : I) (v t : List I) :
    LinearMap.ker (appendC0 D Sc cutoff i v t) = appendCrossingSpan D Sc cutoff i v t := by
  apply le_antisymm _ (appendCrossingSpan_le_ker D Sc cutoff i v t)
  intro z hz
  have hall : z ∈ appendCrossingSpan D Sc cutoff i v t ⊔
      LinearMap.range (appendOutputEmbedding D Sc cutoff i v t) := by
    rw [appendCrossingSpan_sup_output]
    exact Submodule.mem_top
  obtain ⟨c, hc, p, hp, he⟩ := Submodule.mem_sup.mp hall
  obtain ⟨f, rfl⟩ := hp
  have hc0 : appendC0 D Sc cutoff i v t c = 0 := appendCrossingSpan_le_ker D Sc cutoff i v t hc
  have hf := congrArg (appendC0 D Sc cutoff i v t) he
  rw [map_add, hc0, appendC0_embedding, zero_add] at hf
  have hf0 : f = 0 := hf.trans hz
  rw [hf0, map_zero, add_zero] at he
  exact he ▸ hc

theorem appendC0_residual_mem (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    z - appendOutputEmbedding D Sc cutoff i v t (appendC0 D Sc cutoff i v t z) ∈
      appendCrossingSpan D Sc cutoff i v t := by
  rw [← appendC0_ker, LinearMap.mem_ker]
  simp only [map_sub, appendC0_embedding, sub_self]

/-- The prescribed augmented inverse: subtract the actual polynomial output
from the vector to obtain its crossing component. -/
def appendC0Splitting (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) ≃ₗ[k]
      (appendCrossingSpan D Sc cutoff i v t × (ℕ →₀ Old D Sc cutoff v t)) where
  toFun z := (⟨z - appendOutputEmbedding D Sc cutoff i v t (appendC0 D Sc cutoff i v t z),
    appendC0_residual_mem D Sc cutoff i v t z⟩, appendC0 D Sc cutoff i v t z)
  invFun p := p.1.1 + appendOutputEmbedding D Sc cutoff i v t p.2
  left_inv z := sub_add_cancel z _
  right_inv p := by
    obtain ⟨c, f⟩ := p
    have hc : appendC0 D Sc cutoff i v t c.1 = 0 := appendCrossingSpan_le_ker D Sc cutoff i v t c.2
    apply Prod.ext
    · apply Subtype.ext
      change c.1 + _ - _ = c.1
      simp only [map_add, hc, appendC0_embedding, zero_add, add_sub_cancel_right]
    · change appendC0 D Sc cutoff i v t (c.1 + _) = f
      simp only [map_add, hc, appendC0_embedding, zero_add]
  map_add' a b := by
    apply Prod.ext
    · apply Subtype.ext
      change a + b - _ = (a - _) + (b - _)
      simp only [map_add]
      abel
    · exact map_add _ a b
  map_smul' a b := by
    apply Prod.ext
    · apply Subtype.ext
      change a • b - _ = a • (b - _)
      simp only [map_smul, smul_sub]
    · exact map_smul _ a b

@[simp] theorem appendC0Splitting_symm (i : I) (v t : List I)
    (c : appendCrossingSpan D Sc cutoff i v t) (f : ℕ →₀ Old D Sc cutoff v t) :
    (appendC0Splitting D Sc cutoff i v t).symm (c, f) =
      c.1 + appendOutputEmbedding D Sc cutoff i v t f := rfl

/-- The output-dot commutator of the actual global polynomial projection. -/
def appendC0Defect (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  (appendC0 D Sc cutoff i v t).comp (appendOutputDot D Sc cutoff i v t) -
    (appendOutputShift D Sc cutoff v t).comp (appendC0 D Sc cutoff i v t)

@[simp] theorem appendC0Defect_embedding (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    appendC0Defect D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) = 0 := by
  simp only [appendC0Defect, LinearMap.sub_apply, LinearMap.comp_apply,
    appendOutputDot_embedding, appendC0_embedding, sub_self]

@[simp] theorem appendC0Defect_crossing (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendC0Defect D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g) =
      -SKM.zsign k (D.parity i * D.parity i) •
        Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (r ≫ twist k (D.parity i) g)) := by
  simp only [appendC0Defect, LinearMap.sub_apply, LinearMap.comp_apply,
    appendC0_outputDot_crossing, appendC0_crossing, map_zero, sub_zero]

end OddMath.QuiverHecke.ELV
end

end
