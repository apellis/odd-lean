/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputOldTransport
/-!
# Two-sided output-order balanced extraction

The actual bare-long old-factor transport identifies the action of output old
quotient coefficients on every degree. The derived twist is the sum of balance
parity, bare-long parity, and moving-dot parity. A finite normalized long section
extends the comparison to every quotient element. This is the two-sided
coefficient bridge in `DeformedMackeyBoundary.md` (2); identifying the independently
specified boundary polynomial S in corrected rho coordinates remains separate.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem moving_one_short (p : ZMod 2) (i : I) (v : List I)
    {z : Target D Sc cutoff i v (v ++ [i])}
    (hz : z ∈ chronologicalShortSpan D Sc cutoff i v v) :
    signedMovingPowerTarget D Sc cutoff i v (v ++ [i]) 1 z ∈
      chronologicalShortSpan D Sc cutoff i v v := by
  rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v] at hz ⊢
  change outputLongExtraction D Sc cutoff p i v z = 0 at hz
  change outputLongExtraction D Sc cutoff p i v _ = 0
  ext m
  cases m with
  | zero => exact outputLongCoordinate_signedMoving_zero D Sc cutoff p i v 1 (by omega) z
  | succ m =>
    change outputLongCoordinate D Sc cutoff p i v (m+1) _ = 0
    rw [Nat.add_comm m 1, outputLongCoordinate_signedMoving]
    have hm := congrArg (fun f : ℕ →₀ Old D Sc cutoff v v => f m) hz
    change outputLongCoordinate D Sc cutoff p i v m z = 0 at hm
    rw [hm, map_zero, smul_zero]

theorem moving_power_short (p : ZMod 2) (i : I) (v : List I) (d : ℕ)
    {z : Target D Sc cutoff i v (v ++ [i])}
    (hz : z ∈ chronologicalShortSpan D Sc cutoff i v v) :
    signedMovingPowerTarget D Sc cutoff i v (v ++ [i]) d z ∈
      chronologicalShortSpan D Sc cutoff i v v := by
  induction d with
  | zero =>
    obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v (v ++ [i]) z
    change projection D Sc cutoff i v (v ++ [i]) ((𝟙 _) ≫ h) ∈ _
    simpa only [Category.id_comp] using hz
  | succ d ih =>
    rw [Nat.add_comm d 1, ← signedMovingPowerTarget_add]
    exact moving_one_short D Sc cutoff p i v ih

theorem dotted_bareU_transport (p : ZMod 2) (i : I) (v : List I)
    (m : ℕ) (g : hom D Sc cutoff v v) :
    projection D Sc cutoff i v (v ++ [i])
      ((movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v) ≫
        appendInsert D Sc cutoff i v v g -
      insert D Sc cutoff i v v
        (twist k ((m : ZMod 2) * D.parity i + D.parity i * wordSumParity D v) g) ≫
        (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v)) ∈
      chronologicalShortSpan D Sc cutoff i v v := by
  have h := moving_power_short D Sc cutoff p i v m (bareUFull_transport D Sc cutoff i g)
  rw [signedMovingPowerTarget_projection, Preadditive.comp_sub,
    ← Category.assoc, ← Category.assoc, movingPower_insert_twist, Category.assoc, ← twist_add] at h
  simpa only [Category.assoc, nsmul_eq_mul] using h

theorem old_source_short (p : ZMod 2) (i : I) (v : List I)
    (r : hom D Sc cutoff v v) {z : Target D Sc cutoff i v (v ++ [i])}
    (hz : z ∈ chronologicalShortSpan D Sc cutoff i v v) :
    oldSourceTarget D Sc cutoff i v (v ++ [i]) r z ∈
      chronologicalShortSpan D Sc cutoff i v v := by
  rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v] at hz ⊢
  change outputLongExtraction D Sc cutoff p i v z = 0 at hz
  change outputLongExtraction D Sc cutoff p i v _ = 0
  ext n
  change outputLongCoordinate D Sc cutoff p i v n _ = 0
  rw [outputLongCoordinate_oldSource]
  have hn := congrArg (fun f : ℕ →₀ Old D Sc cutoff v v => f n) hz
  change outputLongCoordinate D Sc cutoff p i v n z = 0 at hn
  rw [hn, map_zero]

/-- All dotted long rows, both full old coefficients, in the relative quotient. -/
theorem dotted_bareU_pair_transport (p : ZMod 2) (i : I) (v : List I)
    (m : ℕ) (b : Old D Sc cutoff v v) (g : hom D Sc cutoff v v) :
    act D Sc cutoff i (appendInsert D Sc cutoff i v v g)
      (pair D Sc cutoff p i (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v) b) -
    pair D Sc cutoff p i (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v)
      (oldComp D Sc cutoff v v v b
        (oldTwist D Sc cutoff
          (p + ((m : ZMod 2) * D.parity i + D.parity i * wordSumParity D v)) v v
          ((ideal D Sc cutoff v v).mkQ g))) ∈ chronologicalShortSpan D Sc cutoff i v v := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
  have h := old_source_short D Sc cutoff p i v (twist k p r)
    (dotted_bareU_transport D Sc cutoff p i v m g)
  have twmk (q : ZMod 2) : oldTwist D Sc cutoff q v v
      ((ideal D Sc cutoff v v).mkQ g) = (ideal D Sc cutoff v v).mkQ (twist k q g) := rfl
  rw [twmk, oldComp_mk, pair_mk, pair_mk]
  have ha (f : hom D Sc cutoff (i :: v) (v ++ [i])) :
      act D Sc cutoff i (appendInsert D Sc cutoff i v v g)
        (projection D Sc cutoff i v (v ++ [i]) f) =
      projection D Sc cutoff i v (v ++ [i]) (f ≫ appendInsert D Sc cutoff i v v g) := rfl
  rw [ha, twist_comp, twist_add, twist_twist, insert_comp]
  have hh : oldSourceTarget D Sc cutoff i v (v ++ [i]) (twist k p r)
      (projection D Sc cutoff i v (v ++ [i])
        ((movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v) ≫
          appendInsert D Sc cutoff i v v g -
        insert D Sc cutoff i v v
          (twist k ((m : ZMod 2) * D.parity i + D.parity i * wordSumParity D v) g) ≫
          (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v))) =
      projection D Sc cutoff i v (v ++ [i])
        (insert D Sc cutoff i v v (twist k p r) ≫
          (((movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v) ≫
            appendInsert D Sc cutoff i v v g) -
          insert D Sc cutoff i v v
            (twist k ((m : ZMod 2) * D.parity i + D.parity i * wordSumParity D v) g) ≫
            (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v))) := rfl
  rw [hh] at h
  simpa only [Preadditive.comp_sub, map_sub, Category.assoc] using h

/-- Every extracted degree of a dotted long row has the two-sided old coefficient comparison. -/
theorem dotted_bareU_pair_coordinate (p : ZMod 2) (i : I) (v : List I)
    (m n : ℕ) (b : Old D Sc cutoff v v) (g : hom D Sc cutoff v v) :
    outputLongCoordinate D Sc cutoff p i v n
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g)
        (pair D Sc cutoff p i (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v) b)) =
    outputLongCoordinate D Sc cutoff p i v n
      (pair D Sc cutoff p i (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v)
        (oldComp D Sc cutoff v v v b
          (oldTwist D Sc cutoff
            (p + ((m : ZMod 2) * D.parity i + D.parity i * wordSumParity D v)) v v
            ((ideal D Sc cutoff v v).mkQ g)))) := by
  have h := dotted_bareU_pair_transport D Sc cutoff p i v m b g
  rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v] at h
  change outputLongExtraction D Sc cutoff p i v _ = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact congrArg (fun f : ℕ →₀ Old D Sc cutoff v v => f n) h

/-- The actual output action on a dotted long row, before quotient descent. -/
def dottedOutputRow (p : ZMod 2) (i : I) (v : List I) (m : ℕ)
    (b : Old D Sc cutoff v v) : hom D Sc cutoff v v →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) where
  toFun g := outputLongExtraction D Sc cutoff p i v
    (act D Sc cutoff i (appendInsert D Sc cutoff i v v g)
      (pair D Sc cutoff p i (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v) b))
  map_add' g h := by
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
    simp only [pair_mk, map_add]
    change outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i]) (_ ≫ (_ + _))) = _
    rw [Preadditive.comp_add, map_add, map_add]
    rfl
  map_smul' a g := by
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
    simp only [pair_mk, map_smul]
    change outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i]) (_ ≫ (a • _))) = _
    rw [Linear.comp_smul, map_smul, map_smul]
    rfl

theorem dottedOutputRow_ideal (p : ZMod 2) (i : I) (v : List I) (m : ℕ)
    (b : Old D Sc cutoff v v) {g : hom D Sc cutoff v v}
    (hg : g ∈ ideal D Sc cutoff v v) : dottedOutputRow D Sc cutoff p i v m b g = 0 := by
  ext n
  change outputLongCoordinate D Sc cutoff p i v n _ = 0
  rw [dotted_bareU_pair_coordinate]
  have hg' : (ideal D Sc cutoff v v).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hg
  rw [hg', map_zero, map_zero, map_zero, map_zero]

/-- Output quotient descent of the actual finite extraction on every dotted long row. -/
def dottedOutputQuotientRow (p : ZMod 2) (i : I) (v : List I) (m : ℕ)
    (b : Old D Sc cutoff v v) : Old D Sc cutoff v v →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  (ideal D Sc cutoff v v).liftQ (dottedOutputRow D Sc cutoff p i v m b)
    (fun _ hg => dottedOutputRow_ideal D Sc cutoff p i v m b hg)

@[simp] theorem dottedOutputQuotientRow_mk (p : ZMod 2) (i : I) (v : List I) (m : ℕ)
    (b : Old D Sc cutoff v v) (g : hom D Sc cutoff v v) :
    dottedOutputQuotientRow D Sc cutoff p i v m b ((ideal D Sc cutoff v v).mkQ g) =
      dottedOutputRow D Sc cutoff p i v m b g := rfl

/-- Two-sided comparison, with arbitrary full old quotients on both sides. -/
theorem dottedOutputQuotientRow_comparison (p : ZMod 2) (i : I) (v : List I)
    (m n : ℕ) (b c : Old D Sc cutoff v v) :
    dottedOutputQuotientRow D Sc cutoff p i v m b c n =
    outputLongCoordinate D Sc cutoff p i v n
      (pair D Sc cutoff p i (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v)
        (oldComp D Sc cutoff v v v b
          (oldTwist D Sc cutoff
            (p + ((m : ZMod 2) * D.parity i + D.parity i * wordSumParity D v)) v v c))) := by
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  exact dotted_bareU_pair_coordinate D Sc cutoff p i v m n b g

theorem tail_long_zero (i : I) (v : List I) :
    HEq (prependTail D Sc (longOutputIndex i v 0)) (OutputOldComposite.bareU D Sc i v) := by
  have transport {s s' t : List I} (e : s = s') {gs gs' : List PG} (eg : gs = gs')
      (h : SChain s (pl s gs) t) (h' : SChain s' (pl s' gs') t) :
      HEq (cl D Sc s t gs h) (cl D Sc s' t gs' h') := by
    subst s'; subst gs'; rfl
  apply transport (congrArg (List.cons i) (longOutputIndex_oldTarget i v 0))
  change (List.replicate 0 0).map PG.dot ++
    cw (Categorification.TypeA.canWord (v.length+1) (longPrependShuffle v.length).1⁻¹) =
      cw (leadingMoveWord [] v)
  simp only [List.replicate_zero, List.map_nil, List.nil_append,
    canWord_longPrependShuffle, leadingMoveWord_eq_descRun, List.length_nil]

theorem tail_long (i : I) (v : List I) (m : ℕ) :
    HEq (prependTail D Sc (longOutputIndex i v m))
      ((dotE D Sc (i :: v) 0 ^ m) ≫ OutputOldComposite.bareU D Sc i v) := by
  have hs := prependTail_shift D Sc (longOutputIndex i v 0) m
  change (dotE D Sc (i :: (longOutputIndex i v 0).oldTarget) 0 ^ m) ≫
    prependTail D Sc (longOutputIndex i v 0) = prependTail D Sc (longOutputIndex i v m) at hs
  rw [← hs]
  have transport {t t' : List I} (e : t = t')
      (f : (pres D Sc).obj (ob D (i :: t)) ⟶ (pres D Sc).obj (ob D (v ++ [i])))
      (g : (pres D Sc).obj (ob D (i :: t')) ⟶ (pres D Sc).obj (ob D (v ++ [i])))
      (h : HEq f g) : HEq ((dotE D Sc (i :: t) 0 ^ m) ≫ f)
        ((dotE D Sc (i :: t') 0 ^ m) ≫ g) := by
    subst t'; cases h; rfl
  exact transport (longOutputIndex_oldTarget i v 0) _ _ (tail_long_zero D Sc i v)

theorem pair_long (p : ZMod 2) (i : I) (v : List I) (m : ℕ)
    (b : Old D Sc cutoff v (longOutputIndex i v m).oldTarget) :
    pair D Sc cutoff p i
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        prependTail D Sc (longOutputIndex i v m)) b =
    pair D Sc cutoff p i (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v)
      (Eq.mp (congrArg (Old D Sc cutoff v) (longOutputIndex_oldTarget i v m)) b) := by
  have transport {t t' : List I} (e : t = t')
      (f : (pres D Sc).obj (ob D (i :: t)) ⟶ (pres D Sc).obj (ob D (v ++ [i])))
      (g : (pres D Sc).obj (ob D (i :: t')) ⟶ (pres D Sc).obj (ob D (v ++ [i])))
      (h : HEq f g) (b : Old D Sc cutoff v t) :
      pair D Sc cutoff p i ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] f) b =
        pair D Sc cutoff p i
          ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] g)
          (Eq.mp (congrArg (Old D Sc cutoff v) e) b) := by
    subst t'; cases h; rfl
  rw [transport (longOutputIndex_oldTarget i v m) _ _ (tail_long D Sc i v m) b]
  apply congrArg (fun h => pair D Sc cutoff p i h
    (Eq.mp (congrArg (Old D Sc cutoff v) (longOutputIndex_oldTarget i v m)) b))
  exact affineUnit_comp D Sc cutoff _ _

theorem output_coordinate_cast (p : ZMod 2) (i : I) (v : List I) (n : ℕ)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    outputLongCoordinate D Sc cutoff p i v n z =
      (SKM.zsign k (D.parity i * wordSumParity D v)) ^ n •
      Eq.mp (congrArg (Old D Sc cutoff v) (longOutputIndex_oldTarget i v n))
        (prependOldCoordinate D Sc cutoff p (longOutputIndex i v n) z) := by
  have transport {t t' : List I} (e : t = t')
      (f : Target D Sc cutoff i v (v ++ [i]) →ₗ[k] Old D Sc cutoff v t) (a : k) :
      (Eq.mp (congrArg (fun t => Target D Sc cutoff i v (v ++ [i]) →ₗ[k]
        Old D Sc cutoff v t) e) (a • f)) z =
        a • Eq.mp (congrArg (Old D Sc cutoff v) e) (f z) := by
    subst t'; rfl
  exact transport (longOutputIndex_oldTarget i v n) _ _

theorem coordinate_long_row (p : ZMod 2) (i : I) (v : List I) (m n : ℕ)
    (b : Old D Sc cutoff v v) :
    outputLongCoordinate D Sc cutoff p i v n
      (pair D Sc cutoff p i (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v) b) =
      if n = m then (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m • b else 0 := by
  let b' : Old D Sc cutoff v (longOutputIndex i v m).oldTarget :=
    Eq.mpr (congrArg (Old D Sc cutoff v) (longOutputIndex_oldTarget i v m)) b
  have hp := pair_long D Sc cutoff p i v m b'
  have hb : Eq.mp (congrArg (Old D Sc cutoff v) (longOutputIndex_oldTarget i v m)) b' = b := by
    simp [b']
  rw [hb] at hp
  rw [← hp, output_coordinate_cast]
  by_cases hn : n = m
  · subst n
    rw [prependOldCoordinate_pair, hb, ite_eq_left rfl]
  · rw [prependOldCoordinate_pair_off D Sc cutoff p (longOutputIndex i v n)
      (longOutputIndex i v m) (fun h => hn (congrArg Prod.fst h)), ite_eq_right hn]
    have cast_zero {t t' : List I} (e : t = t') :
        Eq.mp (congrArg (Old D Sc cutoff v) e) 0 = 0 := by subst t'; rfl
    rw [cast_zero (longOutputIndex_oldTarget i v n), smul_zero]

def outputLongSection (p : ZMod 2) (i : I) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] Target D Sc cutoff i v (v ++ [i]) :=
  Finsupp.lsum k fun m => (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m •
    pair D Sc cutoff p i (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v)

theorem coordinate_section (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) (n : ℕ) :
    outputLongCoordinate D Sc cutoff p i v n (outputLongSection D Sc cutoff p i v f) = f n := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]
  | single m b =>
    simp only [outputLongSection, Finsupp.lsum_single, LinearMap.smul_apply, map_smul,
      coordinate_long_row]
    by_cases hn : n = m
    · subst n
      simp only [ite_true, smul_smul, ← mul_pow, SKM.zsign_mul_self',
        one_pow, one_smul, Finsupp.single_eq_same]
    · rw [ite_eq_right hn, smul_zero, Finsupp.single_eq_of_ne hn]

theorem coordinate_act_long_row (p : ZMod 2) (i : I) (v : List I) (m n : ℕ)
    (b : Old D Sc cutoff v v) (g : hom D Sc cutoff v v) :
    outputLongCoordinate D Sc cutoff p i v n
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g)
        (pair D Sc cutoff p i (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v) b)) =
    oldComp D Sc cutoff v v v
      (outputLongCoordinate D Sc cutoff p i v n
        (pair D Sc cutoff p i (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v) b))
      (oldTwist D Sc cutoff (p + ((n : ZMod 2) * D.parity i + D.parity i * wordSumParity D v)) v v
        ((ideal D Sc cutoff v v).mkQ g)) := by
  rw [dotted_bareU_pair_coordinate, coordinate_long_row, coordinate_long_row]
  by_cases hn : n = m
  · subst n
    simp only [ite_true, map_smul, LinearMap.smul_apply]
  · simp only [ite_eq_right hn, map_zero, LinearMap.zero_apply]

theorem coordinate_act_section (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) (n : ℕ) (g : hom D Sc cutoff v v) :
    outputLongCoordinate D Sc cutoff p i v n
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g)
        (outputLongSection D Sc cutoff p i v f)) =
    oldComp D Sc cutoff v v v (f n)
      (oldTwist D Sc cutoff (p + ((n : ZMod 2) * D.parity i + D.parity i * wordSumParity D v)) v v
        ((ideal D Sc cutoff v v).mkQ g)) := by
  rw [← coordinate_section D Sc cutoff p i v f n]
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add f h hf hh => simp only [map_add, hf, hh, LinearMap.add_apply]
  | single m b =>
    simp only [outputLongSection, Finsupp.lsum_single, LinearMap.smul_apply, map_smul,
      coordinate_act_long_row]

/-- Canonical output old action on every degree of every quotient element. -/
theorem outputLongCoordinate_outputOld (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) (n : ℕ) (g : hom D Sc cutoff v v) :
    outputLongCoordinate D Sc cutoff p i v n
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) z) =
    oldComp D Sc cutoff v v v (outputLongCoordinate D Sc cutoff p i v n z)
      (oldTwist D Sc cutoff (p + ((n : ZMod 2) * D.parity i + D.parity i * wordSumParity D v)) v v
        ((ideal D Sc cutoff v v).mkQ g)) := by
  have he : outputLongExtraction D Sc cutoff p i v z =
      outputLongExtraction D Sc cutoff p i v
        (outputLongSection D Sc cutoff p i v (outputLongExtraction D Sc cutoff p i v z)) := by
    ext m
    exact (coordinate_section D Sc cutoff p i v _ m).symm
  have ha := outputLongExtraction_act_appendInsert_congr D Sc cutoff p i v g he
  have hn := congrArg (fun f : ℕ →₀ Old D Sc cutoff v v => f n) ha
  exact hn.trans (coordinate_act_section D Sc cutoff p i v _ n g)

/-- Finite extraction after the actual output old arrow. -/
def outputOldExtractionHom (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    hom D Sc cutoff v v →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) where
  toFun g := outputLongExtraction D Sc cutoff p i v
    (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) z)
  map_add' g h := by
    obtain ⟨r, rfl⟩ := projection_surjective D Sc cutoff i v (v ++ [i]) z
    simp only [map_add]
    change outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i]) (r ≫ (_ + _))) = _
    rw [Preadditive.comp_add, map_add, map_add]
    rfl
  map_smul' a g := by
    obtain ⟨r, rfl⟩ := projection_surjective D Sc cutoff i v (v ++ [i]) z
    simp only [map_smul]
    change outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i]) (r ≫ (a • _))) = _
    rw [Linear.comp_smul, map_smul, map_smul]
    rfl

theorem outputOldExtractionHom_ideal (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) {g : hom D Sc cutoff v v}
    (hg : g ∈ ideal D Sc cutoff v v) : outputOldExtractionHom D Sc cutoff p i v z g = 0 := by
  ext n
  change outputLongCoordinate D Sc cutoff p i v n _ = 0
  rw [outputLongCoordinate_outputOld]
  have hg' : (ideal D Sc cutoff v v).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).mpr hg
  rw [hg', map_zero, map_zero]

/-- Output quotient factor descended from actual arrow action, for arbitrary z. -/
def outputOldExtraction (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) :
    Old D Sc cutoff v v →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  (ideal D Sc cutoff v v).liftQ (outputOldExtractionHom D Sc cutoff p i v z)
    (fun _ hg => outputOldExtractionHom_ideal D Sc cutoff p i v z hg)

@[simp] theorem outputOldExtraction_mk (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) (g : hom D Sc cutoff v v) :
    outputOldExtraction D Sc cutoff p i v z ((ideal D Sc cutoff v v).mkQ g) =
      outputLongExtraction D Sc cutoff p i v
        (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) z) := rfl

theorem outputOldExtraction_coordinate (p : ZMod 2) (i : I) (v : List I)
    (z : Target D Sc cutoff i v (v ++ [i])) (n : ℕ) (c : Old D Sc cutoff v v) :
    outputOldExtraction D Sc cutoff p i v z c n =
      oldComp D Sc cutoff v v v (outputLongCoordinate D Sc cutoff p i v n z)
        (oldTwist D Sc cutoff
          (p + D.parity i * wordSumParity D v + (n : ZMod 2) * D.parity i) v v c) := by
  obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  rw [outputOldExtraction_mk, outputLongExtraction_apply]
  simpa only [add_comm, add_left_comm, add_assoc] using
    outputLongCoordinate_outputOld D Sc cutoff p i v z n g

/-- Two-sided balanced output-order comparison, all degrees and both full old quotients. -/
theorem outputLongCoordinate_twoSided_balanced (p : ZMod 2) (i : I) (v : List I) (n : ℕ)
    (h : hom D Sc cutoff (i :: v) (v ++ [i])) (b c : Old D Sc cutoff v v) :
    outputOldExtraction D Sc cutoff p i v
      (balancedForward D Sc cutoff p i v (v ++ [i]) (balancedTmul D Sc cutoff p i h b)) c n =
    oldComp D Sc cutoff v v v
      (oldComp D Sc cutoff v v v b
        (outputLongCoordinate D Sc cutoff p i v n (projection D Sc cutoff i v (v ++ [i]) h)))
      (oldTwist D Sc cutoff
        (p + D.parity i * wordSumParity D v + (n : ZMod 2) * D.parity i) v v c) := by
  rw [outputOldExtraction_coordinate, outputLongCoordinate_balanced]


end OddMath.QuiverHecke.ELVOld

noncomputable section
open CategoryTheory StringDiagrams Supercategory Categorification.TypeA
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem canonical_last_commute (i : I) (v : List I) (m : ℕ)
    (g : hom D Sc cutoff v v) :
    appendInsert D Sc cutoff i v v g ≫ appendMovingPower D Sc cutoff i v m =
      appendMovingPower D Sc cutoff i v m ≫
        appendInsert D Sc cutoff i v v (twist k ((m : ZMod 2) * D.parity i) g) := by
  symm
  change appendMovingPower D Sc cutoff i v m ≫ rightContext D Sc cutoff [i] v v _ =
    rightContext D Sc cutoff [i] v v g ≫ appendMovingPower D Sc cutoff i v m
  rw [appendMovingPower_whisker, trailing_comp_rightContext D Sc cutoff
    (firstDot_pow_parity D Sc i [] m)]
  simp only [nsmul_eq_mul, twist_twist]

theorem canonical_pure_compare (p : ZMod 2) (i : I) (v : List I) (m n : ℕ) :
    outputLongCoordinate D Sc cutoff p i v n
      (projection D Sc cutoff i v (v ++ [i])
        (bareUFull D Sc cutoff i v ≫ appendMovingPower D Sc cutoff i v m)) =
    (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m •
    outputLongCoordinate D Sc cutoff p i v n
      (projection D Sc cutoff i v (v ++ [i])
        (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v)) := by
  have hw : cw (canWord (v.length + 1) (longPrependShuffle v.length).1⁻¹) =
      cw (leadingMoveWord [] v) := by
    rw [canWord_longPrependShuffle, leadingMoveWord_eq_descRun]
    rfl
  have hu : SChain (i :: v)
      (pl (i :: v) (cw (canWord (v.length + 1) (longPrependShuffle v.length).1⁻¹)))
      (v ++ [i]) := by
    rw [hw]
    exact leadingMoveWord_sChain i [] v
  have hd := sChain_dot_pow (v ++ [i]) v.length m
  have h := sChain_append_of hu hd
  rw [← List.map_replicate] at h
  obtain ⟨h', he⟩ := prependOldCoordinate_long_last_dots D Sc cutoff p i v (v ++ [i]) 1 m h
  have hcl : cl D Sc _ _ _ h =
      OutputOldComposite.bareU D Sc i v ≫ dotE D Sc (v ++ [i]) v.length ^ m := by
    simp only [OutputOldComposite.bareU, dotE_pow, cl_comp, List.map_replicate, hw]
  have hcl' : cl D Sc _ _ _ h' =
      (dotE D Sc (i :: v) 0 ^ m) ≫ OutputOldComposite.bareU D Sc i v := by
    simp only [OutputOldComposite.bareU, dotE_pow, cl_comp, List.map_replicate, hw]
  have hn := he (longOutputIndex i v n) rfl
  rw [hcl, hcl'] at hn
  have hc : bareUFull D Sc cutoff i v ≫ appendMovingPower D Sc cutoff i v m =
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        (OutputOldComposite.bareU D Sc i v ≫ dotE D Sc (v ++ [i]) v.length ^ m) :=
    (affineUnit_comp D Sc cutoff _ _).symm
  have hc' : movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v =
      (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        ((dotE D Sc (i :: v) 0 ^ m) ≫ OutputOldComposite.bareU D Sc i v) :=
    (affineUnit_comp D Sc cutoff _ _).symm
  have hn' : prependOldCoordinate D Sc cutoff p (longOutputIndex i v n)
      (projection D Sc cutoff i v (v ++ [i])
        (bareUFull D Sc cutoff i v ≫ appendMovingPower D Sc cutoff i v m)) =
      (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m •
      prependOldCoordinate D Sc cutoff p (longOutputIndex i v n)
        (projection D Sc cutoff i v (v ++ [i])
          (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v)) := by
    rw [hc, hc']
    exact hn
  rw [output_coordinate_cast, output_coordinate_cast, hn']
  have cast_smul {t t' : List I} (e : t = t') (a : k) (b : Old D Sc cutoff v t) :
      Eq.mp (congrArg (Old D Sc cutoff v) e) (a • b) =
        a • Eq.mp (congrArg (Old D Sc cutoff v) e) b := by subst t'; rfl
  rw [cast_smul (longOutputIndex_oldTarget i v n), smul_comm]

theorem canonical_pair_compare (p : ZMod 2) (i : I) (v : List I) (m n : ℕ)
    (b : Old D Sc cutoff v v) :
    outputLongCoordinate D Sc cutoff p i v n
      (pair D Sc cutoff p i (bareUFull D Sc cutoff i v ≫ appendMovingPower D Sc cutoff i v m) b) =
    (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m •
    outputLongCoordinate D Sc cutoff p i v n
      (pair D Sc cutoff p i (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v) b) := by
  have hb (h : hom D Sc cutoff (i :: v) (v ++ [i])) :=
    outputLongCoordinate_balanced D Sc cutoff p i v n h b
  simp only [balancedForward_tmul] at hb
  rw [hb, hb, canonical_pure_compare, map_smul]

theorem canonical_pair_monomial (p : ZMod 2) (i : I) (v : List I) (m n : ℕ)
    (b : Old D Sc cutoff v v) :
    outputLongCoordinate D Sc cutoff p i v n
      (pair D Sc cutoff p i (bareUFull D Sc cutoff i v ≫ appendMovingPower D Sc cutoff i v m) b) =
      if n = m then b else 0 := by
  rw [canonical_pair_compare, coordinate_long_row]
  split_ifs
  · rw [smul_smul, ← mul_pow, SKM.zsign_mul_self', one_pow, one_smul]
  · rw [smul_zero]

/-- Literal chronological U, output old arrow, then last dots. -/
theorem canonical_output_monomial (p : ZMod 2) (i : I) (v : List I) (m n : ℕ)
    (b c : Old D Sc cutoff v v) (g : hom D Sc cutoff v v)
    (hg : (ideal D Sc cutoff v v).mkQ g = c) :
    outputLongCoordinate D Sc cutoff p i v n
      (pair D Sc cutoff p i
        ((bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v v g) ≫
          appendMovingPower D Sc cutoff i v m) b) =
      if n = m then oldComp D Sc cutoff v v v b
        (oldTwist D Sc cutoff (p + D.parity i * wordSumParity D v) v v c) else 0 := by
  rw [Category.assoc, canonical_last_commute, ← Category.assoc]
  have hp (h : hom D Sc cutoff (i :: v) (v ++ [i])) (f : hom D Sc cutoff v v) :
      pair D Sc cutoff p i (h ≫ appendInsert D Sc cutoff i v v f) b =
        act D Sc cutoff i (appendInsert D Sc cutoff i v v f) (pair D Sc cutoff p i h b) := by
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective b
    simp only [pair_mk]
    change projection D Sc cutoff i v (v ++ [i]) (_ ≫ (_ ≫ _)) =
      projection D Sc cutoff i v (v ++ [i]) ((_ ≫ _) ≫ _)
    rw [Category.assoc]
  rw [hp, outputLongCoordinate_outputOld, canonical_pair_monomial]
  by_cases hn : n = m
  · subst n
    simp only [ite_true]
    have ht : (ideal D Sc cutoff v v).mkQ (twist k ((m : ZMod 2) * D.parity i) g) =
        oldTwist D Sc cutoff ((m : ZMod 2) * D.parity i) v v c := by rw [← hg]; rfl
    rw [ht]
    congr 1
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
    change (ideal D Sc cutoff v v).mkQ (twist k _ (twist k _ r)) =
      (ideal D Sc cutoff v v).mkQ (twist k _ r)
    have hpar : p + ((m : ZMod 2) * D.parity i + D.parity i * wordSumParity D v) =
        (p + D.parity i * wordSumParity D v) + (m : ZMod 2) * D.parity i := by abel
    rw [hpar, twist_add, twist_twist]
  · simp only [ite_eq_right hn, map_zero, LinearMap.zero_apply]

theorem canonical_output_balanced (p : ZMod 2) (i : I) (v : List I) (m n : ℕ)
    (b c : Old D Sc cutoff v v) (g : hom D Sc cutoff v v)
    (hg : (ideal D Sc cutoff v v).mkQ g = c) :
    outputLongCoordinate D Sc cutoff p i v n
      (balancedForward D Sc cutoff p i v (v ++ [i])
        (balancedTmul D Sc cutoff p i
          ((bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v v g) ≫
            appendMovingPower D Sc cutoff i v m) b)) =
      if n = m then oldComp D Sc cutoff v v v b
        (oldTwist D Sc cutoff (p + D.parity i * wordSumParity D v) v v c) else 0 := by
  rw [balancedForward_tmul]
  exact canonical_output_monomial D Sc cutoff p i v m n b c g hg

theorem canonical_output_extraction (p : ZMod 2) (i : I) (v : List I) (m : ℕ)
    (b c : Old D Sc cutoff v v) (g : hom D Sc cutoff v v)
    (hg : (ideal D Sc cutoff v v).mkQ g = c) :
    outputLongExtraction D Sc cutoff p i v
      (pair D Sc cutoff p i
        ((bareUFull D Sc cutoff i v ≫ appendInsert D Sc cutoff i v v g) ≫
          appendMovingPower D Sc cutoff i v m) b) =
      Finsupp.single m (oldComp D Sc cutoff v v v b
        (oldTwist D Sc cutoff (p + D.parity i * wordSumParity D v) v v c)) := by
  ext n
  rw [outputLongExtraction_apply, canonical_output_monomial D Sc cutoff p i v m n b c g hg]
  by_cases hn : n = m
  · subst n; simp only [ite_true, Finsupp.single_eq_same]
  · rw [ite_eq_right hn, Finsupp.single_eq_of_ne hn]
end OddMath.QuiverHecke.ELVOld
