import OddMath.QuiverHecke.CyclotomicAction.OutputTransport
import OddMath.QuiverHecke.CyclotomicAction.LeadingMove

/-!
# Leading source transport

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
namespace OddMath.QuiverHecke.ELV
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

/-- Auxiliary dotted-row section for the output-order comparison. -/
def outputOrderSection (p : ZMod 2) (i : I) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] Target D Sc cutoff i v (v ++ [i]) :=
  Finsupp.lsum k fun m => (SKM.zsign k (D.parity i * wordSumParity D v)) ^ m •
    pair D Sc cutoff p i (movingPower D Sc cutoff i v m ≫ bareUFull D Sc cutoff i v)

theorem coordinate_section (p : ZMod 2) (i : I) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) (n : ℕ) :
    outputLongCoordinate D Sc cutoff p i v n (outputOrderSection D Sc cutoff p i v f) = f n := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg]
  | single m b =>
    simp only [outputOrderSection, Finsupp.lsum_single, LinearMap.smul_apply, map_smul,
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
        (outputOrderSection D Sc cutoff p i v f)) =
    oldComp D Sc cutoff v v v (f n)
      (oldTwist D Sc cutoff (p + ((n : ZMod 2) * D.parity i + D.parity i * wordSumParity D v)) v v
        ((ideal D Sc cutoff v v).mkQ g)) := by
  rw [← coordinate_section D Sc cutoff p i v f n]
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | add f h hf hh => simp only [map_add, hf, hh, LinearMap.add_apply]
  | single m b =>
    simp only [outputOrderSection, Finsupp.lsum_single, LinearMap.smul_apply, map_smul,
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
        (outputOrderSection D Sc cutoff p i v (outputLongExtraction D Sc cutoff p i v z)) := by
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

end OddMath.QuiverHecke.ELV

noncomputable section
open CategoryTheory StringDiagrams Supercategory Categorification.TypeA
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV
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
end OddMath.QuiverHecke.ELV
end
end

end

section

/-!
# Leading-source monomials for the output boundary

Hom-level source-dot separation for the ordered-product comparison in
`DeformedMackeyBoundary.md` (2), without a finite colour-type assumption.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory Supercategory
open scoped TensorProduct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
local notation "O[" w "]" => Presentation.obj (pres D Sc) (ob D w)

private theorem source_dot_cons (w : List I) (p : ℕ) (ps : List ℕ) :
    endpointDotMonomial D Sc w (p :: ps) =
      dotE D Sc w p ≫ endpointDotMonomial D Sc w ps := by
  rw [dotE_eq_cl D Sc (sChain_dotAny w p)]
  unfold endpointDotMonomial
  rw [cl_comp]
  rfl

private theorem left_dot_interchange {A B : (pres D Sc).Presented}
    {q : ZMod 2} {x : End A} (hx : x ∈ parity (R := k) A A q) (f : End B) :
    x ▷ B ≫ A ◁ f = A ◁ twist k q f ≫ x ▷ B := by
  refine Supercategory.induction_on (R := k) f ?_ (fun r g hg => ?_)
    (fun f g hf hg => ?_)
  · simp only [map_zero, MonoidalSupercategory.whiskerLeft_zero (R := k),
      Limits.comp_zero, Limits.zero_comp]
  · rw [twist_of_mem _ hg, MonoidalSupercategory.whiskerLeft_smul (R := k),
      Linear.smul_comp, MonoidalSupercategory.super_interchange hx hg,
      koszulSign_smul (R := k)]
  · simp only [map_add, MonoidalSupercategory.whiskerLeft_add (R := k),
      Preadditive.comp_add, Preadditive.add_comp, hf, hg]

private theorem first_dot_old (i : I) (v : List I) (f : End O[v]) :
    dotE D Sc (i :: v) 0 ≫ O[[i]] ◁ f =
      O[[i]] ◁ twist k (D.parity i) f ≫ dotE D Sc (i :: v) 0 := by
  have hd : dotE D Sc (i :: v) 0 = (inductionStrandDot D Sc i ▷ O[v]) :=
    (inductionFirstDot_eq_dotE D Sc i ⟨v, rfl⟩).symm
  rw [hd]
  exact left_dot_interchange D Sc (inductionStrandDot_parity D Sc i) f

/-- Hom-valued source separation, with the source-category object family fixed. -/
def separatedSourceOldHom (i : I) (v : List I) : List ℕ → End O[v]
  | [] => 𝟙 _
  | 0 :: ps => twist k (D.parity i) (separatedSourceOldHom i v ps)
  | (p + 1) :: ps => dotE D Sc v p ≫ separatedSourceOldHom i v ps

/-- Exact Hom separation of source dots, retaining every old parity twist. -/
theorem endpointDotMonomial_separate_hom (i : I) (v : List I) (ps : List ℕ) :
    endpointDotMonomial D Sc (i :: v) ps =
      O[[i]] ◁ separatedSourceOldHom D Sc i v ps ≫
        dotE D Sc (i :: v) 0 ^ sourceMovingDegree ps := by
  induction ps with
  | nil =>
    simp only [separatedSourceOldHom, sourceMovingDegree, pow_zero, End.one_def,
      MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp]
    exact cl_nil D Sc (i :: v) rfl
  | cons p ps ih =>
    rw [source_dot_cons, ih]
    cases p with
    | zero =>
      rw [← Category.assoc, first_dot_old, Category.assoc]
      simp only [separatedSourceOldHom, sourceMovingDegree, pow_succ, End.mul_def]
    | succ p =>
      rw [← whiskerLeft_letter_dotE D Sc i v p, ← Category.assoc]
      simp only [separatedSourceOldHom, sourceMovingDegree,
        MonoidalSupercategory.whiskerLeft_comp (R := k)]

/-- Separation signs cancel on the independently specified square-product terms. -/
theorem separatedSourceOldHom_leading (i : I) (v μ : List I) (a : ℕ)
    (c : MoveChoices μ) :
    separatedSourceOldHom D Sc i v (leadingSourceDots D i 0 a μ c) =
      endpointDotMonomial D Sc v (sourceOldDots (leadingSourceDots D i 0 a μ c)) := by
  induction μ generalizing a with
  | nil => exact (cl_nil D Sc v rfl).symm
  | cons j μ ih =>
    rcases c with ⟨b, c⟩
    by_cases hij : i = j
    · subst j
      rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
      all_goals
        fin_cases b <;>
          simp [leadingSourceDots, leadingSourceBlockDots, hi, sourceOldDots,
            separatedSourceOldHom, source_dot_cons, twist_twist, ih]
    · simp [leadingSourceDots, leadingSourceBlockDots, hij, ih]

/-- A leading source monomial has its independently computed old dot factor. -/
theorem leadingSourceDots_separate_hom (i : I) (v : List I) (c : MoveChoices v) :
    endpointDotMonomial D Sc (i :: v) (leadingSourceDots D i 0 0 v c) =
      O[[i]] ◁ endpointDotMonomial D Sc v
        (sourceOldDots (leadingSourceDots D i 0 0 v c)) ≫
      dotE D Sc (i :: v) 0 ^ sourceMovingDegree (leadingSourceDots D i 0 0 v c) := by
  rw [endpointDotMonomial_separate_hom, separatedSourceOldHom_leading]

namespace ELV
variable (cutoff : I → ℕ)

/-- The old affine dot monomial specified by a choice in the ordered product. -/
def leadingSourceOldArrow (i : I) (v : List I) (c : MoveChoices v) : hom D Sc cutoff v v :=
  affineUnit D Sc cutoff v v
    (endpointDotMonomial D Sc v (sourceOldDots (leadingSourceDots D i 0 0 v c)))

/-- Every old twist fixes the independent old dot monomial, also in full ELV. -/
theorem leadingSourceOldArrow_twist (i : I) (v : List I) (c : MoveChoices v) (q : ZMod 2) :
    twist k q (leadingSourceOldArrow D Sc cutoff i v c) =
      leadingSourceOldArrow D Sc cutoff i v c := by
  unfold leadingSourceOldArrow
  rw [← affineUnit_twist]
  congr 1
  exact leadingMoveOldDots_twist D Sc i v c q

private theorem leading_degree_sign (i : I) (v : List I) (c : MoveChoices v) (q : ZMod 2) :
    (SKM.zsign k (D.parity i * q)) ^
      sourceMovingDegree (leadingSourceDots D i 0 0 v c) = 1 := by
  rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
  · simp [hi, SKM.zsign]
  · have he := sourceMovingDegree_leadingSourceDots_even D i hi 0 v c
    have hd : Even (sourceMovingDegree (leadingSourceDots D i 0 0 v c)) :=
      Nat.even_iff.mpr he
    unfold SKM.zsign
    split_ifs
    · exact hd.neg_one_pow
    · simp

private theorem leading_source_pair (p : ZMod 2) (i : I) (v : List I) (c : MoveChoices v) :
    projection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff (i :: v) (v ++ [i])
        (endpointDotMonomial D Sc (i :: v) (leadingSourceDots D i 0 0 v c) ≫
          OutputOldComposite.bareU D Sc i v)) =
    pair D Sc cutoff p i
      (movingPower D Sc cutoff i v (sourceMovingDegree (leadingSourceDots D i 0 0 v c)) ≫
        bareUFull D Sc cutoff i v)
      ((ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c)) := by
  rw [pair_mk, leadingSourceOldArrow_twist, leadingSourceDots_separate_hom,
    Category.assoc]
  congr 1
  rw [leadingSourceOldArrow, insert_affineUnit]
  change affineUnit D Sc cutoff _ _ (_ ≫ (_ ≫ _)) =
    affineUnit D Sc cutoff _ _ _ ≫
      (affineUnit D Sc cutoff _ _ _ ≫ affineUnit D Sc cutoff _ _ _)
  rw [affineUnit_comp, affineUnit_comp]
  rfl

/-- Input-to-output transport of an independent leading source monomial, modulo
exact chronological short span, not total crossing length. -/
theorem leading_source_output_transport (i : I) (v : List I) (c : MoveChoices v) :
    projection D Sc cutoff i v (v ++ [i])
      (affineUnit D Sc cutoff (i :: v) (v ++ [i])
        (endpointDotMonomial D Sc (i :: v) (leadingSourceDots D i 0 0 v c) ≫
          OutputOldComposite.bareU D Sc i v) -
        ((bareUFull D Sc cutoff i v ≫
          appendInsert D Sc cutoff i v v (leadingSourceOldArrow D Sc cutoff i v c)) ≫
          appendMovingPower D Sc cutoff i v
            (sourceMovingDegree (leadingSourceDots D i 0 0 v c)))) ∈
      chronologicalShortSpan D Sc cutoff i v v := by
  rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff 0 i v]
  change outputLongExtraction D Sc cutoff 0 i v _ = 0
  rw [map_sub, map_sub, sub_eq_zero]
  ext n
  rw [outputLongExtraction_apply, outputLongExtraction_apply, leading_source_pair,
    coordinate_long_row, leading_degree_sign]
  rw [← pair_id D Sc cutoff 0 i,
    canonical_output_monomial D Sc cutoff 0 i v _ n _ _ _ rfl]
  split_ifs
  · rw [one_smul]
    change (ideal D Sc cutoff v v).mkQ _ =
      (ideal D Sc cutoff v v).mkQ (𝟙 _ ≫ twist k _ _)
    rw [Category.id_comp, leadingSourceOldArrow_twist]
  · rfl

/-- The canonical output extractor evaluates each independently specified
leading-source monomial. No transport premise is assumed. -/
theorem leading_source_output_extraction (p : ZMod 2) (i : I) (v : List I)
    (c : MoveChoices v) :
    outputLongExtraction D Sc cutoff p i v
      (projection D Sc cutoff i v (v ++ [i])
        (affineUnit D Sc cutoff (i :: v) (v ++ [i])
          (endpointDotMonomial D Sc (i :: v) (leadingSourceDots D i 0 0 v c) ≫
            OutputOldComposite.bareU D Sc i v))) =
      Finsupp.single (sourceMovingDegree (leadingSourceDots D i 0 0 v c))
        ((ideal D Sc cutoff v v).mkQ (leadingSourceOldArrow D Sc cutoff i v c)) := by
  have ht := leading_source_output_transport D Sc cutoff i v c
  rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v] at ht
  change outputLongExtraction D Sc cutoff p i v _ = 0 at ht
  rw [map_sub, map_sub, sub_eq_zero] at ht
  rw [ht, ← pair_id D Sc cutoff p i, canonical_output_extraction D Sc cutoff p i v _ _ _ _ rfl]
  congr 1
  change (ideal D Sc cutoff v v).mkQ (𝟙 _ ≫ twist k _ _) = _
  rw [Category.id_comp, leadingSourceOldArrow_twist]

end ELV
end OddMath.QuiverHecke
end

end

section

/-!
# The global sign of the ordered square product

The unsigned product `leadingMoveSquareProduct` is defined directly from square
differences, not from coefficients or an inverse coordinate map. Its factors are
in chronological order (earlier factors on the right in the endomorphism ring).
The library's endpoint polynomial is this product times one parity sign for each
old strand of the moving colour. No restriction on the other colours is needed.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Unsigned local square difference: odd colours use squared dots, even
colours use dots, and unequal colours contribute the identity. -/
def leadingSourceUnsignedSquare (t : List I) (i j : I) (m p : ℕ) :
    End ((pres D Sc).obj (ob D t)) :=
  if i = j then
    if D.parity i = 1 then (dotE D Sc t m ^ 2 - dotE D Sc t p ^ 2) ^ 2
    else (dotE D Sc t m - dotE D Sc t p) ^ 2
  else 1

/-- Independently prescribed unsigned ordered product at a fixed endpoint.
The old positions increase from `a + 1`, with earlier factors on the right. -/
def leadingSourceUnsignedProduct (t : List I) (i : I) (m : ℕ) : ℕ → List I →
    End ((pres D Sc).obj (ob D t))
  | _, [] => 1
  | a, j :: ν => leadingSourceUnsignedProduct t i m (a + 1) ν *
      leadingSourceUnsignedSquare D Sc t i j m (a + 1)

/-- The unsigned ordered `S` product on the original source word. -/
def leadingMoveSquareProduct (i : I) (l ν : List I) :
    End ((pres D Sc).obj (ob D (l ++ i :: ν))) :=
  leadingSourceUnsignedProduct D Sc (l ++ i :: ν) i l.length l.length ν

/-- A matching factor contributes exactly the library parity sign. -/
theorem leadingSourceSquare_eq_sign_smul (t : List I) (i j : I) (m p : ℕ) :
    leadingSourceSquare D Sc t i j m p =
      (if i = j then SKM.zsign k (D.parity i) else 1) •
        leadingSourceUnsignedSquare D Sc t i j m p := by
  by_cases hij : i = j
  · subst j
    by_cases hp : D.parity i = 1
    all_goals simp [leadingSourceSquare, leadingSourceUnsignedSquare, SKM.zsign, hp]
  · simp [leadingSourceSquare, leadingSourceUnsignedSquare, hij]

/-- Pulling out the local signs gives `(-1)^(parity(i) * count_i(ν))`.
The power of `zsign` expresses this without choosing an integer lift of parity. -/
theorem leadingSourceProduct_eq_sign_smul (t : List I) (i : I) (m a : ℕ)
    (ν : List I) :
    leadingSourceProduct D Sc t i m a ν =
      SKM.zsign k (D.parity i) ^ ν.count i •
        leadingSourceUnsignedProduct D Sc t i m a ν := by
  induction ν generalizing a with
  | nil => simp [leadingSourceProduct, leadingSourceUnsignedProduct]
  | cons j ν ih =>
    rw [leadingSourceProduct, leadingSourceUnsignedProduct, ih,
      leadingSourceSquare_eq_sign_smul]
    by_cases hij : i = j
    · subst j
      simp [pow_succ, smul_smul, mul_comm]
    · simp [hij, Ne.symm hij]

/-- The signed product equals the explicit global library sign times `S`. -/
theorem leadingMoveProduct_eq_sign_smul_squareProduct (i : I) (l ν : List I) :
    leadingMoveProduct D Sc i l ν =
      SKM.zsign k (D.parity i) ^ ν.count i • leadingMoveSquareProduct D Sc i l ν :=
  leadingSourceProduct_eq_sign_smul D Sc (l ++ i :: ν) i l.length l.length ν

/-- The endpoint polynomial equals the global sign times the independently
specified unsigned `S`, for arbitrary words and both parities. -/
theorem leadingMoveEndpointPolynomial_eq_sign_smul_squareProduct
    (i : I) (l ν : List I) :
    leadingMoveEndpointPolynomial D Sc i l ν =
      SKM.zsign k (D.parity i) ^ ν.count i • leadingMoveSquareProduct D Sc i l ν := by
  rw [leadingMoveEndpointPolynomial_eq_product,
    leadingMoveProduct_eq_sign_smul_squareProduct]

/-- Synthesizing the explicit finite coefficients as endpoint monomials gives
exactly the global sign times the unsigned product; no coordinate inverse is used. -/
theorem leadingSource_expansion_eq_sign_smul (t : List I) (i : I) (m a : ℕ)
    (ν : List I) :
    (∑ c : MoveChoices ν, leadingMoveCoeff D (k := k) i ν c •
      (show End ((pres D Sc).obj (ob D t)) from
        endpointDotMonomial D Sc t (leadingSourceDots D i m a ν c))) =
      SKM.zsign k (D.parity i) ^ ν.count i •
        leadingSourceUnsignedProduct D Sc t i m a ν := by
  rw [← leadingSourceProduct_expansion, leadingSourceProduct_eq_sign_smul]

end OddMath.QuiverHecke
end

end
