import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Preorder.Finite
import OddMath.QuiverHecke.CyclotomicAction.AppendMackey.AppendTensorRightDot
import OddMath.QuiverHecke.CyclotomicAction.SuperQuotient

/-!
# Append content

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

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
