/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Envelope
import OddMath.SKM.EnvelopeSOp
import OddMath.SKM.MoreGenerators
import OddMath.SKM.DotSlides

/-!
# The generator assignments for ψ and its dot powers

The construction in the proof of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.4. The object and 1-morphism assignments fix
weights and words, adding `|i,λ|` to the parity shift of each downward strand.
The upward dot has coefficient `t` for odd colours, where `t² = -1`.

The dot-power formula is proved using composition in the actual super-opposite,
not by assuming preservation of the defining relations. The 2-superfunctor,
its remaining relation checks, extension and categorical inverse are not
constructed here. The calculation works over a purely even commutative ring;
the field assumption of §9 is not needed for this slice.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory
universe u v w

/-- The scalar in the upward dot and crossing assignments of Proposition 9.4. -/
def psiCoeff {k : Type w} [CommRing k] (t : k) (p : ZMod 2) : k :=
  if p = 0 then 1 else t

@[simp] theorem psiCoeff_zero {k : Type w} [CommRing k] (t : k) : psiCoeff t 0 = 1 := by
  simp [psiCoeff]

@[simp] theorem psiCoeff_one {k : Type w} [CommRing k] (t : k) : psiCoeff t 1 = t := by
  simp [psiCoeff]

/-- The square root cancels the Koszul sign in a composite of two odd factors. -/
theorem psiCoeff_comp {k : Type w} [CommRing k] {t : k} (ht : t ^ 2 = -1)
    (p q : ZMod 2) :
    sign k (p * q) * (psiCoeff t q * psiCoeff t p) = psiCoeff t (p + q) := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl <;>
    simp [psiCoeff, ← pow_two, ht, show (1 : ZMod 2) + 1 = 0 from rfl]

private theorem cpow_mem {k : Type w} [CommRing k] {C : Type*} [Category C]
    [Preadditive C] [Linear k C] [Supercategory k C] {A : C} {x : A ⟶ A}
    {p : ZMod 2} (hx : x ∈ parity (R := k) A A p) (n : ℕ) :
    cpow x n ∈ parity (R := k) A A (n * p) := by
  induction n with
  | zero => simpa using id_mem (R := k) A
  | succ n ih =>
    simpa only [cpow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using comp_mem ih hx

private theorem psi_cpow {k : Type w} [CommRing k] {C : Type*} [Category C]
    [Preadditive C] [Linear k C] [Supercategory k C] {A : C} {x : A ⟶ A}
    {p : ZMod 2} (hx : x ∈ parity (R := k) A A p) {t : k} (ht : t ^ 2 = -1) (n : ℕ) :
    SOp.unsop (cpow (SOp.sop (R := k) (psiCoeff t p • x)) n) =
      psiCoeff t (n * p) • cpow x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [cpow_succ, SOp.unsop_comp, ih, SOp.unsop_sop,
      SOp.smul_compC, SOp.compC_smul, SOp.compC_of_mem (cpow_mem hx n) hx,
      ← cpow_succ', smul_smul, smul_smul]
    rw [show psiCoeff t (n * p) * psiCoeff t p * sign k (n * p * p) =
      psiCoeff t ((n : ZMod 2) * p + p) by
        calc
          _ = sign k (n * p * p) * (psiCoeff t p * psiCoeff t (n * p)) := by ring
          _ = _ := psiCoeff_comp ht _ _]
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul]

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- The parity shift contributed by the downward strands of a well-formed word. -/
def psiParity {a b : UGr D Sc sy hc} (f : a ⟶ b) : ZMod 2 :=
  (f.obj.word.map fun c => if c.l.1 then 0 else ipar D c.l.2 c.r).sum

/-- The weight assignment for ψ. -/
def psiObj (a : UGr D Sc sy hc) : TwoSOp k (Uqπ D Sc sy hc) := ⟨⟨⟨a⟩⟩⟩

/-- The 1-morphism assignment for ψ, before verifying the 2-morphism relations. -/
def psiMap {a b : UGr D Sc sy hc} (f : a ⟶ b) : psiObj a ⟶ psiObj b :=
  ⟨⟨psiParity f, ⟨0, f⟩⟩⟩

@[simp] theorem psiParity_id (a : UGr D Sc sy hc) : psiParity (𝟙 a) = 0 := rfl

theorem psiParity_comp {a b c : UGr D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    psiParity (f ≫ g) = psiParity f + psiParity g := by
  change ((f.obj.word ++ g.obj.word).map _).sum = _
  simp [psiParity]

theorem psiMap_id (a : UGr D Sc sy hc) : psiMap (𝟙 a) = 𝟙 (psiObj a) := rfl

theorem psiMap_comp {a b c : UGr D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    psiMap (f ≫ g) = psiMap f ≫ psiMap g := by
  change SOp.mk (Envelope.mk (psiParity (f ≫ g)) (QEnvelope.mk 0 (f ≫ g))) = _
  rw [psiParity_comp]
  rfl

/-- A signed word as a 1-morphism in the existing graded presentation. -/
def psiWord (μ : X) (s : List (Letter I)) :
    (⟨(wt D μ s : X)⟩ : UGr D Sc sy hc) ⟶ ⟨μ⟩ where
  obj := ob D μ s
  start_eq := rfl
  wf := ok_wd D μ s
  endR_eq := ob_endR D μ s

@[simp] theorem psiParity_up (μ : X) (i : I) :
    psiParity (sy := sy) (hc := hc) (psiWord (Sc := Sc) μ [up i]) = 0 := rfl

@[simp] theorem psiParity_dn (μ : X) (i : I) :
    psiParity (sy := sy) (hc := hc) (psiWord (Sc := Sc) μ [dn i]) = ipar D i μ := by
  simp [psiParity, psiWord, ob, wd]

/-- The E-generator has zero parity and integer shifts. -/
theorem psiMap_up (μ : X) (i : I) :
    psiMap (sy := sy) (hc := hc) (psiWord (Sc := Sc) μ [up i]) =
      SOp.mk (Envelope.mk 0 (QEnvelope.mk 0 (psiWord (Sc := Sc) μ [up i]))) := rfl

/-- The F-generator acquires the weight-dependent parity shift. -/
theorem psiMap_dn (μ : X) (i : I) :
    psiMap (sy := sy) (hc := hc) (psiWord (Sc := Sc) μ [dn i]) =
      SOp.mk (Envelope.mk (ipar D i μ) (QEnvelope.mk 0 (psiWord (Sc := Sc) μ [dn i]))) := by
  unfold psiMap
  rw [psiParity_dn]

/-- The target of the upward dot assignment. -/
abbrev psiE (μ : X) (i : I) :=
  psiMap (sy := sy) (hc := hc) (psiWord (Sc := Sc) μ [up i])

/-- The dotted upward strand in the target envelope, with the printed coefficient. -/
def psiDots (t : k) (μ : X) (i : I) (n : ℕ) :
    psiE (Sc := Sc) (sy := sy) (hc := hc) μ i ⟶ psiE μ i :=
  SOp.mk' (psiCoeff t (n * D.parity i) • cl D Sc μ [up i] [up i] (dotsL [] i [] n))

/-- The single-dot assignment in the proof of Proposition 9.4. -/
abbrev psiDot (t : k) (μ : X) (i : I) :=
  psiDots (Sc := Sc) (sy := sy) (hc := hc) t μ i 1

private theorem psiEDot_mem (μ : X) (i : I) :
    (show SOp.unop (psiE (Sc := Sc) (sy := sy) (hc := hc) μ i) ⟶
      SOp.unop (psiE (Sc := Sc) (sy := sy) (hc := hc) μ i) from
      cl D Sc μ [up i] [up i] (dotsL [] i [] 1)) ∈
      parity (R := k) _ _ (D.parity i) := by
  change cl D Sc μ [up i] [up i] (dotsL [] i [] 1) ∈
    (pres D Sc).homDeg (Presentation.parityDeg (sig D)) _ _ (D.parity i + (0 + 0))
  unfold cl
  split_ifs
  · apply Presentation.diag_mem_homDeg'
    rw [degree_parity_mkD]
    simp only [parity_dotsL, Nat.cast_one, one_mul, add_zero]
  · exact Submodule.zero_mem _

private theorem psiEDot_pow (μ : X) (i : I) (n : ℕ) :
    cpow (show SOp.unop (psiE (Sc := Sc) (sy := sy) (hc := hc) μ i) ⟶
      SOp.unop (psiE (Sc := Sc) (sy := sy) (hc := hc) μ i) from
      cl D Sc μ [up i] [up i] (dotsL [] i [] 1)) n =
      cl D Sc μ [up i] [up i] (dotsL [] i [] n) := by
  induction n with
  | zero =>
    change 𝟙 ((pres D Sc).obj (ob D μ [up i])) = _
    simp [dotsL, cl_nil]
  | succ n ih =>
    rw [cpow_succ, ih]
    change cl D Sc μ [up i] [up i] (dotsL [] i [] n) ≫
      cl D Sc μ [up i] [up i] (dotsL [] i [] 1) = _
    rw [cl_dotsL_eq_pow (D := D) (Sc := Sc) (s := [up i]) μ [] i [] n rfl,
      cl_dotsL_eq_pow (D := D) (Sc := Sc) (s := [up i]) μ [] i [] (n + 1) rfl]
    rfl

/-- **Proposition 9.4, dot-power display:** the power of the assigned dot has
coefficient `1` or `t` according to the parity of `n|i|`. -/
theorem psiDot_power (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (n : ℕ) :
    cpow (psiDot (Sc := Sc) (sy := sy) (hc := hc) t μ i) n = psiDots t μ i n := by
  apply SOp.hom_ext
  change SOp.unsop (cpow (SOp.sop (psiCoeff t (1 * D.parity i) •
    (show (SOp.unop (psiE (Sc := Sc) (sy := sy) (hc := hc) μ i)) ⟶ _ from
      cl D Sc μ [up i] [up i] (dotsL [] i [] 1)))) n) = _
  rw [one_mul, psi_cpow (psiEDot_mem (Sc := Sc) (sy := sy) (hc := hc) μ i) ht]
  exact congrArg (psiCoeff t (n * D.parity i) • ·)
    (psiEDot_pow (Sc := Sc) (sy := sy) (hc := hc) μ i n)

end OddMath.SKM
