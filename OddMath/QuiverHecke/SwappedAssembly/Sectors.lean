/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierShiftedAdjunction
import OddMath.SKM.RouquierMulticolour

/-! # Probe and reservoir sectors of the swapped Hom categories

The swapped Hom construction of `docs/Nondegeneracy/SwappedActionAssembly.md`, §1, (A1)–(A3),
for the presentation of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5.

`ProbeReservoir` packages the probe `T` (on the precomposition side, with its shifted left
adjunctions) and the reservoir `W` (on the postcomposition side), both satisfying the
multicolour relations, together with the two highest weights `ΛP`, `ΛR`.

A *sector* is a pair `(b, c)` of formal contents (probe content `b`, reservoir content `c`).
Its Hom category is `H (b, c) = T (-(ΛP - α(b))) ⟶ W (-ΛR + α(c))`, of weight
`ΛP - ΛR - α(b) + α(c)`. Formal content, not its image under `α`, indexes the sectors.

An upward strand `Eᵢ` changes the sector by one of the two raising summands of (A2): the
probe summand `A` (precomposition by `Eᵢ` of the probe) or the reservoir summand `B`
(postcomposition by `Eᵢ` of the reservoir, shifted by `pᵢ P(b)`); a downward strand `Fᵢ` by
one of the reverse edges of (A3). `SPath w s t` is a choice of summand for every strand of the
word `w` (read from left to right), compatible with the contents, from the leftmost sector `s`
to the rightmost sector `t`; `pathFunctor` composes the corresponding Hom-sector functors,
`H t ⥤ H s`. There are finitely many paths for a word and a leftmost sector.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u uB v w

variable {I X : Type u}

/-- A sector: probe content and reservoir content. -/
abbrev Sector (I : Type u) := (I →₀ ℕ) × (I →₀ ℕ)

/-- The neighbouring sector across a strand with signed letter `l`, through the probe summand
(`side = true`) or the reservoir summand (`side = false`), from the sector `s` on its left. -/
def nextSector : Letter I → Bool → Sector I → Sector I
  | (true, i), true, s => (s.1 + Finsupp.single i 1, s.2)
  | (true, i), false, s => (s.1, s.2 - Finsupp.single i 1)
  | (false, i), true, s => (s.1 - Finsupp.single i 1, s.2)
  | (false, i), false, s => (s.1, s.2 + Finsupp.single i 1)

/-- The content condition for a summand: a reservoir summand of `Eᵢ` and a probe summand of
`Fᵢ` need positive `i`-content on the left. -/
def StepValid : Letter I → Bool → Sector I → Prop
  | (true, _), true, _ => True
  | (true, i), false, s => 1 ≤ s.2 i
  | (false, i), true, s => 1 ≤ s.1 i
  | (false, _), false, _ => True

/-- A choice of summand for every strand of a word of colours, compatible with the contents,
from the leftmost sector to the rightmost sector. -/
inductive SPath : List (Col I X) → Sector I → Sector I → Type u
  | nil (s : Sector I) : SPath [] s s
  | cons {w : List (Col I X)} {t : Sector I} (c : Col I X) (side : Bool) (s : Sector I)
      (hv : StepValid c.l side s) (p : SPath w (nextSector c.l side s) t) : SPath (c :: w) s t

namespace SPath

/-- Concatenation of paths. -/
def append : {l m : List (Col I X)} → {s t r : Sector I} → SPath l s t → SPath m t r →
    SPath (l ++ m) s r
  | _, _, _, _, _, .nil _, q => q
  | _, _, _, _, _, .cons c side s hv p, q => .cons c side s hv (append p q)

/-- Splitting a path of a concatenated word at the junction. -/
def split : (l : List (Col I X)) → {m : List (Col I X)} → {s r : Sector I} →
    SPath (l ++ m) s r → Σ t, SPath l s t × SPath m t r
  | [], _, s, _, p => ⟨s, .nil s, p⟩
  | _ :: l, _, _, _, .cons c side s hv p =>
    ⟨(split l p).1, .cons c side s hv (split l p).2.1, (split l p).2.2⟩

theorem split_append : {l m : List (Col I X)} → {s t r : Sector I} → (p : SPath l s t) →
    (q : SPath m t r) → split l (append p q) = ⟨t, p, q⟩
  | _, _, _, _, _, .nil _, _ => rfl
  | _, _, _, _, _, .cons c side s hv p, q => by
    simp only [append, split]
    rw [split_append p q]

theorem append_split : (l : List (Col I X)) → {m : List (Col I X)} → {s r : Sector I} →
    (p : SPath (l ++ m) s r) → append (split l p).2.1 (split l p).2.2 = p
  | [], _, _, _, _ => rfl
  | _ :: l, _, _, _, .cons c side s hv p => by
    change cons c side s hv (append (split l p).2.1 (split l p).2.2) = _
    rw [append_split l p]

/-- A path through a nonempty word is its first summand followed by a path. -/
def head {c : Col I X} {w : List (Col I X)} {s t : Sector I} :
    SPath (c :: w) s t → Σ side : Bool, PLift (StepValid c.l side s) ×
      SPath w (nextSector c.l side s) t
  | .cons _ side _ hv p => ⟨side, PLift.up hv, p⟩

theorem head_injective {c : Col I X} {w : List (Col I X)} {s t : Sector I} :
    Function.Injective (head : SPath (c :: w) s t → _) := by
  intro p q h
  cases p
  cases q
  simp only [head, Sigma.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [heq_eq_eq, Prod.mk.injEq] at h
  rw [h.2]

instance subsingleton_nil (s t : Sector I) : Subsingleton (SPath ([] : List (Col I X)) s t) :=
  ⟨fun p q => by cases p; cases q; rfl⟩

instance finite : (w : List (Col I X)) → (s t : Sector I) → Finite (SPath w s t)
  | [], _, _ => Finite.of_subsingleton
  | c :: w, s, t => by
    have : ∀ side : Bool, Finite (SPath w (nextSector c.l side s) t) :=
      fun side => finite w _ t
    exact Finite.of_injective _ head_injective

end SPath

variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]

variable (k B) in
/-- The probe and reservoir factors of the swapped Hom construction, with their highest
weights. The probe sits on the precomposition side and carries shifted left adjunctions; the
reservoir sits on the postcomposition side. Both satisfy the multicolour relations. -/
structure ProbeReservoir (D : Datum I X) (Sc : Scalars D k) where
  /-- The probe. -/
  T : RouquierFamily (k := k) (B := B) D
  /-- The reservoir. -/
  W : RouquierFamily (k := k) (B := B) D
  /-- The shifted left adjunctions of the probe. -/
  leftAdj : RouquierLeftAdjoints (k := k) T
  /-- The multicolour relations of the probe. -/
  probeRel : RouquierMulticolour T Sc
  /-- The multicolour relations of the reservoir. -/
  reservoirRel : RouquierMulticolour W Sc
  /-- The highest weight of the probe. -/
  ΛP : X
  /-- The highest weight of the reservoir. -/
  ΛR : X

variable {D : Datum I X}

/-- The root-lattice image `α(b)` of a formal content. -/
def contentWeight (D : Datum I X) : (I →₀ ℕ) →+ X := Finsupp.weight D.α

theorem contentWeight_add_single (b : I →₀ ℕ) (i : I) :
    contentWeight D (b + Finsupp.single i 1) = contentWeight D b + D.α i := by
  rw [map_add]
  simp [contentWeight, Finsupp.weight_apply]

theorem contentWeight_sub_single {b : I →₀ ℕ} {i : I} (hb : 1 ≤ b i) :
    contentWeight D (b - Finsupp.single i 1) + D.α i = contentWeight D b := by
  have hle : Finsupp.single i 1 ≤ b := by
    rw [Finsupp.single_le_iff]; exact hb
  conv_rhs => rw [← tsub_add_cancel_of_le hle]
  rw [contentWeight_add_single]

namespace ProbeReservoir

variable {Sc : Scalars D k} (P : ProbeReservoir k B D Sc)

/-- The probe weight `ΛP - α(b)` of a sector. -/
def muP (s : Sector I) : X := P.ΛP - contentWeight D s.1

/-- The reservoir weight `-ΛR + α(c)` of a sector. -/
def muM (s : Sector I) : X := -P.ΛR + contentWeight D s.2

/-- The weight `ΛP - ΛR - α(b) + α(c)` of a sector. -/
def wt (s : Sector I) : X := P.muP s + P.muM s

/-- The Hom category of a sector. -/
abbrev H (s : Sector I) : Type v := homWeightSector P.T.obj P.W.obj (P.muP s) (P.muM s)

end ProbeReservoir

namespace ProbeReservoir

variable {Sc : Scalars D k} (P : ProbeReservoir k B D Sc)

/-- The Hom-sector functor of one strand, from the right sector to the left sector: (A2) for
an upward strand and (A3) for a downward strand. -/
def step : (l : Letter I) → (side : Bool) → (s : Sector I) → StepValid l side s →
    (P.H (nextSector l side s) ⥤ P.H s)
  | (true, i), true, s, _ =>
    homContentPreE P.T P.W.obj i (P.muM s)
      (show -P.muP s + D.α i = -P.muP (s.1 + Finsupp.single i 1, s.2) by
        simp only [muP, contentWeight_add_single]; abel)
  | (true, i), false, s, hv =>
    homContentPostE P.T.obj P.W i s.1 (P.muP s)
      (show P.muM (s.1, s.2 - Finsupp.single i 1) + D.α i = P.muM s by
        simp only [muM]; rw [add_assoc, contentWeight_sub_single hv])
  | (false, i), true, s, hv =>
    homContentPreF P.T P.W.obj i (P.muM s)
      (show -P.muP (s.1 - Finsupp.single i 1, s.2) + D.α i = -P.muP s by
        simp only [muP]; rw [← contentWeight_sub_single (D := D) hv]; abel)
  | (false, i), false, s, _ =>
    homContentPostF P.T.obj P.W i s.1 (P.muP s)
      (show P.muM s + D.α i = P.muM (s.1, s.2 + Finsupp.single i 1) by
        simp only [muM, contentWeight_add_single]; abel)


/-- The Hom-sector functor of a path, from its rightmost sector to its leftmost sector. -/
def pathFunctor : {w : List (Col I X)} → {s t : Sector I} → SPath w s t → (P.H t ⥤ P.H s)
  | _, _, _, .nil _ => 𝟭 _
  | _, _, _, .cons c side s hv p => pathFunctor p ⋙ P.step c.l side s hv

@[simp] theorem pathFunctor_nil (s : Sector I) :
    P.pathFunctor (SPath.nil (X := X) s) = 𝟭 _ := rfl

@[simp] theorem pathFunctor_cons {w : List (Col I X)} {t : Sector I} (c : Col I X)
    (side : Bool) (s : Sector I) (hv : StepValid c.l side s)
    (p : SPath w (nextSector c.l side s) t) :
    P.pathFunctor (.cons c side s hv p) = P.pathFunctor p ⋙ P.step c.l side s hv := rfl

/-- The functor of a concatenated path is the composite. -/
theorem pathFunctor_append : {l m : List (Col I X)} → {s t r : Sector I} →
    (p : SPath l s t) → (q : SPath m t r) →
    P.pathFunctor (p.append q) = P.pathFunctor q ⋙ P.pathFunctor p
  | _, _, _, _, _, .nil _, _ => rfl
  | _, _, _, _, _, .cons c side s hv p, q => by
    rw [SPath.append, pathFunctor_cons, pathFunctor_append p q, pathFunctor_cons]
    rfl

omit [TwoSupercategory k B] [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- A strand changes the sector weight by the weight of its letter. -/
theorem wt_nextSector (l : Letter I) (side : Bool) (s : Sector I) (hv : StepValid l side s) :
    P.wt s = sh D l + P.wt (nextSector l side s) := by
  obtain ⟨_ | _, i⟩ := l <;> cases side <;>
    simp only [wt, muP, muM, nextSector, sh, Bool.false_eq_true, ↓reduceIte] <;>
    first
    | (rw [contentWeight_add_single]; abel)
    | (rw [← contentWeight_sub_single (D := D) hv]; abel)

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
