/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Leftward

/-! # The equal-colour leftward data from inverses of the augmented maps

The equal-colour leftward data `L` of the swapped generators (the leftward crossing
`Fᵢ Eᵢ → Eᵢ Fᵢ` and the `♦`-cups and caps) are read off the two-sided inverses of the
augmented maps of Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5, following (A7) of `docs/Nondegeneracy/SwappedActionAssembly.md`:

* (1.13), `⟨hᵢ, ν⟩ ≥ 0`: `(σ, ε, ε x, …) : Eᵢ Fᵢ → Fᵢ Eᵢ ⊕ 1^{⟨hᵢ,ν⟩}` has the inverse
  `(-lcross, ♦-cups)`;
* (1.14), `⟨hᵢ, ν⟩ < 0`: `(-σ, η, x η, …) : Eᵢ Fᵢ ⊕ 1^{-⟨hᵢ,ν⟩} → Fᵢ Eᵢ` has the inverse
  `(lcross, ♦-caps)`.

The entries of the augmented maps are built from the upward generators alone
(`sigmaEntry`, `epsEntry`, `etaEntry`), so these are conditions on the coefficient `c` of the
equal-colour mixed block. `PosInverse` and `NegInverse` state, entry by entry between summand
paths, that given families are the components of the inverse; `AugmentedInvertible c` asks
for such families at every colour, weight and pair of sectors (for `⟨hᵢ, ν⟩ = 0` the map
(1.13) is used).

Main declarations:

* `LeftwardData.isInverse_of_posInverse_negInverse`: leftward data whose entries invert the
  augmented maps satisfy `LeftwardData.IsInverse` (the converse of
  `leftward_supernatural_of_nonneg`, `leftward_supernatural_of_nonpos`, which extract the
  inverse from `IsInverse`);
* `leftwardOfInvertible`, `leftwardOfInvertible_isInverse`: the leftward data (A7) built from
  chosen inverses, and their inversion relations.

The invertibility `AugmentedInvertible c` for the unit-dot probe and the full-ELV reservoir is
the written consequence of the factor hypotheses in `docs/Nondegeneracy/SwappedHomInversion.md`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams Supercategory OddMath.SKM

universe u uB vB wB

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{wB, vB} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

open Classical

section Entries

variable (P : ProbeReservoir k B D Sc)

/-- The entry of `ε xⁿ : Eᵢ Fᵢ → 1` (`epsL i n`) for the upward generators. -/
def epsEntry (c : P.CrossCoeff) (i : I) (n : ℕ) (ν : X) {t s : Sector I}
    (p : SPath (wd D ν [up i, dn i]) t s) (r : SPath (wd D ν []) t s) (Z : P.H s) :
    (P.pathFunctor p).obj Z ⟶ (P.pathFunctor r).obj Z :=
  compList (P.upwardGens c) (SKM.layList D ν (SKM.epsL i n)) ((SKM.sChain_epsL i n).chain D ν)
    p r Z

/-- The entry of `xⁿ η : 1 → Fᵢ Eᵢ` (`etaL i n`) for the upward generators. -/
def etaEntry (c : P.CrossCoeff) (i : I) (n : ℕ) (ν : X) {t s : Sector I}
    (r : SPath (wd D ν []) t s) (q : SPath (wd D ν [dn i, up i]) t s) (Z : P.H s) :
    (P.pathFunctor r).obj Z ⟶ (P.pathFunctor q).obj Z :=
  compList (P.upwardGens c) (SKM.layList D ν (SKM.etaL i n)) ((SKM.sChain_etaL i n).chain D ν)
    r q Z

/-- **The inverse of the augmented map (1.13)**, entry by entry: for `⟨hᵢ, ν⟩ ≥ 0`, the
families `lc` (the leftward crossing `Fᵢ Eᵢ → Eᵢ Fᵢ`) and `dc n` (the `♦`-cups `1 → Eᵢ Fᵢ`,
`n < ⟨hᵢ, ν⟩`) are such that `(-lc, dc)` is a two-sided inverse of `(σ, ε xⁿ)`. The five
conditions are the relations `invP₁`–`invP₅`. -/
def PosInverse (c : P.CrossCoeff) (i : I) (ν : X) (t s : Sector I)
    (lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t s) (p : SPath (wd D ν [up i, dn i]) t s)
      (Z : P.H s), (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (wd D ν []) t s) (p : SPath (wd D ν [up i, dn i]) t s)
      (Z : P.H s), (P.pathFunctor _r).obj Z ⟶ (P.pathFunctor p).obj Z) : Prop :=
  letI := Fintype.ofFinite (SPath (wd D ν [up i, dn i]) t s)
  letI := Fintype.ofFinite (SPath (wd D ν [dn i, up i]) t s)
  letI := Fintype.ofFinite (SPath (wd D ν []) t s)
  (∀ p p' Z, -∑ q, P.sigmaEntry c i i ν p q Z ≫ lc q p' Z +
      ∑ n ∈ Finset.range (D.h i ν).toNat, ∑ r, P.epsEntry c i n ν p r Z ≫ dc n r p' Z =
      famDelta (fun x => P.pathFunctor x) p p' Z) ∧
  (∀ q q' Z, ∑ p, lc q p Z ≫ P.sigmaEntry c i i ν p q' Z =
      -famDelta (fun x => P.pathFunctor x) q q' Z) ∧
  (∀ m : ℕ, (m : ℤ) < D.h i ν → ∀ q r Z, ∑ p, lc q p Z ≫ P.epsEntry c i m ν p r Z = 0) ∧
  (∀ n : ℕ, (n : ℤ) < D.h i ν → ∀ r q Z, ∑ p, dc n r p Z ≫ P.sigmaEntry c i i ν p q Z = 0) ∧
  (∀ m n : ℕ, (m : ℤ) < D.h i ν → (n : ℤ) < D.h i ν → ∀ r r' Z,
      ∑ p, dc n r p Z ≫ P.epsEntry c i m ν p r' Z =
        if m = n then famDelta (fun x => P.pathFunctor x) r r' Z else 0)

/-- **The inverse of the augmented map (1.14)**, entry by entry: for `⟨hᵢ, ν⟩ ≤ 0`, the
families `lc` (the leftward crossing `Fᵢ Eᵢ → Eᵢ Fᵢ`) and `dc n` (the `♦`-caps `Fᵢ Eᵢ → 1`,
`n < -⟨hᵢ, ν⟩`) are such that `(lc, dc)` is a two-sided inverse of `(-σ, xⁿ η)`. The five
conditions are the relations `invM₁`–`invM₅`. -/
def NegInverse (c : P.CrossCoeff) (i : I) (ν : X) (t s : Sector I)
    (lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t s) (p : SPath (wd D ν [up i, dn i]) t s)
      (Z : P.H s), (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (wd D ν [dn i, up i]) t s) (r : SPath (wd D ν []) t s)
      (Z : P.H s), (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor r).obj Z) : Prop :=
  letI := Fintype.ofFinite (SPath (wd D ν [up i, dn i]) t s)
  letI := Fintype.ofFinite (SPath (wd D ν [dn i, up i]) t s)
  letI := Fintype.ofFinite (SPath (wd D ν []) t s)
  (∀ q q' Z, -∑ p, lc q p Z ≫ P.sigmaEntry c i i ν p q' Z +
      ∑ n ∈ Finset.range (-D.h i ν).toNat, ∑ r, dc n q r Z ≫ P.etaEntry c i n ν r q' Z =
      famDelta (fun x => P.pathFunctor x) q q' Z) ∧
  (∀ p p' Z, ∑ q, P.sigmaEntry c i i ν p q Z ≫ lc q p' Z =
      -famDelta (fun x => P.pathFunctor x) p p' Z) ∧
  (∀ m : ℕ, (m : ℤ) < -D.h i ν → ∀ r p Z, ∑ q, P.etaEntry c i m ν r q Z ≫ lc q p Z = 0) ∧
  (∀ n : ℕ, (n : ℤ) < -D.h i ν → ∀ p r Z, ∑ q, P.sigmaEntry c i i ν p q Z ≫ dc n q r Z = 0) ∧
  (∀ m n : ℕ, (m : ℤ) < -D.h i ν → (n : ℤ) < -D.h i ν → ∀ r r' Z,
      ∑ q, P.etaEntry c i m ν r q Z ≫ dc n q r' Z =
        if m = n then famDelta (fun x => P.pathFunctor x) r r' Z else 0)

/-- **The augmented maps are invertible**: at every colour `i`, weight `ν` and pair of
sectors whose rightmost sector `s` has weight `ν`, the augmented map (1.13) has an inverse when
`⟨hᵢ, ν⟩ ≥ 0` and (1.14) has one when `⟨hᵢ, ν⟩ < 0`. (At other sectors the number of dotted
windows does not match the summands and the maps are not invertible in general.) -/
def AugmentedInvertible (c : P.CrossCoeff) : Prop :=
  ∀ (i : I) (ν : X) (t s : Sector I), P.wt s = ν →
    (0 ≤ D.h i ν → ∃ lc dc, P.PosInverse c i ν t s lc dc) ∧
    (D.h i ν < 0 → ∃ lc dc, P.NegInverse c i ν t s lc dc)

/-- **The leftward data (A7)** built from inverses of the augmented maps: the leftward
crossing is minus the first component of the inverse of (1.13) for `⟨hᵢ, ν⟩ ≥ 0` and the first
component of the inverse of (1.14) otherwise; the `♦`-cups and caps are the remaining
components. Off the weight-matched sectors (`P.wt s ≠ ν`) all three are zero. -/
def leftwardOfInvertible (c : P.CrossCoeff) (h : P.AugmentedInvertible c) : P.LeftwardData where
  lcrossSame i ν {t s} q p Z :=
    if hw : P.wt s = ν then
      if hh : 0 ≤ D.h i ν then (((h i ν t s hw).1 hh).choose q p Z)
      else ((h i ν t s hw).2 (not_le.mp hh)).choose q p Z
    else 0
  dcup i n ν {t s} r p Z :=
    if hw : P.wt s = ν then
      if hh : 0 ≤ D.h i ν then ((h i ν t s hw).1 hh).choose_spec.choose n r p Z else 0
    else 0
  dcap i n ν {t s} q r Z :=
    if hw : P.wt s = ν then
      if hh : D.h i ν < 0 then ((h i ν t s hw).2 hh).choose_spec.choose n q r Z else 0
    else 0

end Entries

variable {P : ProbeReservoir k B D Sc}

/-! ## Entries of the relation diagrams -/

theorem compDiag_epsL_swappedGens (c : P.CrossCoeff) (L : P.LeftwardData) (i : I) (n : ℕ)
    (ν : X) {t s : Sector I} (p : SPath (wd D ν [up i, dn i]) t s) (r : SPath (wd D ν []) t s)
    (Z : P.H s) :
    compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.epsL i n) (SKM.sChain_epsL i n)) p r Z =
      P.epsEntry c i n ν p r Z :=
  compDiag_swappedGens_eq_upward c L ν (SKM.epsL i n) (SKM.sChain_epsL i n) (epsL_upward i n)
    p r Z

theorem compDiag_etaL_swappedGens (c : P.CrossCoeff) (L : P.LeftwardData) (i : I) (n : ℕ)
    (ν : X) {t s : Sector I} (r : SPath (wd D ν []) t s) (q : SPath (wd D ν [dn i, up i]) t s)
    (Z : P.H s) :
    compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.etaL i n) (SKM.sChain_etaL i n)) r q Z =
      P.etaEntry c i n ν r q Z :=
  compDiag_swappedGens_eq_upward c L ν (SKM.etaL i n) (SKM.sChain_etaL i n) (etaL_upward i n)
    r q Z

theorem compDiag_lcrossL_swappedGens (c : P.CrossCoeff) (L : P.LeftwardData) (i : I) (ν : X)
    {t s : Sector I} (q : SPath (wd D ν [dn i, up i]) t s) (p : SPath (wd D ν [up i, dn i]) t s)
    (Z : P.H s) :
    compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.lcrossL i i) (SKM.sChain_lcrossL i i)) q p Z =
      L.lcrossSame i ν q p Z := by
  rw [compDiag_lcrossL, swappedGens_lcross_self]

theorem compDiag_dcupL_swappedGens (c : P.CrossCoeff) (L : P.LeftwardData) (i : I) (n : ℕ)
    (ν : X) (hn : (n : ℤ) < D.h i ν) {t s : Sector I} (r : SPath (wd D ν []) t s)
    (p : SPath (wd D ν [up i, dn i]) t s) (Z : P.H s) :
    compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.dcupL i n) (SKM.sChain_dcupL i n)) r p Z =
      L.dcup i n ν r p Z := by
  rw [compDiag_dcupL]
  exact P.swappedGens_dcup_of_lt c L i n ν hn r p Z

theorem compDiag_dcapL_swappedGens (c : P.CrossCoeff) (L : P.LeftwardData) (i : I) (n : ℕ)
    (ν : X) (hn : (n : ℤ) < -D.h i ν) {t s : Sector I} (q : SPath (wd D ν [dn i, up i]) t s)
    (r : SPath (wd D ν []) t s) (Z : P.H s) :
    compDiag (P.swappedGens c L) (SKM.mkD D ν (SKM.dcapL i n) (SKM.sChain_dcapL i n)) q r Z =
      L.dcap i n ν q r Z := by
  rw [compDiag_dcapL]
  exact P.swappedGens_dcap_of_lt c L i n ν hn q r Z

theorem compDiag_id_eq_famDelta (gens : P.Generators) {w : List (Letter I)} (ν : X)
    {t s : Sector I} {_inst : Fintype (SPath (wd D ν w) t s)} (p q : SPath (wd D ν w) t s)
    (Z : P.H s) :
    compDiag gens (𝟙 (SKM.ob D ν w)) p q Z = famDelta (fun x => P.pathFunctor x) p q Z := by
  rw [compDiag_id]
  unfold famDelta
  split_ifs <;> rfl

/-! ## The inversion relations from the inverses -/

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
