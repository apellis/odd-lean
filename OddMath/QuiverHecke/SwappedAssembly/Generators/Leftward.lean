/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Generators.Cross
import OddMath.QuiverHecke.SwappedAssembly.WhiskerReduction

/-! # The leftward generators in the swapped action

The leftward crossing and the `♦`-cups and caps of Brundan–Ellis, *Super Kac–Moody
2-categories*, arXiv:1701.04133v2, Definition 1.5, (1.12)–(1.14) and (2.6), are the entries of
two-sided inverses of maps built from the upward generators
(`docs/Nondegeneracy/SwappedActionAssembly.md`, §§4–5).

* `upwardGens c`: the generator images with the upward dot, crossing (for the coefficient `c`
  of the equal-colour mixed block), rightward cup and cap, and zero leftward generators. The
  sideways crossing `σ = sigmaL i j` only uses the upward generators.
* `sigmaEntry c i j ν p q Z`: the entry of `σ : Eⱼ Fᵢ → Fᵢ Eⱼ` between summand paths.
* `lcrossNeImage c i j ν`, for distinct colours: the entry from `p` to `p'` is the inverse of
  the entry of `σ` from `p'` to `p` when that entry is invertible, and zero otherwise. For
  `i ≠ j` the matrix of `σ` is a block permutation of the four summand supports with
  invertible blocks (§5, (A9)–(A13)); on such a matrix this is its two-sided inverse.
* `LeftwardData`: the equal-colour leftward crossing and the `♦`-cups and caps, as data. They
  are the entries of the inverse of the whole augmented map of (1.13), resp. (1.14), (A7);
  the identities characterizing them are the relations `invP₁`–`invM₅`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u uB v w

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable (P : ProbeReservoir k B D Sc)

/-- The generator images with the upward dot, crossing, rightward cup and cap, and zero
leftward crossing and `♦`-cups and caps. -/
def upwardGens (c : P.CrossCoeff) : P.Generators where
  dot := P.dotImage
  cross := P.crossImage c
  cup := P.cupImage
  cap := P.capImage
  lcross _ _ _ _ _ _ := 0
  dcup _ _ _ _ _ _ := 0
  dcap _ _ _ _ _ _ := 0

/-- The entry of the sideways crossing `σ : Eⱼ Fᵢ → Fᵢ Eⱼ` (`sigmaL i j`, the unit, the upward
crossing, the counit) with rightmost weight `ν` between summand paths. -/
def sigmaEntry (c : P.CrossCoeff) (i j : I) (ν : X) {t s : Sector I}
    (p : SPath (wd D ν [up j, dn i]) t s) (q : SPath (wd D ν [dn i, up j]) t s) (Z : P.H s) :
    (P.pathFunctor p).obj Z ⟶ (P.pathFunctor q).obj Z :=
  compList (P.upwardGens c) (SKM.layList D ν (SKM.sigmaL i j))
    ((SKM.sChain_sigmaL i j).chain D ν) p q Z

open Classical in
/-- **The image of the leftward crossing for distinct colours**: the entrywise inverse of the
sideways crossing (zero at non-invertible entries). -/
def lcrossNeImage (c : P.CrossCoeff) (i j : I) (ν : X) : P.GenImage (.lcross i j) ν :=
  fun p p' Z =>
    if h : IsIso (P.sigmaEntry c i j ν p' p Z) then @inv _ _ _ _ _ h else 0

/-- The equal-colour leftward crossing and the `♦`-cups and caps, as data (A7). -/
structure LeftwardData where
  /-- The leftward crossing `Fᵢ Eᵢ → Eᵢ Fᵢ`. -/
  lcrossSame : ∀ (i : I) (ν : X), P.GenImage (.lcross i i) ν
  /-- The `♦`-cup with label `n`. -/
  dcup : ∀ (i : I) (n : ℕ) (ν : X), P.GenImage (.dcup i n) ν
  /-- The `♦`-cap with label `n`. -/
  dcap : ∀ (i : I) (n : ℕ) (ν : X), P.GenImage (.dcap i n) ν

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
