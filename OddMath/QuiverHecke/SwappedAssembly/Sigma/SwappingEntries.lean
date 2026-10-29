/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SameColourBlocks
import OddMath.QuiverHecke.SwappedAssembly.Sigma.Entry

/-! # The swapping entries of the same-colour sideways crossing

Between distinct sectors `t ≠ s`, the entry of the sideways crossing
`σ = sigmaL i i : Eᵢ Fᵢ → Fᵢ Eᵢ` of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Definition 1.5, (1.11), in the swapped Hom construction is one of the two
swapping blocks `W_A`, `W_B` of `docs/Nondegeneracy/AugmentedSectorBlocks.md` §2. The sum over
the intermediate summand paths of the unit, the upward crossing and the counit has a single
nonzero term.

## Main results

* `ProbeReservoir.exists_dec_of_compLayer_ne_zero`: a nonzero layer entry relates two
  decomposed paths with the same outer parts.
* `ProbeReservoir.sigmaEntry_eq_sum`: the entry of `σ` is the sum over the two intermediate
  paths of the composite of the cup, crossing and cap entries (`sigmaTerm`).
* `ProbeReservoir.sides_of_sigmaTerm_ne_zero`: a nonzero term has intermediate summands
  `[q₁, q₁, p₁, p₂]` and `[q₁, q₂, p₂, p₂]`, where `[p₁, p₂]` and `[q₁, q₂]` are the summands of
  the source and target paths.
* `ProbeReservoir.sigmaEntry_eq_sigmaTerm`: hence the entry is that single term.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

/-- A nonzero layer entry relates two paths that agree outside the generator. -/
theorem exists_dec_of_compLayer_ne_zero (gens : P.Generators) (L : Layer (SKM.sig D))
    {s t : Sector I} (p : SPath L.dom.word s t) (q : SPath L.cod.word s t) (Z : P.H t)
    (h : compLayer gens L p q Z ≠ 0) :
    ∃ (x y : Sector I) (pu : SPath L.left s x) (pg : SPath ((SKM.sig D).dom L.gen) x y)
      (qg : SPath ((SKM.sig D).cod L.gen) x y) (pv : SPath L.right y t),
      p = (pu.append pg).append pv ∧ q = (pu.append qg).append pv := by
  obtain ⟨d, rfl⟩ : ∃ d : SPath.Dec L.left ((SKM.sig D).dom L.gen) L.right s t, p = d.path :=
    ⟨_, (SPath.path_decOf _ _ p).symm⟩
  obtain ⟨e, rfl⟩ : ∃ e : SPath.Dec L.left ((SKM.sig D).cod L.gen) L.right s t, q = e.path :=
    ⟨_, (SPath.path_decOf _ _ q).symm⟩
  by_cases ho : d.outer = e.outer
  · obtain ⟨⟨x, y⟩, pu, pg, pv⟩ := d
    obtain ⟨⟨x', y'⟩, pu', qg, pv'⟩ := e
    simp only [SPath.Dec.outer, Prod.mk.injEq, Sigma.mk.injEq] at ho
    obtain ⟨⟨rfl, h1⟩, ⟨rfl, h2⟩⟩ := ho
    cases h1; cases h2
    exact ⟨x, y, pu, pg, qg, pv, rfl, rfl⟩
  · exact absurd (compLayer_eq_zero gens L d e ho Z) h

open Classical in
/-- A three-layer composite is the double sum over the intermediate paths. -/
theorem compList_three (gens : P.Generators) (L₁ L₂ L₃ : Layer (SKM.sig D))
    {a b : Obj (SKM.sig D)} (h : Chain a [L₁, L₂, L₃] b) {s t : Sector I}
    (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t) :
    letI := Fintype.ofFinite (SPath L₁.cod.word s t)
    letI := Fintype.ofFinite (SPath L₂.cod.word s t)
    compList gens _ h p q Z = ∑ m₁ : SPath L₁.cod.word s t, ∑ m₂ : SPath L₂.cod.word s t,
      eqToHom (by rw [pathFunctor_cast]) ≫
        compLayer gens L₁ (p.cast (congrArg Obj.word h.2.1.symm)) m₁ Z ≫
        eqToHom (by rw [pathFunctor_cast]) ≫
        compLayer gens L₂ (m₁.cast (congrArg Obj.word h.2.2.2.1.symm)) m₂ Z ≫
        eqToHom (by rw [pathFunctor_cast]) ≫
        compLayer gens L₃ (m₂.cast (congrArg Obj.word h.2.2.2.2.2.1.symm))
          (q.cast (congrArg Obj.word h.2.2.2.2.2.2.symm)) Z ≫
        eqToHom (by rw [pathFunctor_cast]) := by
  obtain ⟨hv₁, rfl, hv₂, h₂, hv₃, h₃, rfl⟩ := h
  simp only [compList, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
  simp only [SPath.cast_self]
  rw [Finset.sum_eq_single q (fun x _ hx => by simp [hx]) (by simp)]
  simp

/-- The summands of a nonzero cup entry of the sideways crossing. -/
theorem sides_of_cup_ne_zero (gens : P.Generators) (i j : I) (ν : X) {t s : Sector I}
    (p : SPath (SKM.lay D ν [] (SKM.Shape.cup i) [up j, dn i]).dom.word t s)
    (m : SPath (SKM.lay D ν [] (SKM.Shape.cup i) [up j, dn i]).cod.word t s) (Z : P.H s)
    (h : compLayer gens (SKM.lay D ν [] (SKM.Shape.cup i) [up j, dn i]) p m Z ≠ 0) :
    ∃ σ, m.sides = σ :: σ :: p.sides := by
  obtain ⟨x, y, pu, pg, qg, pv, rfl, rfl⟩ := exists_dec_of_compLayer_ne_zero gens _ p m Z h
  cases pu
  obtain rfl := SPath.eq_of_nil (X := X) pg
  cases pg
  obtain ⟨σ, hσ⟩ := SPath.side_eq_of_closed qg (by simp)
  exact ⟨σ, by simp [SPath.sides_append, hσ, SPath.sides]⟩

/-- The summands of a nonzero cap entry of the sideways crossing. -/
theorem sides_of_cap_ne_zero (gens : P.Generators) (i j : I) (ν : X) {t s : Sector I}
    (m : SPath (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []).dom.word t s)
    (q : SPath (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []).cod.word t s) (Z : P.H s)
    (h : compLayer gens (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []) m q Z ≠ 0) :
    ∃ τ, m.sides = q.sides ++ [τ, τ] := by
  obtain ⟨x, y, pu, pg, qg, pv, rfl, rfl⟩ := exists_dec_of_compLayer_ne_zero gens _ m q Z h
  cases pv
  obtain rfl := SPath.eq_of_nil (X := X) qg
  cases qg
  obtain ⟨τ, hτ⟩ := SPath.side_eq_of_closed pg (by simp)
  exact ⟨τ, by simp [SPath.sides_append, hτ, SPath.sides]⟩

/-- The summands of a nonzero crossing entry of the sideways crossing: the outer strands keep
their summands. -/
theorem sides_of_cross_ne_zero (gens : P.Generators) (i j : I) (ν : X) {t s : Sector I}
    (m : SPath (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]).dom.word t s)
    (m' : SPath (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]).cod.word t s) (Z : P.H s)
    (h : compLayer gens (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]) m m' Z ≠ 0) :
    ∃ a b u v, m.sides = a :: (u ++ [b]) ∧ m'.sides = a :: (v ++ [b]) := by
  obtain ⟨x, y, pu, pg, qg, pv, rfl, rfl⟩ := exists_dec_of_compLayer_ne_zero gens _ m m' Z h
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 (SPath.length_sides pu)
  obtain ⟨b, hb⟩ := List.length_eq_one_iff.1 (SPath.length_sides pv)
  exact ⟨a, b, pg.sides, qg.sides, by simp [SPath.sides_append, ha, hb],
    by simp [SPath.sides_append, ha, hb]⟩

section SigmaTerm

variable (gens : P.Generators) (i j : I) (ν : X)

/-- The first layer of the sideways crossing: the cup. -/
abbrev sigL₁ : Layer (SKM.sig D) := SKM.lay D ν [] (SKM.Shape.cup i) [up j, dn i]
/-- The second layer of the sideways crossing: the upward crossing. -/
abbrev sigL₂ : Layer (SKM.sig D) := SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]
/-- The third layer of the sideways crossing: the cap. -/
abbrev sigL₃ : Layer (SKM.sig D) := SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []

theorem sigL₁_dom : wd D ν [up j, dn i] = (sigL₁ (D := D) i j ν).dom.word := by
  rw [SKM.lay_dom]; rfl
theorem sigL₂_dom : (sigL₁ (D := D) i j ν).cod.word = (sigL₂ (D := D) i j ν).dom.word := by
  rw [SKM.lay_dom, SKM.lay_cod]; rfl
theorem sigL₃_dom : (sigL₂ (D := D) i j ν).cod.word = (sigL₃ (D := D) i j ν).dom.word := by
  rw [SKM.lay_dom, SKM.lay_cod]; rfl
theorem sigL₃_cod : wd D ν [dn i, up j] = (sigL₃ (D := D) i j ν).cod.word := by
  rw [SKM.lay_cod]; rfl

/-- The term of the entry of the sideways crossing at the intermediate paths `m₁`, `m₂`. -/
def sigmaTerm {t s : Sector I} (p : SPath (wd D ν [up j, dn i]) t s)
    (q : SPath (wd D ν [dn i, up j]) t s) (m₁ : SPath (sigL₁ (D := D) i j ν).cod.word t s)
    (m₂ : SPath (sigL₂ (D := D) i j ν).cod.word t s) (Z : P.H s) :
    (P.pathFunctor p).obj Z ⟶ (P.pathFunctor q).obj Z :=
  eqToHom (by rw [pathFunctor_cast]) ≫
    compLayer gens (sigL₁ i j ν) (p.cast (sigL₁_dom i j ν)) m₁ Z ≫
    eqToHom (by rw [pathFunctor_cast]) ≫
    compLayer gens (sigL₂ i j ν) (m₁.cast (sigL₂_dom i j ν)) m₂ Z ≫
    eqToHom (by rw [pathFunctor_cast]) ≫
    compLayer gens (sigL₃ i j ν) (m₂.cast (sigL₃_dom i j ν)) (q.cast (sigL₃_cod i j ν)) Z ≫
    eqToHom (by rw [pathFunctor_cast])

open Classical in
/-- The entry of the sideways crossing as a double sum of `sigmaTerm`s. -/
theorem sigmaEntry_eq_sum (c : P.CrossCoeff) {t s : Sector I}
    (p : SPath (wd D ν [up j, dn i]) t s) (q : SPath (wd D ν [dn i, up j]) t s) (Z : P.H s) :
    letI := Fintype.ofFinite (SPath (sigL₁ (D := D) i j ν).cod.word t s)
    letI := Fintype.ofFinite (SPath (sigL₂ (D := D) i j ν).cod.word t s)
    P.sigmaEntry c i j ν p q Z =
      ∑ m₁, ∑ m₂, sigmaTerm (P.upwardGens c) i j ν p q m₁ m₂ Z :=
  compList_three (P.upwardGens c) (sigL₁ i j ν) (sigL₂ i j ν) (sigL₃ i j ν)
    ((SKM.sChain_sigmaL i j).chain D ν) p q Z


/-- The summands of the intermediate paths of a nonzero term of the sideways crossing: the cup
and the cap stay in the summands of the left strand of the target and of the right strand of
the source. -/
theorem sides_of_sigmaTerm_ne_zero {t s : Sector I} (p : SPath (wd D ν [up j, dn i]) t s)
    (q : SPath (wd D ν [dn i, up j]) t s) (m₁ : SPath (sigL₁ (D := D) i j ν).cod.word t s)
    (m₂ : SPath (sigL₂ (D := D) i j ν).cod.word t s) (Z : P.H s)
    (h : sigmaTerm gens i j ν p q m₁ m₂ Z ≠ 0) :
    ∃ p₁ p₂ q₁ q₂, p.sides = [p₁, p₂] ∧ q.sides = [q₁, q₂] ∧
      m₁.sides = [q₁, q₁, p₁, p₂] ∧ m₂.sides = [q₁, q₂, p₂, p₂] := by
  unfold sigmaTerm at h
  have h₁ : compLayer gens (sigL₁ i j ν) (p.cast (sigL₁_dom i j ν)) m₁ Z ≠ 0 := fun e => h (by
    rw [e]; simp only [Limits.zero_comp, Limits.comp_zero])
  have h₂ : compLayer gens (sigL₂ i j ν) (m₁.cast (sigL₂_dom i j ν)) m₂ Z ≠ 0 := fun e => h (by
    rw [e]; simp only [Limits.zero_comp, Limits.comp_zero])
  have h₃ : compLayer gens (sigL₃ i j ν) (m₂.cast (sigL₃_dom i j ν)) (q.cast (sigL₃_cod i j ν))
      Z ≠ 0 := fun e => h (by
    rw [e]; simp only [Limits.zero_comp, Limits.comp_zero])
  obtain ⟨σ, hσ⟩ := sides_of_cup_ne_zero gens i j ν _ _ Z h₁
  obtain ⟨a, b, u, v, hu, hv⟩ := sides_of_cross_ne_zero gens i j ν _ _ Z h₂
  obtain ⟨τ, hτ⟩ := sides_of_cap_ne_zero gens i j ν _ _ Z h₃
  simp only [SPath.sides_cast] at hσ hu hv hτ
  obtain ⟨p₁, p₂, hp⟩ := List.length_eq_two.1 (SPath.length_sides p)
  obtain ⟨q₁, q₂, hq⟩ := List.length_eq_two.1 (SPath.length_sides q)
  have hlu := congrArg List.length (hσ.symm.trans hu)
  have hlv := congrArg List.length (hτ.symm.trans hv)
  simp only [hp, hq, List.length_cons, List.length_append, List.length_nil] at hlu hlv
  obtain ⟨u₁, u₂, rfl⟩ := List.length_eq_two.1 (by omega : u.length = 2)
  obtain ⟨v₁, v₂, rfl⟩ := List.length_eq_two.1 (by omega : v.length = 2)
  rw [hp] at hσ
  rw [hq] at hτ
  have e₁ := hσ.symm.trans hu
  have e₂ := hτ.symm.trans hv
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at e₁ e₂
  obtain ⟨ha₁, -, -, hb₁, -⟩ := e₁
  obtain ⟨ha₂, -, -, hb₂, -⟩ := e₂
  refine ⟨p₁, p₂, q₁, q₂, hp, hq, ?_, ?_⟩
  · rw [hσ, ha₁, ← ha₂]
  · rw [hτ, hb₂, ← hb₁]; rfl

/-- If two summand paths have the sides forced by `sides_of_sigmaTerm_ne_zero`, the sideways
crossing entry is the single corresponding term. -/
theorem sigmaEntry_eq_sigmaTerm (c : P.CrossCoeff) {t s : Sector I}
    (p : SPath (wd D ν [up j, dn i]) t s) (q : SPath (wd D ν [dn i, up j]) t s)
    (m₁ : SPath (sigL₁ (D := D) i j ν).cod.word t s) (m₂ : SPath (sigL₂ (D := D) i j ν).cod.word t s)
    (p₁ p₂ q₁ q₂ : Bool) (hp : p.sides = [p₁, p₂]) (hq : q.sides = [q₁, q₂])
    (hm₁ : m₁.sides = [q₁, q₁, p₁, p₂]) (hm₂ : m₂.sides = [q₁, q₂, p₂, p₂]) (Z : P.H s) :
    P.sigmaEntry c i j ν p q Z = sigmaTerm (P.upwardGens c) i j ν p q m₁ m₂ Z := by
  classical
  rw [sigmaEntry_eq_sum]
  rw [Finset.sum_eq_single m₁ ?_ (by simp)]
  · rw [Finset.sum_eq_single m₂ ?_ (by simp)]
    intro x _ hx
    by_contra hne
    obtain ⟨a₁, a₂, b₁, b₂, ha, hb, -, h₂⟩ := sides_of_sigmaTerm_ne_zero _ i j ν p q m₁ x Z hne
    rw [hp] at ha; rw [hq] at hb
    simp only [List.cons.injEq, and_true] at ha hb
    obtain ⟨rfl, rfl⟩ := ha; obtain ⟨rfl, rfl⟩ := hb
    exact hx (SPath.eq_of_sides _ _ (h₂.trans hm₂.symm))
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    by_contra hne
    obtain ⟨a₁, a₂, b₁, b₂, ha, hb, h₁, -⟩ := sides_of_sigmaTerm_ne_zero _ i j ν p q x y Z hne
    rw [hp] at ha; rw [hq] at hb
    simp only [List.cons.injEq, and_true] at ha hb
    obtain ⟨rfl, rfl⟩ := ha; obtain ⟨rfl, rfl⟩ := hb
    exact hx (SPath.eq_of_sides _ _ (h₁.trans hm₁.symm))

end SigmaTerm

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
