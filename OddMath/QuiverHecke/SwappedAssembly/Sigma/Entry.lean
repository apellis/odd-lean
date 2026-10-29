/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.Permutation
import OddMath.QuiverHecke.SwappedAssembly.CupCapZigzag

/-! # The entry of the sideways crossing for distinct colours

The sideways crossing `sigmaL i j` of Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, (1.11), is the composite of a cup, a crossing and a cap. Its image in the
swapped layer representation is a sum, over the summand paths of the two middle words, of
composites of layer entries. For `i ≠ j` exactly one term can be nonzero: following the sides
of a summand path through the layers, a nonzero cup entry duplicates a side, a crossing of
distinct colours exchanges two sides and a cap removes a matching pair, so the middle paths
are determined by the source path.

## Main results

* `ProbeReservoir.sides_of_cup`, `ProbeReservoir.sides_of_cross`, `ProbeReservoir.sides_of_cap`:
  how a nonzero layer entry changes sides.
* `ProbeReservoir.sigmaEntry_eq`: the sideways crossing entry is a single composite.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM

universe u

variable {I X : Type u}

namespace SPath

theorem sides_of_nil {s t : Sector I} (p : SPath ([] : List (Col I X)) s t) :
    p.sides = [] ∧ s = t := by
  cases p; exact ⟨rfl, rfl⟩

theorem exists_sides_one {c : Col I X} {s t : Sector I} (p : SPath [c] s t) :
    ∃ τ, p.sides = [τ] := by
  rcases p with _ | ⟨_, τ, _, _, p⟩
  rcases p with _ | _
  exact ⟨τ, rfl⟩

theorem exists_sides_pair {c₁ c₂ : Col I X} {s t : Sector I} (p : SPath [c₁, c₂] s t) :
    ∃ a b, p.sides = [a, b] := by
  obtain ⟨a, b, _, _, h, rfl⟩ := exists_eq_pair p
  subst h
  exact ⟨a, b, rfl⟩

variable {i j : I}

/-- For `i ≠ j`, the paths of `Eᵢ Eⱼ` and `Eⱼ Eᵢ` between the same sectors run through
exchanged summands. -/
theorem sides_upUp (hij : i ≠ j) {r₁ r₂ r₁' r₂' : X} {x y : Sector I}
    (p : SPath [⟨up i, r₁⟩, ⟨up j, r₂⟩] x y) (q : SPath [⟨up j, r₁'⟩, ⟨up i, r₂'⟩] x y) :
    q.sides = p.sides.reverse := by
  obtain ⟨a, b, hv₁, hv₂, hs, hp⟩ := exists_eq_pair p
  obtain ⟨a', b', hv₁', hv₂', hs', hq⟩ := exists_eq_pair q
  have ep : p.sides = [a, b] := by subst hs; subst hp; rfl
  have eq : q.sides = [a', b'] := by subst hs'; subst hq; rfl
  rw [ep, eq]
  have h := hs'.trans hs.symm
  clear hp hq ep eq hs hs'
  show [a', b'] = [b, a]
  have h1i := congrArg (fun x : Sector I => x.1 i) h
  have h1j := congrArg (fun x : Sector I => x.1 j) h
  have h2i := congrArg (fun x : Sector I => x.2 i) h
  have h2j := congrArg (fun x : Sector I => x.2 j) h
  have hji : (Finsupp.single j 1 : I →₀ ℕ) i = 0 := Finsupp.single_eq_of_ne hij
  have hij' : (Finsupp.single i 1 : I →₀ ℕ) j = 0 := Finsupp.single_eq_of_ne hij.symm
  clear h
  cases a <;> cases b <;> cases a' <;> cases b' <;>
    simp only [nextSector, StepValid, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply,
      Pi.sub_apply, Finsupp.single_eq_same, hji, hij'] at h1i h1j h2i h2j hv₁ hv₂ hv₁' hv₂' ⊢ <;>
    omega

theorem length_sides : {w : List (Col I X)} → {s t : Sector I} → (p : SPath w s t) →
    p.sides.length = w.length
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ _ _ _ p => by simp [sides, length_sides p]

end SPath

variable [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

theorem length_wd (μ : X) : (u : List (Letter I)) → (wd D μ u).length = u.length
  | [] => rfl
  | _ :: u => by simp [length_wd μ u]

namespace ProbeReservoir

variable {P : ProbeReservoir k B D Sc}

/-- A nonzero entry of a layer is the image of its generator between paths with the same
outer parts. -/
theorem compLayer_ne_zero (gens : P.Generators) (L : Layer (SKM.sig D)) {s t : Sector I}
    (p : SPath L.dom.word s t) (q : SPath L.cod.word s t) (Z : P.H t)
    (h : compLayer gens L p q Z ≠ 0) :
    ∃ (x y : Sector I) (pu : SPath L.left s x) (pg : SPath ((SKM.sig D).dom L.gen) x y)
      (qg : SPath ((SKM.sig D).cod L.gen) x y) (pv : SPath L.right y t),
      p = (pu.append pg).append pv ∧ q = (pu.append qg).append pv ∧
        gens.image L.gen pg qg ((P.pathFunctor pv).obj Z) ≠ 0 := by
  obtain ⟨⟨⟨x, y⟩, pu, pg, pv⟩, rfl⟩ :
      ∃ d : SPath.Dec L.left ((SKM.sig D).dom L.gen) L.right s t, d.path = p :=
    ⟨_, SPath.path_decOf _ _ p⟩
  obtain ⟨⟨⟨x', y'⟩, qu, qg, qv⟩, rfl⟩ :
      ∃ e : SPath.Dec L.left ((SKM.sig D).cod L.gen) L.right s t, e.path = q :=
    ⟨_, SPath.path_decOf _ _ q⟩
  by_cases hout : ((⟨x, pu⟩, ⟨y, pv⟩) : (Σ z, SPath L.left s z) × (Σ z, SPath L.right z t)) =
      (⟨x', qu⟩, ⟨y', qv⟩)
  · simp only [Prod.mk.injEq, Sigma.mk.injEq] at hout
    obtain ⟨⟨rfl, h1⟩, ⟨rfl, h2⟩⟩ := hout
    cases h1; cases h2
    refine ⟨x, y, pu, pg, qg, pv, rfl, rfl, fun hz => h ?_⟩
    change compLayer gens L ((pu.append pg).append pv) ((pu.append qg).append pv) Z = 0
    rw [compLayer_eq, hz]
    simp
  · exact absurd (compLayer_eq_zero gens L _ _ hout Z) h


/-- The summands of the two paths at a nonzero entry of a layer differ only inside the
generator. -/
theorem compLayer_ne_zero_sides (gens : P.Generators) (L : Layer (SKM.sig D)) {s t : Sector I}
    (p : SPath L.dom.word s t) (q : SPath L.cod.word s t) (Z : P.H t)
    (h : compLayer gens L p q Z ≠ 0) :
    ∃ (x y : Sector I) (pu : SPath L.left s x) (pg : SPath ((SKM.sig D).dom L.gen) x y)
      (qg : SPath ((SKM.sig D).cod L.gen) x y) (pv : SPath L.right y t),
      p.sides = pu.sides ++ pg.sides ++ pv.sides ∧ q.sides = pu.sides ++ qg.sides ++ pv.sides := by
  obtain ⟨x, y, pu, pg, qg, pv, rfl, rfl, -⟩ := compLayer_ne_zero gens L p q Z h
  exact ⟨x, y, pu, pg, qg, pv, by simp [SPath.sides_append], by simp [SPath.sides_append]⟩

/-- At a nonzero entry of a cup layer with empty left context, the cup runs through one
summand twice. -/
theorem sides_of_cup (gens : P.Generators) (μ : X) (i : I) (v : List (Letter I))
    {s t : Sector I} (p : SPath (SKM.lay D μ [] (SKM.Shape.cup i) v).dom.word s t)
    (q : SPath (SKM.lay D μ [] (SKM.Shape.cup i) v).cod.word s t) (Z : P.H t)
    (h : compLayer gens (SKM.lay D μ [] (SKM.Shape.cup i) v) p q Z ≠ 0) :
    ∃ σ, q.sides = σ :: σ :: p.sides := by
  obtain ⟨x, y, pu, pg, qg, pv, hp, hq⟩ := compLayer_ne_zero_sides gens _ p q Z h
  obtain ⟨hu, rfl⟩ := SPath.sides_of_nil (pu : SPath [] s x)
  obtain ⟨hg, rfl⟩ := SPath.sides_of_nil (pg : SPath [] s y)
  obtain ⟨σ, hσ⟩ :=
    SPath.side_eq_of_closed (qg : SPath (wd D (SKM.wt D μ v) (SKM.Shape.cup i).cod) s s) (by simp)
  refine ⟨σ, ?_⟩
  rw [hq, hp, hu, hg, hσ]
  rfl

/-- At a nonzero entry of a cap layer with empty right context, the cap runs through one
summand twice. -/
theorem sides_of_cap (gens : P.Generators) (μ : X) (i : I) (u : List (Letter I))
    {s t : Sector I} (p : SPath (SKM.lay D μ u (SKM.Shape.cap i) []).dom.word s t)
    (q : SPath (SKM.lay D μ u (SKM.Shape.cap i) []).cod.word s t) (Z : P.H t)
    (h : compLayer gens (SKM.lay D μ u (SKM.Shape.cap i) []) p q Z ≠ 0) :
    ∃ σ, p.sides = q.sides ++ [σ, σ] := by
  obtain ⟨x, y, pu, pg, qg, pv, hp, hq⟩ := compLayer_ne_zero_sides gens _ p q Z h
  obtain ⟨hv, rfl⟩ := SPath.sides_of_nil (pv : SPath [] y t)
  obtain ⟨hg, rfl⟩ := SPath.sides_of_nil (qg : SPath [] x y)
  obtain ⟨σ, hσ⟩ := SPath.side_eq_of_closed (pg : SPath (wd D μ (SKM.Shape.cap i).dom) x x)
    (by simp)
  refine ⟨σ, ?_⟩
  rw [hq, hp, hv, hg, hσ]
  simp

/-- At a nonzero entry of a distinct-colour upward crossing layer, the crossing exchanges the
summands of its two strands. -/
theorem sides_of_cross (gens : P.Generators) (μ : X) {i j : I} (hij : i ≠ j)
    (u v : List (Letter I)) {s t : Sector I}
    (p : SPath (SKM.lay D μ u (SKM.Shape.cross i j) v).dom.word s t)
    (q : SPath (SKM.lay D μ u (SKM.Shape.cross i j) v).cod.word s t) (Z : P.H t)
    (h : compLayer gens (SKM.lay D μ u (SKM.Shape.cross i j) v) p q Z ≠ 0) :
    ∃ (l r : List Bool) (a b : Bool), l.length = u.length ∧
      p.sides = l ++ [a, b] ++ r ∧ q.sides = l ++ [b, a] ++ r := by
  obtain ⟨x, y, pu, pg, qg, pv, hp, hq⟩ := compLayer_ne_zero_sides gens _ p q Z h
  obtain ⟨a, b, hab⟩ := SPath.exists_sides_pair
    (pg : SPath (wd D (SKM.wt D μ v) (SKM.Shape.cross i j).dom) x y)
  have hba := SPath.sides_upUp hij
    (pg : SPath (wd D (SKM.wt D μ v) (SKM.Shape.cross i j).dom) x y)
    (qg : SPath (wd D (SKM.wt D μ v) (SKM.Shape.cross i j).cod) x y)
  refine ⟨pu.sides, pv.sides, a, b, ?_, ?_, ?_⟩
  · rw [SPath.length_sides]
    exact length_wd _ u
  · rw [hp]; exact congrArg (fun z => pu.sides ++ z ++ pv.sides) hab
  · rw [hq]; exact congrArg (fun z => pu.sides ++ z ++ pv.sides) (hba.trans (by rw [hab]; rfl))

/-- The top of the crossing layer of `sigmaL i j` is the bottom of its cap layer. -/
theorem sigma_cross_cap_word (i j : I) (ν : X) :
    (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]).cod.word =
      (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []).dom.word :=
  (congrArg Obj.word ((SKM.sChain_sigmaL i j).chain D ν).2.2.2.2.2.1).symm

/-- The top of the cap layer of `sigmaL i j` is the word `Fᵢ Eⱼ`. -/
theorem sigma_cap_word (i j : I) (ν : X) :
    wd D ν [dn i, up j] = (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []).cod.word :=
  (congrArg Obj.word ((SKM.sChain_sigmaL i j).chain D ν).2.2.2.2.2.2).symm

theorem compList_cons_eq (gens : P.Generators) (L : Layer (SKM.sig D))
    (ls : List (Layer (SKM.sig D))) {a b : Obj (SKM.sig D)} (h : Chain a (L :: ls) b)
    {s t : Sector I} (p : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t) :
    letI := Fintype.ofFinite (SPath L.cod.word s t)
    compList gens (L :: ls) h p q Z =
      ∑ pm, eqToHom (by rw [P.pathFunctor_cast]) ≫
        compLayer gens L (p.cast (congrArg Obj.word h.2.1.symm)) pm Z ≫
          compList gens ls h.2.2 pm q Z := rfl

theorem ne_zero_of_comp_ne_zero {C : Type*} [Category C] [Preadditive C] {x y z : C}
    {f : x ⟶ y} {g : y ⟶ z} (h : f ≫ g ≠ 0) : f ≠ 0 ∧ g ≠ 0 :=
  ⟨fun hf => h (by rw [hf, Limits.zero_comp]), fun hg => h (by rw [hg, Limits.comp_zero])⟩

theorem compList_nil_of_ne (gens : P.Generators) {a b : Obj (SKM.sig D)} (h : Chain a [] b)
    {s t : Sector I} (n : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t)
    (hn : n.cast (congrArg Obj.word h) ≠ q) : compList gens [] h n q Z = 0 :=
  dite_eq_right hn

theorem compList_nil_of_eq (gens : P.Generators) {a b : Obj (SKM.sig D)} (h : Chain a [] b)
    {s t : Sector I} (n : SPath a.word s t) (q : SPath b.word s t) (Z : P.H t)
    (hn : n.cast (congrArg Obj.word h) = q) :
    compList gens [] h n q Z = eqToHom (by rw [← hn, P.pathFunctor_cast]) :=
  dite_eq_left hn

/-- A nonzero entry of a one-layer list has a nonzero layer entry. -/
theorem compList_one_ne_zero (gens : P.Generators) (L : Layer (SKM.sig D))
    {a b : Obj (SKM.sig D)} (h : Chain a [L] b) {s t : Sector I} (n : SPath a.word s t)
    (q : SPath b.word s t) (Z : P.H t) (hz : compList gens [L] h n q Z ≠ 0) :
    ∃ n' : SPath L.cod.word s t,
      compLayer gens L (n.cast (congrArg Obj.word h.2.1.symm)) n' Z ≠ 0 := by
  rw [compList_cons_eq] at hz
  obtain ⟨n', -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  exact ⟨n', (ne_zero_of_comp_ne_zero (ne_zero_of_comp_ne_zero hn).2).1⟩

/-- A nonzero entry of a two-layer list has nonzero layer entries. -/
theorem compList_two_ne_zero (gens : P.Generators) (L L' : Layer (SKM.sig D))
    {a b : Obj (SKM.sig D)} (h : Chain a [L, L'] b) {s t : Sector I} (n : SPath a.word s t)
    (q : SPath b.word s t) (Z : P.H t) (hz : compList gens [L, L'] h n q Z ≠ 0) :
    ∃ (n₂ : SPath L.cod.word s t) (n₃ : SPath L'.cod.word s t),
      compLayer gens L (n.cast (congrArg Obj.word h.2.1.symm)) n₂ Z ≠ 0 ∧
        compLayer gens L' (n₂.cast (congrArg Obj.word h.2.2.2.1.symm)) n₃ Z ≠ 0 := by
  rw [compList_cons_eq] at hz
  obtain ⟨n₂, -, hn⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  obtain ⟨-, hn⟩ := ne_zero_of_comp_ne_zero hn
  obtain ⟨h₂, hn⟩ := ne_zero_of_comp_ne_zero hn
  obtain ⟨n₃, h₃⟩ := compList_one_ne_zero gens L' h.2.2 n₂ q Z hn
  exact ⟨n₂, n₃, h₂, h₃⟩

/-- The summands at a nonzero term of the entry of `sigmaL i j`, `i ≠ j`. -/
theorem sigma_sides (gens : P.Generators) {i j : I} (hij : i ≠ j) (ν : X) {t s : Sector I}
    (Z : P.H s) {a b : Bool}
    (n₁ : SPath (SKM.lay D ν [] (SKM.Shape.cup i) [up j, dn i]).cod.word t s)
    (hσ : ∃ σ, n₁.sides = [σ, σ, a, b])
    (e₁ : (SKM.lay D ν [] (SKM.Shape.cup i) [up j, dn i]).cod.word =
      (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]).dom.word)
    (n₂ : SPath (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]).cod.word t s)
    (e₂ : (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]).cod.word =
      (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []).dom.word)
    (n₃ : SPath (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []).cod.word t s)
    (z₂ : compLayer gens (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]) (n₁.cast e₁) n₂ Z ≠ 0)
    (z₃ : compLayer gens (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []) (n₂.cast e₂) n₃ Z ≠ 0) :
    n₁.sides = [b, b, a, b] ∧ n₂.sides = [b, a, b, b] ∧ n₃.sides = [b, a] := by
  obtain ⟨σ, hσ⟩ := hσ
  obtain ⟨l, r, a', b', hl, hn₁, hn₂⟩ :=
    sides_of_cross gens ν hij [dn i] [dn i] (n₁.cast e₁) n₂ Z z₂
  obtain ⟨τ, hτ⟩ := sides_of_cap gens ν i [dn i, up j] (n₂.cast e₂) n₃ Z z₃
  rw [SPath.sides_cast, hσ] at hn₁
  rw [SPath.sides_cast, hn₂] at hτ
  have h3 : n₃.sides.length = 2 := by rw [SPath.length_sides]; rfl
  obtain ⟨y, z, hyz⟩ := List.length_eq_two.mp h3
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hl
  rw [hyz] at hτ
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hn₁ hτ
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hn₁
  obtain ⟨rfl, rfl, rfl, h⟩ := hτ
  obtain rfl := List.singleton_inj.mp h
  exact ⟨hσ, by rw [hn₂]; rfl, hyz⟩

/-- **The entry of the sideways crossing is a single composite.** For `i ≠ j` and a path `p`
of `Eⱼ Fᵢ` through the summands `[a, b]`, the only intermediate paths contributing to
`sigmaEntry p q` are the unit path `m₁` through `[b, b, a, b]` and the crossed path `m₂`
through `[b, a, b, b]`. -/
theorem sigmaEntry_eq (c : P.CrossCoeff) {i j : I} (hij : i ≠ j) (ν : X) {t s : Sector I}
    (p : SPath (wd D ν [up j, dn i]) t s) (q : SPath (wd D ν [dn i, up j]) t s)
    (m₁ : SPath (wd D ν [dn i, up i, up j, dn i]) t s)
    (m₂ : SPath (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]).cod.word t s) (Z : P.H s)
    {a b : Bool} (hp : p.sides = [a, b]) (h₁ : m₁.sides = [b, b, a, b])
    (h₂ : m₂.sides = [b, a, b, b]) :
    P.sigmaEntry c i j ν p q Z =
      compLayer (P.upwardGens c) (SKM.lay D ν [] (SKM.Shape.cup i) [up j, dn i]) p m₁ Z ≫
        compLayer (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]) m₁ m₂ Z ≫
          eqToHom (by rw [P.pathFunctor_cast]) ≫
            compLayer (P.upwardGens c) (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) [])
              (m₂.cast (sigma_cross_cap_word i j ν)) (q.cast (sigma_cap_word i j ν)) Z ≫
              eqToHom (by rw [P.pathFunctor_cast]) := by
  classical
  have hc₂ : Chain (SKM.lay D ν [] (SKM.Shape.cup i) [up j, dn i]).cod
      [SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i],
        SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []] (SKM.ob D ν [dn i, up j]) :=
    ((SKM.sChain_sigmaL i j).chain D ν).2.2
  let inst1 := Fintype.ofFinite
    (SPath (SKM.lay D ν [] (SKM.Shape.cup i) [up j, dn i]).cod.word t s)
  have e : P.sigmaEntry c i j ν p q Z =
      ∑ n₁ : SPath (SKM.lay D ν [] (SKM.Shape.cup i) [up j, dn i]).cod.word t s,
        eqToHom rfl ≫
          compLayer (P.upwardGens c) (SKM.lay D ν [] (SKM.Shape.cup i) [up j, dn i]) p n₁ Z ≫
            compList (P.upwardGens c) _ hc₂ n₁ q Z := rfl
  refine e.trans ((Finset.sum_eq_single
    (m₁ : SPath (SKM.lay D ν [] (SKM.Shape.cup i) [up j, dn i]).cod.word t s) ?_ ?_).trans ?_)
  · intro n₁ _ hn
    by_contra hz
    obtain ⟨-, hz⟩ := ne_zero_of_comp_ne_zero hz
    obtain ⟨z₁, hz⟩ := ne_zero_of_comp_ne_zero hz
    obtain ⟨n₂, n₃, z₂, z₃⟩ := compList_two_ne_zero (P.upwardGens c)
      (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i])
      (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []) hc₂ n₁ q Z hz
    obtain ⟨σ, hσ⟩ := sides_of_cup _ ν i [up j, dn i] _ n₁ Z z₁
    rw [hp] at hσ
    obtain ⟨h₁', -⟩ := sigma_sides _ hij ν Z n₁ ⟨σ, hσ⟩ _ n₂ _ n₃ z₂ z₃
    exact hn (SPath.eq_of_sides _ _ (h₁'.trans h₁.symm))
  · exact fun h => (h (@Finset.mem_univ _ inst1 _)).elim
  refine ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _)).trans ?_
  refine congrArg (_ ≫ ·) ?_
  let inst2 := Fintype.ofFinite
    (SPath (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]).cod.word t s)
  have e₂ : compList (P.upwardGens c) _ hc₂ m₁ q Z =
      ∑ n₂ : SPath (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]).cod.word t s,
        eqToHom rfl ≫
          compLayer (P.upwardGens c) (SKM.lay D ν [dn i] (SKM.Shape.cross i j) [dn i]) m₁ n₂ Z ≫
            compList (P.upwardGens c) _ hc₂.2.2 n₂ q Z := rfl
  refine e₂.trans ((Finset.sum_eq_single m₂ ?_ ?_).trans ?_)
  · intro n₂ _ hn
    by_contra hz
    obtain ⟨-, hz⟩ := ne_zero_of_comp_ne_zero hz
    obtain ⟨z₂, hz⟩ := ne_zero_of_comp_ne_zero hz
    obtain ⟨n₃, z₃⟩ := compList_one_ne_zero (P.upwardGens c)
      (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []) hc₂.2.2 n₂ q Z hz
    obtain ⟨-, h₂', -⟩ := sigma_sides (P.upwardGens c) hij ν Z m₁ ⟨b, h₁⟩ rfl n₂ _ n₃ z₂ z₃
    exact hn (SPath.eq_of_sides _ _ (h₂'.trans h₂.symm))
  · exact fun h => (h (@Finset.mem_univ _ inst2 _)).elim
  refine ((congrArg (· ≫ _) (eqToHom_refl _ _)).trans (Category.id_comp _)).trans ?_
  refine congrArg (_ ≫ ·) ?_
  let inst3 := Fintype.ofFinite
    (SPath (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []).cod.word t s)
  have e₃ : compList (P.upwardGens c) _ hc₂.2.2 m₂ q Z =
      ∑ n₃ : SPath (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) []).cod.word t s,
        eqToHom (by rw [P.pathFunctor_cast]) ≫
          compLayer (P.upwardGens c) (SKM.lay D ν [dn i, up j] (SKM.Shape.cap i) [])
            (m₂.cast (sigma_cross_cap_word i j ν)) n₃ Z ≫
            compList (P.upwardGens c) [] hc₂.2.2.2.2 n₃ q Z := rfl
  refine e₃.trans ((Finset.sum_eq_single (q.cast (sigma_cap_word i j ν)) ?_ ?_).trans ?_)
  · intro n₃ _ hn
    rw [compList_nil_of_ne _ _ _ _ _ fun h => hn ?_, Limits.comp_zero, Limits.comp_zero]
    rw [← h, SPath.cast_cast, SPath.cast_self]
  · exact fun h => (h (@Finset.mem_univ _ inst3 _)).elim
  refine (congrArg (fun f => _ ≫ _ ≫ f)
    (compList_nil_of_eq (P.upwardGens c) hc₂.2.2.2.2 _ q Z
      (by rw [SPath.cast_cast, SPath.cast_self]))).trans ?_
  rfl

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly
