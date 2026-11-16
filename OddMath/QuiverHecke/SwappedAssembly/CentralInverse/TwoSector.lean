/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.BlockMaps

/-! # The two-sector central block

§§4–6 of `docs/Nondegeneracy/SwappedHomInversion.md`, in an arbitrary preadditive category,
in the form used for the central block of the equal-colour augmented maps
(`docs/Nondegeneracy/AugmentedSectorBlocks.md` §3).

The central block has two sectors: the reservoir `R` (objects `X_R`, `Y_R`, crossing `s_R`,
dotted caps `v_R a` and cups `u_R a`) and the probe `P` (objects `X_P`, `Y_P`, crossing
`s_P`), coupled by the two central entries `Cx : X_R ⟶ Y_P` (`D_PR` there) and
`Dx : X_P ⟶ Y_R` (`C_RP` there). With `H` cap windows (`H ≥ 0`) the map is
`X_R ⊕ X_P ⟶ Y_R ⊕ Y_P ⊕ Oᴴ` (`ProbeWindow.posMap`), and with `G` cup windows it is
`X_R ⊕ X_P ⊕ Oᴳ ⟶ Y_R ⊕ Y_P` (`ProbeWindow.negMap`).

The reservoir window is invertible: a cap window `[s_R; v_R n]_{n<h}` with inverse
`(j_R, A_R)` when its height is `h ≥ 0`, a cup window `[s_R, u_R n]_{n<b}` with inverse
`(j_R, B_R)` when it is `-b < 0`. Eliminating it exactly leaves a reservoir identity block next
to a probe residual `ProbeWindow.gMap`, up to explicit source and target isomorphisms, so each
of the four maps is invertible as soon as its probe residual is (`ProbeWindow.isIso_posMap_of_cap`,
`isIso_posMap_of_cup`, `isIso_negMap_of_cap`, `isIso_negMap_of_cup`). No hypothesis beyond the
reservoir window inverse is used: the probe residuals carry the contracted closures
`Dx ≫ j_R ≫ Cx`, `Dx ≫ j_R ≫ v_R a`, `u_R a ≫ j_R ≫ Cx` ((9) there) and the contractions
`A_R n ≫ v_R a`, `u_R a ≫ B_R n` ((7) there) as entries. Modulo the coefficient ideal `J` of §4
there the residuals are the auxiliary maps of cases (a)–(d) of
`docs/Nondegeneracy/ProbeWindowInverse.md`; `ProbeWindow.CoefficientIdeal.isIso_of_sub_mem`
lifts their invertibility.
-/

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- Close an entry equation of a product of `tMap`s. -/
local macro "tfin" : tactic => `(tactic|
  (try simp only [Pi.zero_apply] at *) <;> (try block_norm) <;>
  (first | done | (simp_all [comp_ite, ite_comp]; done) | abel | (simp_all; done)))

section TObj

variable {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ]

/-- The object `Z ⊕ Y ⊕ Oᶥ` of `Mat_ C`. -/
abbrev tObj (Z Y O : C) (ι : Type) [Fintype ι] [DecidableEq ι] : Mat_ C where
  ι := Option (Option ι)
  X o := @Option.rec (Option ι) (fun _ => C) Z
    (fun o' => @Option.rec ι (fun _ => C) Y (fun _ => O) o') o

/-- The block map `Z ⊕ X ⊕ Oᶥ ⟶ Z' ⊕ Y ⊕ Oᵏ` with its nine blocks (rows: source summand). -/
def tMap {Z Z' X Y O : C}
    (zz : Z ⟶ Z') (zy : Z ⟶ Y) (zo : κ → (Z ⟶ O))
    (xz : X ⟶ Z') (xy : X ⟶ Y) (xo : κ → (X ⟶ O))
    (oz : ι → (O ⟶ Z')) (oy : ι → (O ⟶ Y)) (oo : ι → κ → (O ⟶ O)) :
    tObj Z X O ι ⟶ tObj Z' Y O κ :=
  fun o o' => match o, o' with
    | none, none => zz
    | none, some none => zy
    | none, some (some r) => zo r
    | some none, none => xz
    | some none, some none => xy
    | some none, some (some r) => xo r
    | some (some i), none => oz i
    | some (some i), some none => oy i
    | some (some i), some (some r) => oo i r

lemma tMap_comp {Z Z' Z'' X Y W O : C}
    (zz : Z ⟶ Z') (zy : Z ⟶ Y) (zo : κ → (Z ⟶ O))
    (xz : X ⟶ Z') (xy : X ⟶ Y) (xo : κ → (X ⟶ O))
    (oz : ι → (O ⟶ Z')) (oy : ι → (O ⟶ Y)) (oo : ι → κ → (O ⟶ O))
    (zz' : Z' ⟶ Z'') (zy' : Z' ⟶ W) (zo' : μ → (Z' ⟶ O))
    (xz' : Y ⟶ Z'') (xy' : Y ⟶ W) (xo' : μ → (Y ⟶ O))
    (oz' : κ → (O ⟶ Z'')) (oy' : κ → (O ⟶ W)) (oo' : κ → μ → (O ⟶ O)) :
    tMap zz zy zo xz xy xo oz oy oo ≫ tMap zz' zy' zo' xz' xy' xo' oz' oy' oo' =
      tMap (zz ≫ zz' + zy ≫ xz' + ∑ r, zo r ≫ oz' r)
        (zz ≫ zy' + zy ≫ xy' + ∑ r, zo r ≫ oy' r)
        (fun m => zz ≫ zo' m + zy ≫ xo' m + ∑ r, zo r ≫ oo' r m)
        (xz ≫ zz' + xy ≫ xz' + ∑ r, xo r ≫ oz' r)
        (xz ≫ zy' + xy ≫ xy' + ∑ r, xo r ≫ oy' r)
        (fun m => xz ≫ zo' m + xy ≫ xo' m + ∑ r, xo r ≫ oo' r m)
        (fun i => oz i ≫ zz' + oy i ≫ xz' + ∑ r, oo i r ≫ oz' r)
        (fun i => oz i ≫ zy' + oy i ≫ xy' + ∑ r, oo i r ≫ oy' r)
        (fun i m => oz i ≫ zo' m + oy i ≫ xo' m + ∑ r, oo i r ≫ oo' r m) := by
  ext o o'
  rw [Mat_.comp_apply, Fintype.sum_option, Fintype.sum_option, ← add_assoc]
  rcases o with _ | _ | i <;> rcases o' with _ | _ | m <;> rfl

lemma tMap_id (Z Y O : C) :
    𝟙 (tObj Z Y O κ) = tMap (𝟙 Z) 0 0 0 (𝟙 Y) 0 0 0
      (fun r r' => if r = r' then 𝟙 O else 0) := by
  ext o o'
  rcases o with _ | _ | r <;> rcases o' with _ | _ | r'
  · exact Mat_.id_apply_self _ _
  · exact Mat_.id_apply_of_ne _ _ _ (by simp)
  · exact Mat_.id_apply_of_ne _ _ _ (by simp)
  · exact Mat_.id_apply_of_ne _ _ _ (by simp)
  · exact Mat_.id_apply_self _ _
  · exact Mat_.id_apply_of_ne _ _ _ (by simp)
  · exact Mat_.id_apply_of_ne _ _ _ (by simp)
  · exact Mat_.id_apply_of_ne _ _ _ (by simp)
  · by_cases h : r = r'
    · subst h; simp only [tMap, ↓reduceIte]; exact Mat_.id_apply_self _ _
    · simp only [tMap, h, ↓reduceIte]
      exact Mat_.id_apply_of_ne _ _ _ (by simpa using h)

lemma tMap_congr {Z Z' X Y O : C}
    {zz zz' : Z ⟶ Z'} {zy zy' : Z ⟶ Y} {zo zo' : κ → (Z ⟶ O)}
    {xz xz' : X ⟶ Z'} {xy xy' : X ⟶ Y} {xo xo' : κ → (X ⟶ O)}
    {oz oz' : ι → (O ⟶ Z')} {oy oy' : ι → (O ⟶ Y)} {oo oo' : ι → κ → (O ⟶ O)}
    (h1 : zz = zz') (h2 : zy = zy') (h3 : ∀ r, zo r = zo' r)
    (h4 : xz = xz') (h5 : xy = xy') (h6 : ∀ r, xo r = xo' r)
    (h7 : ∀ i, oz i = oz' i) (h8 : ∀ i, oy i = oy' i) (h9 : ∀ i r, oo i r = oo' i r) :
    tMap zz zy zo xz xy xo oz oy oo = tMap zz' zy' zo' xz' xy' xo' oz' oy' oo' := by
  subst h1 h2 h4 h5
  obtain rfl : zo = zo' := funext h3
  obtain rfl : xo = xo' := funext h6
  obtain rfl : oz = oz' := funext h7
  obtain rfl : oy = oy' := funext h8
  obtain rfl : oo = oo' := funext fun i => funext (h9 i)
  rfl

/-- A reservoir identity block next to an invertible auxiliary map is invertible. -/
theorem isIso_tMap_diag {Z X Y O : C} (a : X ⟶ Y) (B : ι → (O ⟶ Y)) (Cc : κ → (X ⟶ O))
    (E : ι → κ → (O ⟶ O)) (h : IsIso (gMap a B Cc E)) :
    IsIso (tMap (𝟙 Z) 0 0 0 a Cc 0 B E) := by
  obtain ⟨g, hg1, hg2⟩ := h
  rw [gMap_eta g, gMap_comp, gMap_id] at hg1 hg2
  have e1 := fun o o' => congrFun (congrFun hg1 o) o'
  have e2 := fun o o' => congrFun (congrFun hg2 o) o'
  refine ⟨tMap (𝟙 Z) 0 0 0 (g none none) (fun r => g none (some r)) 0
    (fun i => g (some i) none) (fun i r => g (some i) (some r)), ?_, ?_⟩
  · rw [tMap_comp, tMap_id]
    refine tMap_congr (by simp) (by simp) (fun r => by simp) (by simp) ?_ (fun r => ?_)
      (fun i => by simp) (fun i => ?_) (fun i r => ?_)
    · simpa using e1 none none
    · simpa using e1 none (some r)
    · simpa using e1 (some i) none
    · simpa using e1 (some i) (some r)
  · rw [tMap_comp, tMap_id]
    refine tMap_congr (by simp) (by simp) (fun r => by simp) (by simp) ?_ (fun r => ?_)
      (fun i => by simp) (fun i => ?_) (fun i r => ?_)
    · simpa using e2 none none
    · simpa using e2 none (some r)
    · simpa using e2 (some i) none
    · simpa using e2 (some i) (some r)

/-- The upper shear `(z, y, o) ↦ (z, y + z ≫ zy, o + z ≫ zo)` is invertible. -/
instance isIso_tShear {Z Y O : C} (zy : Z ⟶ Y) (zo : κ → (Z ⟶ O)) :
    IsIso (tMap (𝟙 Z) zy zo 0 (𝟙 Y) 0 0 0 (fun r r' => if r = r' then 𝟙 O else 0)) := by
  refine ⟨tMap (𝟙 Z) (-zy) (fun r => -zo r) 0 (𝟙 Y) 0 0 0
    (fun r r' => if r = r' then 𝟙 O else 0), ?_, ?_⟩ <;>
  · rw [tMap_comp, tMap_id]
    refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
      (fun i r => ?_) <;> simp [comp_ite]

/-- The lower shear `(z, x, o) ↦ (z + x ≫ xz + o ≫ oz, x, o)` is invertible. -/
instance isIso_tLowerShear {Z X O : C} (xz : X ⟶ Z) (oz : κ → (O ⟶ Z)) :
    IsIso (tMap (𝟙 Z) 0 0 xz (𝟙 X) 0 oz 0 (fun r r' => if r = r' then 𝟙 O else 0) :
      tObj Z X O κ ⟶ _) := by
  refine ⟨tMap (𝟙 Z) 0 0 (-xz) (𝟙 X) 0 (fun r => -oz r) 0
    (fun r r' => if r = r' then 𝟙 O else 0), ?_, ?_⟩ <;>
  · rw [tMap_comp, tMap_id]
    refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
      (fun i r => ?_) <;> simp [comp_ite, ite_comp]

end TObj

omit [Preadditive C] in
/-- If `S ≫ F = M ≫ T` with `S`, `M`, `T` invertible, then `F` is invertible. -/
theorem isIso_of_comp_eq_comp {A A' B B' : C} (S : A' ⟶ A) (F : A ⟶ B) (M : A' ⟶ B')
    (T : B' ⟶ B) (hS : IsIso S) (hM : IsIso M) (hT : IsIso T) (h : S ≫ F = M ≫ T) :
    IsIso F := by
  have : F = inv S ≫ M ≫ T := by rw [← h, IsIso.inv_hom_id_assoc]
  rw [this]
  infer_instance

section TwoSector

/-- The cup-window expansion `f = f ≫ j ≫ s + Σ f ≫ D n ≫ w n`. -/
lemma IsCupInverse.neg_add_eq {X Y O W : C} {b : ℕ} {s : X ⟶ Y} {w : Fin b → (O ⟶ Y)}
    {j : Y ⟶ X} {D : Fin b → (Y ⟶ O)} (H : IsCupInverse s w j D) (f : W ⟶ Y) :
    -(f ≫ j ≫ s) + f = ∑ n, f ≫ D n ≫ w n := by
  obtain ⟨-, -, -, -, h5⟩ := H
  calc -(f ≫ j ≫ s) + f = -(f ≫ j ≫ s) + f ≫ 𝟙 Y := by rw [Category.comp_id]
    _ = _ := by
      rw [← h5, Preadditive.comp_add, Preadditive.comp_sum]
      abel

variable {XR YR XP YP O : C} (sR : XR ⟶ YR) (sP : XP ⟶ YP) (Cx : XR ⟶ YP) (Dx : XP ⟶ YR)
  (vR : ℕ → (XR ⟶ O)) (uR : ℕ → (O ⟶ YR))

/-- The two-sector map with `H` cap windows, `X_R ⊕ X_P ⟶ Y_R ⊕ Y_P ⊕ Oᴴ`: the central block
`[[s_R, Cx], [Dx, s_P]]` and the fused window rows `[v_R a, rowP a]` (`SwappedHomInversion.md`
§6, `F_+`). -/
def posMap {H : ℕ} (rowP : Fin H → (XP ⟶ O)) : tObj XR XP O Empty ⟶ tObj YR YP O (Fin H) :=
  tMap sR Cx (fun a => vR a) Dx sP rowP 0 0 0

/-- The two-sector map with `G` cup windows, `X_R ⊕ X_P ⊕ Oᴳ ⟶ Y_R ⊕ Y_P`: the central block
and the fused window columns `[u_R a, colP a]` (`SwappedHomInversion.md` §6, `F_-`). -/
def negMap {G : ℕ} (colP : Fin G → (O ⟶ YP)) : tObj XR XP O (Fin G) ⟶ tObj YR YP O Empty :=
  tMap sR Cx 0 Dx sP 0 (fun a => uR a) colP 0

variable {sR sP Cx Dx vR uR}

/-- **Two sectors, `H ≥ 0` probe windows, reservoir cap window.** If the reservoir cap window
`[s_R; v_R n]_{n<h}` has the entrywise inverse `(j_R, A_R)`, then `posMap` is invertible as soon
as the probe residual
`[s_P - Dx ≫ j_R ≫ Cx, A_R n ≫ Cx; rowP a - Dx ≫ j_R ≫ v_R a, A_R n ≫ v_R a] :
X_P ⊕ Oʰ ⟶ Y_P ⊕ Oᴴ` is. -/
theorem isIso_posMap_of_cap {h H : ℕ} (rowP : Fin H → (XP ⟶ O)) {jR : YR ⟶ XR}
    {AR : Fin h → (O ⟶ XR)} (hR : IsCapInverse sR (fun n => vR n) jR AR)
    (hG : IsIso (gMap (sP - Dx ≫ jR ≫ Cx) (fun n => AR n ≫ Cx)
      (fun a => rowP a - Dx ≫ jR ≫ vR a) (fun (n : Fin h) (a : Fin H) => AR n ≫ vR a))) :
    IsIso (posMap sR sP Cx Dx vR rowP) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hR
  have h1' : ∀ {W : C} (g : YR ⟶ W), jR ≫ sR ≫ g = g := fun g => by rw [reassoc_of% h1]
  have hM := isIso_tMap_diag (Z := YR) _ _ _ _ hG
  let S : tObj YR XP O (Fin h) ⟶ tObj XR XP O Empty :=
    tMap jR 0 0 (-(Dx ≫ jR)) (𝟙 XP) 0 (fun n => AR n) 0 0
  let T : tObj YR YP O (Fin H) ⟶ tObj YR YP O (Fin H) :=
    tMap (𝟙 YR) (jR ≫ Cx) (fun a => jR ≫ vR a) 0 (𝟙 YP) 0 0 0
      (fun r r' => if r = r' then 𝟙 O else 0)
  have hS : IsIso S := by
    refine ⟨tMap sR 0 (fun n => vR n) Dx (𝟙 XP) 0 0 0 0, ?_, ?_⟩
    · rw [tMap_comp, tMap_id]
      refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
        (fun i r => ?_)
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
    · rw [tMap_comp, tMap_id]
      refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
        (fun i r => ?_)
      · tfin
      · tfin
      · exact r.elim
      · tfin
      · tfin
      · exact r.elim
      · exact i.elim
      · exact i.elim
      · exact i.elim
  have hT : IsIso T := isIso_tShear _ _
  refine isIso_of_comp_eq_comp S _ _ T hS hM hT ?_
  simp only [S, T, posMap]
  rw [tMap_comp, tMap_comp]
  refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
    (fun i r => ?_)
  · tfin
  · tfin
  · tfin
  · tfin
  · tfin
  · tfin
  · tfin
  · tfin
  · tfin

/-- **Two sectors, `H ≥ 0` probe windows, reservoir cup window.** If the reservoir cup window
`[s_R, u_R n]_{n<b}` has the entrywise inverse `(j_R, B_R)`, then `posMap` is invertible as soon
as the probe residual
`[s_P - Dx ≫ j_R ≫ Cx; rowP a - Dx ≫ j_R ≫ v_R a, Dx ≫ B_R n] : X_P ⟶ Y_P ⊕ Oᴴ ⊕ Oᵇ` is. -/
theorem isIso_posMap_of_cup {b H : ℕ} (rowP : Fin H → (XP ⟶ O)) {jR : YR ⟶ XR}
    {BR : Fin b → (YR ⟶ O)} (hR : IsCupInverse sR (fun n => uR n) jR BR)
    (hG : IsIso (gMap (sP - Dx ≫ jR ≫ Cx) (fun e : Empty => e.elim)
      (Sum.elim (fun a => rowP a - Dx ≫ jR ≫ vR a) fun n => Dx ≫ BR n)
      (fun e _ => e.elim))) :
    IsIso (posMap sR sP Cx Dx vR rowP) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := id hR
  have h1' : ∀ {W : C} (g : XR ⟶ W), sR ≫ jR ≫ g = g := fun g => by rw [reassoc_of% h1]
  have h3' : ∀ (n : Fin b) {W : C} (g : XR ⟶ W), uR n ≫ jR ≫ g = 0 := fun n {_} g => by
    simpa using h3 n =≫ g
  have hM := isIso_tMap_diag (Z := XR) _ _ _ _ hG
  let S : tObj XR XP O Empty ⟶ tObj XR XP O Empty :=
    tMap (𝟙 XR) 0 0 (-(Dx ≫ jR)) (𝟙 XP) 0 0 0 (fun r r' => if r = r' then 𝟙 O else 0)
  let T : tObj XR YP O (Fin H ⊕ Fin b) ⟶ tObj YR YP O (Fin H) :=
    tMap sR Cx (fun a => vR a) 0 (𝟙 YP) 0 (Sum.elim 0 fun n => uR n) 0
      (Sum.elim (fun r r' => if r = r' then 𝟙 O else 0) 0)
  have hS : IsIso S := isIso_tLowerShear _ _
  have hT : IsIso T := by
    refine ⟨tMap jR (-(jR ≫ Cx)) (Sum.elim (fun a => -(jR ≫ vR a)) BR) 0 (𝟙 YP) 0 0 0
      (fun r => Sum.elim (fun r' => if r = r' then 𝟙 O else 0) 0), ?_, ?_⟩
    · rw [tMap_comp, tMap_id]
      refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
        (fun i r => ?_)
      · tfin
      · tfin
      · rcases r with r | r <;> tfin
      · tfin
      · tfin
      · tfin
      · rcases i with i | i <;> tfin
      · rcases i with i | i <;> tfin
      · rcases i with i | i <;> rcases r with r | r <;> tfin
    · rw [tMap_comp, tMap_id]
      refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
        (fun i r => ?_)
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
  refine isIso_of_comp_eq_comp S _ _ T hS hM hT ?_
  simp only [S, T, posMap]
  rw [tMap_comp, tMap_comp]
  refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
    (fun i r => ?_)
  · tfin
  · tfin
  · tfin
  · try block_norm
    simpa using hR.neg_add_eq Dx
  · tfin
  · try block_norm
    simp
    abel
  · exact i.elim
  · exact i.elim
  · exact i.elim

/-- **Two sectors, `G` cup windows, reservoir cap window.** If the reservoir cap window
`[s_R; v_R n]_{n<h}` has the entrywise inverse `(j_R, A_R)`, then `negMap` is invertible as soon
as the probe residual `[s_P - Dx ≫ j_R ≫ Cx, (A_R n ≫ Cx, colP a - u_R a ≫ j_R ≫ Cx)] :
X_P ⊕ Oʰ ⊕ Oᴳ ⟶ Y_P` is. -/
theorem isIso_negMap_of_cap {h G : ℕ} (colP : Fin G → (O ⟶ YP)) {jR : YR ⟶ XR}
    {AR : Fin h → (O ⟶ XR)} (hR : IsCapInverse sR (fun n => vR n) jR AR)
    (hG : IsIso (gMap (sP - Dx ≫ jR ≫ Cx)
      (Sum.elim (fun n => AR n ≫ Cx) fun a => colP a - uR a ≫ jR ≫ Cx)
      (fun e : Empty => e.elim) (fun _ e => e.elim))) :
    IsIso (negMap sR sP Cx Dx uR colP) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hR
  have h1' : ∀ {W : C} (g : YR ⟶ W), jR ≫ sR ≫ g = g := fun g => by rw [reassoc_of% h1]
  have h3' : ∀ (n : Fin h) {W : C} (g : W ⟶ YR), g ≫ jR ≫ vR n = 0 := fun n {_} g => by
    simpa using g ≫= h3 n
  have hM := isIso_tMap_diag (Z := YR) _ _ _ _ hG
  let S : tObj YR XP O (Fin h ⊕ Fin G) ⟶ tObj XR XP O (Fin G) :=
    tMap jR 0 0 (-(Dx ≫ jR)) (𝟙 XP) 0 (Sum.elim AR fun a => -(uR a ≫ jR)) 0
      (Sum.elim 0 fun r r' => if r = r' then 𝟙 O else 0)
  let T : tObj YR YP O Empty ⟶ tObj YR YP O Empty :=
    tMap (𝟙 YR) (jR ≫ Cx) 0 0 (𝟙 YP) 0 0 0 (fun r r' => if r = r' then 𝟙 O else 0)
  have hS : IsIso S := by
    refine ⟨tMap sR 0 (Sum.elim (fun n => vR n) 0) Dx (𝟙 XP) 0 (fun a => uR a) 0
      (fun r => Sum.elim 0 fun r' => if r = r' then 𝟙 O else 0), ?_, ?_⟩
    · rw [tMap_comp, tMap_id]
      refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
        (fun i r => ?_)
      · tfin
      · tfin
      · rcases r with r | r <;> tfin
      · tfin
      · tfin
      · rcases r with r | r <;> tfin
      · rcases i with i | i <;> tfin
      · rcases i with i | i <;> tfin
      · rcases i with i | i <;> rcases r with r | r <;> tfin
    · rw [tMap_comp, tMap_id]
      refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
        (fun i r => ?_)
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
  have hT : IsIso T := isIso_tShear _ _
  refine isIso_of_comp_eq_comp S _ _ T hS hM hT ?_
  simp only [S, T, negMap]
  rw [tMap_comp, tMap_comp]
  refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
    (fun i r => ?_)
  · tfin
  · tfin
  · exact r.elim
  · tfin
  · tfin
  · exact r.elim
  · rcases i with i | i <;> tfin
  · rcases i with i | i <;> tfin
  · exact r.elim

/-- **Two sectors, `G` cup windows, reservoir cup window.** If the reservoir cup window
`[s_R, u_R n]_{n<b}` has the entrywise inverse `(j_R, B_R)`, then `negMap` is invertible as soon
as the probe residual `[s_P - Dx ≫ j_R ≫ Cx, colP a - u_R a ≫ j_R ≫ Cx; Dx ≫ B_R n,
u_R a ≫ B_R n] : X_P ⊕ Oᴳ ⟶ Y_P ⊕ Oᵇ` is. -/
theorem isIso_negMap_of_cup {b G : ℕ} (colP : Fin G → (O ⟶ YP)) {jR : YR ⟶ XR}
    {BR : Fin b → (YR ⟶ O)} (hR : IsCupInverse sR (fun n => uR n) jR BR)
    (hG : IsIso (gMap (sP - Dx ≫ jR ≫ Cx) (fun a => colP a - uR a ≫ jR ≫ Cx)
      (fun n => Dx ≫ BR n) (fun (a : Fin G) n => uR a ≫ BR n))) :
    IsIso (negMap sR sP Cx Dx uR colP) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := id hR
  have h1' : ∀ {W : C} (g : XR ⟶ W), sR ≫ jR ≫ g = g := fun g => by rw [reassoc_of% h1]
  have h3' : ∀ (n : Fin b) {W : C} (g : XR ⟶ W), uR n ≫ jR ≫ g = 0 := fun n {_} g => by
    simpa using h3 n =≫ g
  have hM := isIso_tMap_diag (Z := XR) _ _ _ _ hG
  let S : tObj XR XP O (Fin G) ⟶ tObj XR XP O (Fin G) :=
    tMap (𝟙 XR) 0 0 (-(Dx ≫ jR)) (𝟙 XP) 0 (fun a => -(uR a ≫ jR)) 0
      (fun r r' => if r = r' then 𝟙 O else 0)
  let T : tObj XR YP O (Fin b) ⟶ tObj YR YP O Empty :=
    tMap sR Cx 0 0 (𝟙 YP) 0 (fun n => uR n) 0 0
  have hS : IsIso S := isIso_tLowerShear _ _
  have hT : IsIso T := by
    refine ⟨tMap jR (-(jR ≫ Cx)) BR 0 (𝟙 YP) 0 0 0 0, ?_, ?_⟩
    · rw [tMap_comp, tMap_id]
      refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
        (fun i r => ?_)
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
      · tfin
    · rw [tMap_comp, tMap_id]
      refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
        (fun i r => ?_)
      · tfin
      · tfin
      · exact r.elim
      · tfin
      · tfin
      · exact r.elim
      · exact i.elim
      · exact i.elim
      · exact i.elim
  refine isIso_of_comp_eq_comp S _ _ T hS hM hT ?_
  simp only [S, T, negMap]
  rw [tMap_comp, tMap_comp]
  refine tMap_congr ?_ ?_ (fun r => ?_) ?_ ?_ (fun r => ?_) (fun i => ?_) (fun i => ?_)
    (fun i r => ?_)
  · tfin
  · tfin
  · exact r.elim
  · try block_norm
    simpa using hR.neg_add_eq Dx
  · tfin
  · exact r.elim
  · try block_norm
    simpa using hR.neg_add_eq (uR i)
  · tfin
  · exact r.elim

end TwoSector

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
