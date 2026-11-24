import YM.SU5.Selected.CrossMirror
import YM.SU5.Selected.CapCalc
/-! # Same * on every axis cap algebra

Two commuting candidate *'s on a test system which needn't have C* order, or even
ordinary Euclidean positivity. Use instead *simultaneous* two-cap moments and
each-axis Hilbert structure; together they force the σ_j σ_v = -1 part to descend
to zero as an operator on either axis!
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 230000
set_option quotPrecheck false
noncomputable section

namespace YM.CF.Buffered.Afterglow.Tower.Selection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
open RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
open scoped InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock
open Vacancy

variable {Λ : Preparation} {l : ℕ} (Y : Course Λ (VolumeCape.Dream.Nimbus l))
  (H : Real.exp 1 ≤ Λ.x)
local notation "K" => tent Y H
variable {i k : ℕ → ℕ} {I : ℕ → Family (tent Y H) → ℕ → ℂ}
  {E : ℕ → Family (tent Y H) → ℂ} (V : Universal Y H i k I E)
  {D : ℕ → Family (tent Y H) → Family (tent Y H)} {a b : ℕ → ℕ}
  (Q : Coherent (i := i) (k := k) (E := E) Y H D a b)
  (Qc : Clipped Y H (i ∘ a) (k ∘ b))
  (j : Axis) (r : Bool) (C : Arena Y H Q.circuit j 0 r)
local notation "R" => Aurora Y H V Q j r C
local notation "A" => Ark.Ht Y H Q.circuit j 0 r C
local notation "W" => floorV Y H Q.circuit j 0 r C
local notation "F₊" n:max => Tower.Field Y H n j 0 r
local notation "φ" n:max => actor Y H n Q.circuit j 0 r C
local notation "Ω" => seat0 Y H V Q j r C
local notation "π₀" => (R).orthogonalProjectionOnto
local notation "N" n:max => cap Y H V n Q Qc j r C
local notation "Test" => Vacancy.observable (tent Y H) r
local notation "Lab" => Beacon (tent Y H) r

local notation "B" => groundAlgebra Y H V Q Qc j r C
local notation "M" s:max => liftCap Y H V Q Qc j r C s
variable (v : Axis) (C' : Arena Y H Q.circuit v 0 r)
local notation "R'" => Aurora Y H V Q v r C'
local notation "N'" n:max => cap Y H V n Q Qc v r C'
local notation "Ω'" => seat0 Y H V Q v r C'
include V Q Qc C C'
lemma across_pair (x y : Lab) : inner ℂ Ω ((N x.1) x.2 ((N y.1) y.2 Ω)) =
    inner ℂ Ω' ((N' x.1) x.2 ((N' y.1) y.2 Ω')) := by
  let X : Fin 2 → Lab := ![x,y]
  let P : List (Fin 2) := [0,1]
  have hp : P.Nodup := by unfold P; decide
  change heavies Y H V Q Qc j r C X P = heavies Y H V Q Qc v r C' X P
  by_cases h : j=v; swap
  · exact between_axes Y H V Q Qc j r C X v C' h P P hp (List.Perm.refl P)
  subst v; obtain ⟨d,t⟩ := exists_ne j; obtain ⟨C0⟩ := voyage_H Y H V Q.circuit d 0 r
  rw [between_axes Y H V Q Qc j r C X d C0 t.symm P P hp (.refl P),
    between_axes Y H V Q Qc j r C' X d C0 t.symm P P hp (.refl P)]

lemma across_three (x y z : Lab) : inner ℂ Ω ((N x.1) x.2 ((N y.1) y.2 ((N z.1) z.2 Ω))) =
    inner ℂ Ω' ((N' x.1) x.2 ((N' y.1) y.2 ((N' z.1) z.2 Ω'))) := by
  let X : Fin 3 → Lab := ![x,y,z]; let P : List (Fin 3) := [0,1,2]; have hp : P.Nodup := by unfold P; decide
  change heavies Y H V Q Qc j r C X P = heavies Y H V Q Qc v r C' X P
  by_cases h : j=v
  · subst v; obtain ⟨d,t⟩ := exists_ne j; obtain ⟨C0⟩ := voyage_H Y H V Q.circuit d 0 r
    rw [between_axes Y H V Q Qc j r C X d C0 t.symm P P hp (.refl P),
      between_axes Y H V Q Qc j r C' X d C0 t.symm P P hp (.refl P)]
  exact between_axes Y H V Q Qc j r C X v C' h P P hp (List.Perm.refl P)

omit V Q Qc C C'
private def diffF (X X' : Vacancy.observable K r) : Test := combined r X (weighted r X' (-1)) -- Y shadow error
private lemma diffF_val (x y : Test) : (diffF Y H r x y).val=x.val-y.val:=
  show x.val+(-1:ℂ) • y.val=x.val-y.val by rw [neg_one_smul, ←sub_eq_add_neg]
lemma dual_affine (X X' : Test) : dual Y H j r (diffF Y H r X X') = diffF Y H r (dual Y H j r X) (dual Y H j r X') := by
  apply Subtype.ext
  change mirror (tent Y H) j 0 _=_; rw [diffF_val,diffF_val,Tower.foil]; rfl

lemma dual_back (X : Test) : dual Y H j r (dual Y H j r X)=X:=Subtype.ext (mirror_invert _ _ _ X.property.1)
lemma cross_dual (X : Test) : dual Y H v r (dual Y H j r X)=dual Y H j r (dual Y H v r X):=by
  by_cases p:v=j; · subst v; rfl
  exact Subtype.ext (mirrors_commute v j p 0 0 X.val X.property.1)

include V Q Qc C
lemma diff_cap (s : ℕ) (x y : Test) : (M s) (diffF Y H r x y)=(M s) x-(M s) y:=by
  unfold diffF; rw [read_add,read_scale,neg_one_smul,←sub_eq_add_neg]

-- do without C' on interface eventually
private lemma zero_observation (s : ℕ) (X : Test) (h : (N s) X Ω = 0) : (M s) X=0 := distinguish Y H V Q Qc j r C _ _ h

lemma dual_reading (s : ℕ) (X : Test) : (M s) (dual Y H j r X) = (M s) (dual Y H v r X) := by
  obtain ⟨C'⟩ := voyage_H Y H V Q.circuit v 0 r
  let Ω₂ := seat0 Y H V Q v r C'
  let a (i : Test) := cap Y H V s Q Qc v r C' i
  let T := diffF Y H r (dual Y H j r X) (dual Y H v r X)
  let f := dual Y H j r T
  let x := (N s) T Ω; let y := a T Ω₂
  have hv : a f = -(a T).adjoint := by
    rw [show (a T).adjoint=a (dual Y H v r T) from mirror_cap ..]
    let g := liftCap Y H V Q Qc v r C' s
    suffices h : g f = -g (dual Y H v r T) from congrArg Subtype.val h
    unfold f T g; rw [dual_affine,dual_affine, cross_dual Y H j r v,dual_back,dual_back,
      diff_cap,diff_cap]; abel
  have he0 := across_pair Y H V Q Qc j r C v C' (s,f) (s,T)
  change inner ℂ Ω ((N s) f x) = inner ℂ Ω₂ (a f y) at he0
  rw [←show ((N s) T).adjoint=(N s) f from mirror_cap .., hv, ContinuousLinearMap.adjoint_inner_right] at he0
  have he : inner ℂ x x = -inner ℂ y y := he0.trans (by
    rw [ContinuousLinearMap.neg_apply,inner_neg_right,ContinuousLinearMap.adjoint_inner_right]) -- maybe need rfl
  have h : inner ℂ x x = 0 := le_antisymm (le_of_eq_of_le he (by
    exact neg_nonpos_of_nonneg (ContinuousLinearMap.isPositive_one (𝕜:=ℂ) |>.inner_nonneg_left y))) (ContinuousLinearMap.isPositive_one (𝕜:=ℂ) |>.inner_nonneg_left x)
  have ha := zero_observation Y H V Q Qc j r C s T (inner_self_eq_zero.mp h)
  apply sub_eq_zero.mp; rwa [show (M s) T = _ from diff_cap Y H V Q Qc j r C s _ _] at ha

lemma dual_any (s : ℕ) (X : Test) : (N s) (dual Y H v r X) = ((N s) X).adjoint := by
  have he : (M s) (dual Y H v r X)=star ((M s) X):=(dual_reading Y H V Q Qc j r C v s X).symm.trans (read_mirror ..)
  exact congrArg Subtype.val he

include C'
lemma same_inner (x y : Lab) : inner ℂ ((N x.1) x.2 Ω) ((N y.1) y.2 Ω) =
    inner ℂ ((N' x.1) x.2 Ω') ((N' y.1) y.2 Ω') := by
  let X := dual Y H j r x.2
  have he := across_pair Y H V Q Qc j r C v C' (x.1,X) y
  change inner ℂ Ω ((N x.1) X _) = inner ℂ Ω' ((N' x.1) X _) at he
  rw [show (N x.1) X =_ from dual_any Y H V Q Qc j r C j x.1 x.2,
    show (N' x.1) X =_ from dual_any Y H V Q Qc v r C' j x.1 x.2,
    ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right] at he
  exact he
end YM.CF.Buffered.Afterglow.Tower.Selection
