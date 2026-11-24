import YM.Sextet.Difference
import YM.Sextet.PoseMark
 
/-!
# Raw position charges of pairs (independent points on an implementing grid)

An exact derivation before passing to any continuous-sector projection. Uses the same selected
vectors of the singlet increments; in these calculations all *singleState* readings use one
common election, via `single_agrees`.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
section AimVector
variable (P:Spine) (j:Axis) (x:P.Spectrum0 j) (t:ℕ) (r:Cover)

lemma cruise_luggage (f:P.Test) (L:List (Trans j)) :
    P.cruise (Vacancy.spare j L) r f = P.luggage j L (fun i => r i.val) f := by
  induction L with
  | nil => rfl
  | cons i L h=>
    rw [P.ship_started,←h]; rfl

/-- Position a birth-ticket anywhere on the measured grid with nonnegative center coord j.
This charges exactly the heat for the time-advance and the unitary shift *in the possibly
discontinuous sector* at that same grid pose. -/
lemma birth_aim_full (A:P.Apron) (s:A.s≤t) (f:P.birthF j A.s A.F)
    (h:0≤P.grid t r j) :
    ∃ a:P.birthF j t (P.aimMark A t r),
    P.viewF j x t a=
      P.truck j x (P.vtile t r)
        ((P.physicalEnergy j x).E (Real.toNNReal (P.grid t r j)) (P.viewF j x A.s f)) := by
  have hr: (0:ℝ)≤r j := nonneg_of_mul_nonneg_right ((P.grid_eq t r j) ▸ h) (P.macroTick_pos t)
  have hb : ∃ b:ℕ,(b:ℤ)=r j := by exact ⟨_,Int.toNat_of_nonneg (by exact_mod_cast hr)⟩
  obtain ⟨b,hb⟩:=hb
  have he:Real.toNNReal (P.grid t r j)=whenly (timeMesh P.par) t b := by
    ext; rw [Real.coe_toNNReal _ h,P.grid_eq,←hb]; simp [whenly,macroTick,mul_comm]
  let a:= P.rig j A.s t f s
  let c:= P.passesLater j t b a
  let d:= P.certify j t (look j) (fun i=>r i.val) c
  let z:=A.full P t
  have ez:P.aimMark A t r=
      P.luggage j (look j) (fun i=>r i.val) (P.shifts j b z) := by
    unfold z aimMark; rw [←P.cruise_luggage, P.cruise_mesh,hb,P.chart_transverse]
  refine ⟨ez.symm ▸ d,?_⟩
  rw [he,←P.view_rig j x A.s t f s]
  have p:= (P.ship_ideal j x t (look j) (fun i=>r i.val) c).trans
       (congrArg (P.truck j x (P.vtile t r)) (P.releasedLater j x t b a))
  exact (P.identical_F j x t _ d ez).trans p
end AimVector

section CenterRepose
variable (P:Spine) (j:Axis) (x:P.Spectrum0 j) (t:ℕ) (p q:Cover)

theorem select_aim_product (A B:P.Apron) (r:Cover) :
    P.singleState j t x (P.aimMark A t (r+p)*P.aimMark B t (r+q))=
    P.singleState j t x (P.aimMark A t p*P.aimMark B t q) := by
  unfold aimMark
  rw [←P.chart_ids,←P.chart_ids _ q r,←map_mul,P.selected_cruise]

lemma same_truck (r:Cover) (h:∀k, k≠j→ r k =0) :
    P.truck j x (P.vtile t (r+p))=P.truck j x (P.vtile t p) :=
  P.trucking_fixed j x _ _ <| by
    intro i n
    change notch (timeMesh P.par) t ((r+p) i)=_
    rw [Pi.add_apply,h i n,zero_add]

lemma zero_wall (A:P.Apron) (s:A.s≤t) (f:P.birthF j A.s A.F)
    (h:P.grid t p j=0) :
    ∃ a:P.birthF j t (P.aimMark A t p),
      P.viewF j x t a=P.truck j x (P.vtile t p) (P.viewF j x A.s f) ∧
      P.reflectTest j (P.aimMark A t p)=P.aimMark (A.kiss P j) t p := by
  obtain ⟨u,e⟩:=P.birth_aim_full j x t p A s f (ge_of_eq h)
  refine ⟨u,?_,?_⟩
  · rw [e,h,Real.toNNReal_zero,(P.physicalEnergy j x).eZero]; rfl
  rw [P.grid_eq] at h
  have h':(p j:ℝ)=0 := (mul_eq_zero.mp h).resolve_left (P.macroTick_pos t).ne'
  replace h':p j=0 := by exact_mod_cast h'
  have : mirrorΩ j p=p := by funext i; by_cases v:i=j <;> simp [mirrorΩ,v,h']
  rw [P.oppose_aim,this]

local notation "E" => (P.physicalEnergy j x).E
local notation "U" k:max => P.truck j x (P.vtile t k)

/-- The **actual grid price**, for any birth tickets and nonnegative gap of centers (for
purposes of disjoint budgets require still to add widths to this). -/
lemma aim_center_read (A B:P.Apron) (s:A.s≤t) (v:B.s≤t)
    (a:P.birthF j A.s A.F) (b:P.birthF j B.s B.F) (h:P.grid t p j≤P.grid t q j) :
    P.singleState j t x (P.aimMark (A.kiss P j) t p*P.aimMark B t q)=
     inner ℂ ((U p) (P.viewF j x A.s a)) ((U q)
       (E (Real.toNNReal (P.grid t q j-P.grid t p j)) (P.viewF j x B.s b))) := by
  let r:Cover:=Pi.single j (-p j)
  have n : ∀k, k≠j→ r k=0 := fun k i=>Pi.single_eq_of_ne i _
  have e:P.grid t (r+p) j=0 := by simp [P.grid_eq,r]
  have f:P.grid t (r+q) j=P.grid t q j-P.grid t p j := by
    simp only [P.grid_eq,r,Pi.add_apply,Pi.single_eq_same,Int.cast_add,Int.cast_neg]
    ring
  have g:0≤P.grid t (r+q) j := by rw [f]; exact sub_nonneg.mpr h
  obtain ⟨c,hc,hu⟩:=P.zero_wall j x t (r+p) A s a e
  obtain ⟨d,hd⟩:=P.birth_aim_full j x t (r+q) B v b g
  rw [←P.select_aim_product j x t p q _ _ r,←hu,(P.released_gram j x t c d).symm, hc,hd,f,
    P.same_truck j x t p r n,P.same_truck j x t q r n]
end CenterRepose

/-! The vectors at a wall evaluate past **opposed** tests in a bra
(no nonreal smears used here), future tests in a ket. Use the absolute value
as extension off qualified support. Neither the wall nor the lengths of its two legs
need belong to the grid. -/

def toWall (c T:ℝ) : ℝ≥0 := Real.toNNReal |T-c|

lemma toWallCont : Continuous (fun z:ℝ×ℝ=> toWall z.1 z.2) := by unfold toWall; fun_prop

lemma toWall_turn (T:ℝ) : toWall 0 (-T)=toWall 0 T := by simp [toWall]

lemma toWall0 (T:ℝ) (p:0≤T) : toWall 0 T=T.toNNReal := by simp [toWall,p]

lemma toWall_add {x y c:ℝ} (p:x≤c) (q:c≤y) :
    toWall c x+toWall c y=Real.toNNReal (y-x) := by
  ext; simp only [toWall,NNReal.coe_add,Real.coe_toNNReal _ (abs_nonneg (x-c)),Real.coe_toNNReal _ (abs_nonneg (y-c)),
    Real.coe_toNNReal _ (sub_nonneg.mpr (le_trans p q))]; rw [abs_of_nonpos (sub_nonpos.mpr p),
    abs_of_nonneg (sub_nonneg.mpr q)]; ring

lemma heat_wall {j:Axis} {X:Hilbert} (S:OS.Semigroup X j) (U V:X.Op)
    (f:∀r,U.comp (S.E r)=(S.E r).comp U) (g:∀r,V.comp (S.E r)=(S.E r).comp V)
    (A B:X) {x y c:ℝ} (p:x≤c) (q:c≤y) :
    inner ℂ (U (S.E (toWall c x) A)) (V (S.E (toWall c y) B))=
    inner ℂ (U A) (V (S.E (Real.toNNReal (y-x)) B)) := by
  rw [←ContinuousLinearMap.comp_apply U, f, ContinuousLinearMap.comp_apply,
    ←ContinuousLinearMap.adjoint_inner_right, S.sym, ←toWall_add p q,
    ←ContinuousLinearMap.comp_apply _ V, ←g, S.time]
  rfl

lemma truck_heat (P:Spine) (j:Axis) (x:P.Spectrum0 j) (g:P.VMark) (t:ℝ≥0) :
    (P.truck j x g).comp ((P.physicalEnergy j x).E t)=
      ((P.physicalEnergy j x).E t).comp (P.truck j x g) :=
  Alliance.hard (P.voyageF j x) _ _ (fun i _ a=>P.colorMoveE j x i a t) _

section MacroWall
variable (P:Spine) (x:P.Spectrum0 3) (Z:Lead.Clan) (s n:ℕ)
local notation "ξ" => P.advocate 3 x 3
local notation "A" u:max => P.macroBody u s n
local notation "E" => (P.physicalEnergy 3 ξ).E

def gridWall (c:ℝ) (t:ℕ) (q:Cover) :=
  P.truck 3 ξ (P.vtile t q)
     (E (toWall c (P.grid t q 3)) (P.sourceVector x Z s n))

lemma gridWall_turn (t:ℕ) (q:Cover) :
    P.gridWall x Z s n 0 t (mirrorΩ 3 q)=P.gridWall x Z s n 0 t q := by
  unfold gridWall
  rw [P.trucking_fixed 3 ξ _ (P.vtile t q) (by intro i h; simp [vtile,mirrorΩ,h]),P.oppose_grid]
  simp only [mirrorΩ, ↓reduceIte,toWall_turn]

/-- Pair budget evaluation (with no projections), real gap paid in *the same length unit*
on both legs. No question qualification for arbitrary such pairs is inferred; `trans6`
keeps strictly disjoint widths on each side of the wall. -/
theorem gridWall_eq (Y:Lead.Clan) (c:ℝ) (t:ℕ) (p q:Cover) (ht:s≤t)
    (a:P.grid t p 3≤c) (b:c≤P.grid t q 3) :
    P.singleState 3 t x (P.aimMark ((A Z).kiss P 3) t p*P.aimMark (A Y) t q)=
      inner ℂ (P.gridWall x Z s n c t p) (P.gridWall x Y s n c t q) := by
  rw [←P.single_agrees 3 3 x]
  have g:=P.aim_center_read 3 ξ t p q (A Z) (A Y) ht ht (P.timeDifference_birth ..)
      (P.timeDifference_birth ..) (le_trans a b)
  exact g.trans ((heat_wall (P.physicalEnergy 3 ξ) _ _ (P.truck_heat 3 ξ (P.vtile _ p))
    (P.truck_heat 3 ξ (P.vtile _ q)) (P.sourceVector x Z s n) (P.sourceVector x Y s n) a b).symm)

theorem gridWall_view (t:ℕ) (p:Cover) (ht:s≤t) (a:0≤P.grid t p 3) :
    ∃ h:P.birthF 3 t (P.aimMark (A Z) t p), P.viewF 3 ξ t h = P.gridWall x Z s n 0 t p := by
  unfold gridWall; rw [toWall0 _ a]
  exact P.birth_aim_full 3 ξ t p (A Z) ht (P.timeDifference_birth ..) a
end MacroWall
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
