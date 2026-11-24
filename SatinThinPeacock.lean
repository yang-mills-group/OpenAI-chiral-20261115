import SatinThinCliche

set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Y"=> P.run
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "F" s:max=>hat P.par.R.L P.par.x s
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
abbrev uniformFoot:ℕ:= ℓ + frameRadius 3 + Lamour.Bridge.Celeste.breadth 0 noonFrame -- need cover all
abbrev echoFoot:ℕ:=P.uniformFoot+P.sidesPerTick
abbrev roomy:ℕ:= ℓ+P.echoFoot + Lamour.Bridge.Celeste.breadth 0 noonFrame + 1
local notation "k₀"=> (P.sidesPerTick:ℤ)
local notation "b#"=> P.uniformFoot
local notation "υ"=> P.echoFoot
lemma stepPos :0< (k₀):= Int.natCast_pos.mpr P.sides_pos
lemma roomy_p:0<P.roomy:= Nat.succ_pos _
abbrev persistD (p:ℤ):ℤ:= (p - (P.uniformFoot:ℤ))/k₀
abbrev persistN (p:ℤ):ℤ:= P.uniformFoot + (p-(P.uniformFoot:ℤ))%k₀
lemma lodge (x:ℤ) : (b#:ℤ) ≤ P.persistN x ∧ P.persistN x ≤ υ ∧ k₀ * P.persistD x+ P.persistN x=x:=by
 have h:=Int.emod_nonneg (x-(P.uniformFoot:ℤ)) P.stepPos.ne'; have v:= Int.emod_lt_of_pos (x- (P.uniformFoot:ℤ)) P.stepPos; unfold persistD persistN; unfold echoFoot; rw [Int.natCast_add P.uniformFoot]; exact ⟨by omega,by omega,by linarith only [Int.emod_add_mul_ediv (x-(P.uniformFoot:ℤ)) (P.sidesPerTick:ℤ)]⟩
abbrev granule (k:ℕ): Cover:= fun _=> P.persistN k
lemma sheltered (k:ℕ) : ∀ j, Between P.calibration j (-ruler P.par.block* (P.roomy:ℤ)) (ruler P.par.block*(P.roomy:ℤ)) (frameOne (P.granule k)):=by
 intro j i h; obtain ⟨l,_,t⟩:=mem_biUnion.mp h; have hp := rangeFrame i (P.granule k) t j; have hy:= P.lodge k; obtain ⟨hx,hs,_⟩:= hy
 rw [←P.sides_ruler]; let ν:= Lamour.Bridge.Celeste.breadth 0 noonFrame; let Z:=P.persistN k; have hv: (1:ℤ)≤ k₀ :=P.stepPos
 have ht: ∀ m:ℕ,(m:ℤ)≤ k₀*m:=fun m=>le_mul_of_one_le_left (by positivity) hv; specialize ht P.roomy
 refine ⟨?_,?_⟩ <;> { unfold roomy at *; change (i j).natAbs ≤ Z.natAbs+ν at hp; unfold ν Z at hp; (try rw [neg_mul]); omega } -- rw at * fails when goal no neg_mul
lemma region_granule (k:ℕ) : Tower.region 3 0 P.calibration.ℓ (frameOne (P.granule k)):=by
 intro i h; obtain ⟨_,_,t⟩:=mem_biUnion.mp h; obtain ⟨j,hj,rfl⟩:= mem_image.mp t
 have ht:(j 3).natAbs≤ frameRadius 3:= Finset.le_sup (f:=fun x:Cover=> (x 3).natAbs) hj; have hv:=(P.lodge k).1; change _ ≤ j 3+P.persistN k; unfold uniformFoot at hv; omega
abbrev originF (k:ℕ)(t:ℕ)(s:ℕ): Cover:=fun j=> if j=(3:Axis) then t * P.persistD k else P.persistD k - s -- positive pose (shave earlier using s)
abbrev focusF(k t s:ℕ): Cover:= P.granule k + P.sidesPerTick • P.originF k t s
local notation "a#"=> (3:Axis)
local notation "P?"=> P.persistD
lemma focus_axis(k t s:ℕ): P.focusF k t s a# = t * (k:ℤ) + (1-(t:ℤ))* P.persistN k:=by
 have he:=(P.lodge k).2.2; unfold focusF; rw [Pi.add_apply,Pi.smul_apply]; simp only [originF, if_true,granule,nsmul_eq_mul]; linarith only [congrArg ((t:ℤ)* ·) he]
lemma focus_canvas(k t s:ℕ)(b:Axis)(p:b ≠ 3): P.focusF k t s b = k - k₀ * s:=by
 rw [focusF,Pi.add_apply,Pi.smul_apply]; simp only [originF,if_neg p,granule,nsmul_eq_mul]; linarith only [(P.lodge k).2.2]
lemma focus_clock (f r:ℕ): P.focusF (P.megaK f r) 1 0 = P.clockPlate f r (P.baseRoot f):=by ext i; rw [P.clock_brand]; by_cases u:i=(3:Axis) <;> simp_all [P.focus_axis _ 1,P.focus_canvas _ _ _ i]
lemma ready_granule (d:ℤ) : ∀ᶠ r:ℕ in atTop,d<P.persistD (P.plannedK r):=by
 have ht:=tendsto_natCast_atTop_atTop (R:=ℤ); filter_upwards [(ht.comp (tendsto_natCast_atTop_iff.mp P.planned_grows)).eventually_gt_atTop (k₀*d+υ)] with r t; by_contra! g; have he:=mul_le_mul_of_nonneg_left g P.stepPos.le; have hp:= P.lodge (P.plannedK r); change k₀*d+υ < (P.plannedK r:ℤ) at t; omega
lemma advancing_era (x:r≤v): P.persistD (P.megaK f r) ≤ P.persistD (P.megaK f v):=by
 unfold persistD; exact Int.ediv_le_ediv P.stepPos (sub_le_sub_right (Nat.cast_le.mpr (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (L).property (Nat.sub_le_sub_right x f)))) _)
lemma daysF (s r : ℕ)(h : r ≤ s): (P.par.R.L.val:ℝ)^(s-r)* P.macroStep s=P.macroStep r:=by simpa only [timeMesh,macroStep, NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_natCast] using (congrArg ((↑) : ℝ≥0 →ℝ) (mill_finer (timeMesh P.par) r s h))
lemma offeringF (h:f≤v): (P.megaK f v:ℝ) * P.macroStep v / P.sidesPerTick= P.flightCap f:=by
 unfold megaK flightCap; rw [Nat.cast_mul,Nat.cast_pow]; exact congrArg (fun x:ℝ=> x/P.sidesPerTick) ((show (↑(L).val:ℝ)^(v-f)*_ *_=(P.baseK f:ℝ)*((P.par.R.L.val:ℝ)^(v-f)*P.macroStep v) by ring).trans (congrArg ((P.baseK f:ℝ)*·) (P.daysF v f h)))
lemma tile_effective (f r:ℕ) (h:f≤ r)(j:Axis):
    P.meshPose r (P.originF (P.megaK f r) 1 0) j = P.flightCap f - (P.persistN (P.megaK f r):ℝ) * P.macroStep r / P.sidesPerTick:=by
 let k:=P.megaK f r; rw [← P.offeringF h]; let a:=P.persistD k; change (((if _ then (↑(1:ℕ):ℤ)*a else a- (↑(0:ℕ):ℤ)):ℤ):ℝ)*P.macroStep r=(k:ℝ)*P.macroStep r/P.sidesPerTick-_; have he: (P.sidesPerTick:ℝ)* (a:ℝ) + P.persistN k=(k:ℝ):=by exact_mod_cast (P.lodge k).2.2
 rw [← sub_div]; simp only [Nat.cast_one, Nat.cast_zero,one_mul,sub_zero,ite_self]; -- may rewrite lead trivial .
 apply (eq_div_iff (show (P.sidesPerTick:ℝ)≠0 from (Nat.cast_pos.mpr P.sides_pos).ne')).mpr; linarith only [congrArg (· * P.macroStep r) he]
lemma offer_beneath (h:f ≤ r) (j:Axis): P.meshPose r (P.originF (P.megaK f r) 1 0) j ≤P.flightCap f:=by
 rw [P.tile_effective f r h]; have ht: 0≤(P.persistN (P.megaK f r):ℤ):=(Int.natCast_nonneg _).trans (P.lodge _).1; have hx:= P.macroStep_pos r; have he:=P.sides_pos; exact sub_le_self _ (by positivity)
lemma offer_approaches (f : ℕ): Tendsto (fun r:ℕ=>P.meshPose r (P.originF (P.megaK f r) 1 0)) atTop (𝓝 (fun _=>P.flightCap f)):=by
 refine tendsto_pi_nhds.mpr fun b=> ?_
 let U(r:ℕ):=(P.persistN (P.megaK f r):ℝ)*P.macroStep r/P.sidesPerTick; have ht:Tendsto U atTop (𝓝 0):=by
    have he:Tendsto (fun r:ℕ=> (υ:ℝ)*P.macroStep r/P.sidesPerTick) atTop (𝓝 0):=by simpa only [mul_zero,zero_div] using ((P.macroStep_zero.const_mul (υ:ℝ)).div_const (P.sidesPerTick:ℝ))
    refine squeeze_zero (fun r=> div_nonneg (mul_nonneg ?_ (P.macroStep_pos _|>.le)) (Nat.cast_nonneg _)) (fun r=> div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (P.macroStep_pos _|>.le)) (Nat.cast_nonneg _)) he
    exact_mod_cast (Int.natCast_nonneg _).trans (P.lodge (P.megaK f r)).1; -- tune parser
    exact_mod_cast (P.lodge (P.megaK f r)).2.1
 have hp := (tendsto_const_nhds (x:=P.flightCap f)).sub ht; rw [sub_zero] at hp; exact hp.congr' ((eventually_ge_atTop f).mono fun r q => (P.tile_effective f r q b).symm)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.ready_granule
