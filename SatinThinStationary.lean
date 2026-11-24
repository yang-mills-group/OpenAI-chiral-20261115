import SatinThinSouvenir
import YM.SU5.Six.PointSpot
import SatinThinKernel

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
local notation "Λ"=> P.par
local notation "L"=> P.par.R.L
local notation "H"=>P.large
local notation "N" s:max i:max => Journey.side P.run i s
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "E" r:max=> P.singleState 3 r x
local notation "Ω"=> P.colorZero 3 ξ
abbrev dewy (P:Spine)(F:P.Test)(v:ℂ):P.Test:= F - v • (1:P.Test)
abbrev centeredQ (r:ℕ)(X:Cover): P.Test:= P.dewy (P.visitOne r X) ((E r) (P.visitOne r X))
lemma footprint_plot (t:ℕ)(S:Cover): P.centeredQ x t S∈ bay W (frameOne S) true:=by
 let B:=bay W (frameOne S) true; exact B.sub_mem ((Tapestry.locates ..).mpr P.basesT) (B.smul_mem B.one_mem _) -- tune arguments lambda
lemma center_colors (t:ℕ)(S:Cover): P.centeredQ x t S ∈ enclave W:=by let B:=enclave W; exact B.sub_mem (P.clock_colors _) (B.smul_mem B.one_mem _)
def basePlay (f r:ℕ):P.Apron:=⟨r,fun _=>P.roomy,fun _=>P.roomy_p,P.centeredQ x r (P.granule (P.megaK f r)),frameOne (P.granule (P.megaK f r)),P.footprint_plot x r _,P.center_colors x r _,P.sheltered _⟩
local notation "ΛC"=> P.granule
local notation "K" f:max r:max=> P.megaK f r
local notation "R!" f:max r:max=> P.basePlay x f r
lemma base_birth (f r:ℕ): P.birthF 3 r (R! f r).F:= P.criteria 3 r (footprint_plot ..) (P.region_granule _) (P.center_colors x _ _)
lemma origin_act(f r:ℕ): (E r) (R! f r).F=0:=by
 have he:(E r) 1=1:=by rw [P.single_state,P.reading_unit,map_one]
 change (E r) (_- ((E r) (P.visitOne r _)) • 1)=_; rw [map_sub,map_smul _ _ (1:P.Test),he, smul_eq_mul,mul_one,sub_self]
lemma chart_center (X o:Cover) : P.chartAll o (P.centeredQ x s X) = P.centeredQ x s (X+P.sidesPerTick • o):=by
 have ht:=P.chart_price 3 x s (P.visitOne s X) o; rw [P.charged_visit] at ht; unfold centeredQ dewy; rw [map_sub,P.charged_visit, map_smul _ _ (1:P.Test),map_one,ht]
lemma reflect_center (X:Cover): P.reflectTest 3 (P.centeredQ x s X)= P.centeredQ x s (opposeQ 3 X):= by
 have hv:=P.opposed_single x s (P.visitOne s X); rw [P.reflect_visit] at hv; unfold centeredQ dewy; rw [map_sub,P.reflect_visit,P.scale_mirror (1:P.Test), show P.reflectTest 3 1=1 from aureoleUnit ..,hv] -- not AlgHom?
lemma issuing_here (X:P.Apron) (o:Cover): P.issuing X.s X o=P.chartAll o X.F:=by rw [issuing, Apron.full,Nat.sub_self]; rfl
local notation "B"=>P.basePlay x f r
abbrev runP (f r i s:ℕ):= P.originF (P.megaK f r) i s
local notation "q!" i:max s:max=> P.runP f r i s
local notation "W!" i:max s:max=> P.meshPose r (q! i s)
lemma straight_price (i s:ℕ): P.issuing r B (q! i s)= P.centeredQ x r (P.focusF (K f r) i s):= (P.issuing_here ..).trans (P.chart_center ..)
lemma rewind_price(i s:ℕ): P.issuing r ((B).kiss P 3) (opposeQ 3 (q! i s))= P.centeredQ x r (P.recoilF (K f r) i s):=by rw [P.issue_reflect, P.straight_price, P.reflect_center] -- local notation (B).kiss doesn't parse macro
private lemma dewy_form (s:ℕ)(Z Y:P.Test): (E s) (P.dewy Z ((E s) Z)*P.dewy Y ((E s) Y))=(E s) (Z*Y)-(E s) Z* (E s) Y:=by
 have ht:(E s) 1=1:=by rw [P.single_state,P.reading_unit,map_one]
 let v:=E s; unfold dewy; rw [_root_.sub_mul,mul_sub,mul_smul_comm,smul_mul_assoc,one_mul,mul_one,map_sub,map_sub,map_smul,map_smul, map_sub,map_smul,ht]; -- tune
 simp; ring
lemma lens_price(s:ℕ)(Y Z:Cover) : (E s) (P.centeredQ x s Y * P.centeredQ x s Z)= (P.tallWorth s:ℂ)^2 * P.pulseQ 3 z' s Z Y x:=by
 let r:ℂ:= P.tallWorth s; let z:=Δ s Z; let y:=Δ s Y; unfold centeredQ pulseQ; rw [P.dewy_form,P.tariff_scalar]; change (E s) ((r • y)*(r • z))-_=_; rw [smul_mul_assoc,mul_smul_comm]; change _ - (E s) (r • y) * (E s) (r • z)=_; rw [map_smul,map_smul,map_smul,map_smul]; simp only [smul_eq_mul]; change _=r^2*((E s) (y*z)-(E s) z* (E s) y); ring
-- clearance
abbrev reached (f r:ℕ):Prop:= P.roomy < P.persistD (P.megaK f r)
def rentTick (f r:ℕ)(v:ℕ): ℝ:= P.meshPose r (P.runP f r v 0) 3
private lemma rent_pair_clock (x z:ℤ) (n:ℕ) : (if (3:Axis)=(3:Axis) then (n:ℤ)*x else z)=(n:ℤ)*x:= if_pos rfl
lemma run_here (f r v a:ℕ): P.runP f r v a (3:Axis)=(v:ℤ) * P.persistD (P.megaK f r):=rent_pair_clock ..
lemma pose_w (r:ℕ)(p:Cover)(j:Axis): P.meshPose r p j = (p j:ℝ)*P.macroStep r:=rfl
lemma rent_only (f r v a:ℕ): P.meshPose r (P.runP f r v a) (3:Axis) = P.rentTick f r v:=by
 unfold rentTick; rw [P.pose_w,P.pose_w,P.run_here,P.run_here]
lemma play_width (f r:ℕ)(j:Axis): (R! f r).realWidth P j = P.roomy * P.macroStep r:=by unfold Apron.realWidth; change (↑((P.roomy:ℤ)):ℝ)* _=_; rw [Int.cast_natCast]; rfl
variable (u:P.reached f r) {m:ℕ}(h:0 < i)(P':0<v)
include u -- local axis confusion q n numbers
lemma bought_as (i:ℕ)(p:0 < i) (b:Axis): (B).realWidth P b < P.rentTick f r i:=by
 rw [P.play_width]; change (P.roomy:ℝ)*P.macroStep r < (↑((q! i 0) (3:Axis)):ℝ)*P.macroStep r; have ht: (P.roomy:ℤ)< (q! i 0) 3:= by
    rw [P.run_here]; refine lt_of_lt_of_le u (le_mul_of_one_le_left ((Int.natCast_nonneg _).trans u.le) (by omega))
 exact mul_lt_mul_of_pos_right ((show (P.roomy:ℝ) = (↑(↑P.roomy:ℤ):ℝ) from Int.cast_natCast P.roomy|>.symm).trans_lt (Int.cast_lt (R:=ℝ)|>.2 ht)) (P.macroStep_pos r)
lemma reach_onward (h:r≤v): P.reached f v:=lt_of_lt_of_le u (P.advancing_era h) -- hp binder p implicit
local notation "p!" i:max s:max => opposeR 3 (W! i s)
include P' h
lemma turn_point (b:ℕ) : P.Turnstile 3 (usher ((B).kiss P 3) B) [false,true] (usher (p! i b) (W! v 0)) := by
 refine List.pairwise_pair.mpr (show (p! i b) 3+(B).realWidth P 3<(W! v 0) 3-((B).realWidth P 3) from ?_); rw [show (p! i b) 3 = - ((W! i b) (3:Axis)) from if_pos rfl, P.rent_only,P.rent_only]; linarith only [P.bought_as x u i h 3,P.bought_as x u v P' 3]
omit h P' u in
def charmF:= P.roomy + P.roomy + 1
lemma turn_all : P.Plenum (usher ((B).kiss P 3) B) [false,true] (usher (p! i P.charmF) (W! v 0)):=by
 refine ⟨fun d:Axis=> ⟨_,List.Perm.refl _,?_⟩⟩; by_cases k:d=3; · subst d; exact P.turn_point x u h P' _ -- order tune
 let a:= P.roomy; let g:= P.megaK f r; let w:= P.macroStep r; have ht:0<w:= P.macroStep_pos _; let b:= (P).charmF; apply List.pairwise_pair.mpr; change (opposeR 3 (W! i b) d)+(B).realWidth P d < (W! v 0) d-(B).realWidth P d
 rw [P.play_width]; unfold opposeR mirrorΩ; rw [if_neg k]
 let z (a v:ℕ):= P.runP f r a v; have he(v w:ℕ): z v w d=P.persistD g-(w:ℤ):= if_neg k
 change (↑((z i b d):ℤ):ℝ)*w+(a:ℝ)*w < (↑((z v 0 d):ℤ):ℝ)*w- (a:ℝ)*w
 rw [he,he,Int.cast_sub,Int.cast_sub]; simp only [Int.cast_natCast,Nat.cast_zero,Int.cast_zero]; rw [show (↑b:ℝ)= (a:ℝ)+a+1 from (by unfold b charmF; rw [Nat.cast_add_one,Nat.cast_add])]; linarith only [ht]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.turn_all
