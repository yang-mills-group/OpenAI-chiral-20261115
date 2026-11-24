import SatinThinHighness

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
local notation "z'" => witnessZ
open Regis.Head.Etch Push.Local AnalyticBridge.VerifiedReset
local notation "Δ" t:max x:max => P.tariffQ z' t x
lemma stencil_body {n:Side}(i:Signed)(q:Quad i)(s:ℝ)(t:Site (More n))(x:Pane n)(b:ℝ)(h:0≤b)(hi:tax i=1) : kris z' (Real.sqrt b) s i t x = if pingS s (Lattice.halo 10 {t}) x then b*quadScore t x else 0:=by
 have he:= quad_move i q t 0 x; rw [hi,one_mul,affine,Signed.act_zero,zero_add] at he; unfold kris; dsimp only; rw [ping_commutes,halo_plan,affine,Signed.act_zero,zero_add]; split; swap; rfl
 rw [←he]; unfold petalWorth quadScore; rw [← mul_div_assoc,Finset.mul_sum,sum_div]; refine Finset.sum_congr rfl fun _ _=> ?_; rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt h]; unfold witnessZ; ring
lemma playback_q (X:Cover): playback (loneTrip X) j 0=loneTrip (opposeQ j X) (Signed.mirror j):=by
 unfold playback turnoverX loneTrip; congr 1
 · funext i k; by_cases h:j=k <;> simp_all [affine, Signed.mirror, Signed.act, eq_comm (a:=k) (b:=j),opposeQ,mirrorΩ]
 funext i; rw [mul_one]
lemma reflect_charge(X:Cover): P.reflectTest j (Δ s X)= Δ s (opposeQ j X):=by
 rw [tariffQ,P.visit_reflect,playback_q]; apply Subtype.ext; funext u i; let k:= opposeQ j X; let N':= (W).c u; let a:= wrap (More N') k
 change (loneTrip k _).issued z' (F s) N' i=(loneTrip k _).issued z' (F s) N' i
 unfold Trip.issued pension chalkOp Hookah.Blaze.silk; simp only [Fintype.prod_unique,Trip.tryN,loneTrip,comp_apply]
 rw [stencil_body (Signed.mirror j) (quad_mirror j) _ _ _ _ (P.f_here s).le (tax_mi _), stencil_body 1 quad_id _ _ _ _ (P.f_here s).le tax_o]
lemma moving_lamp (x:ℤ){C:Cover}: P.shifts j x (Δ s C) = Δ s (C + P.sidesPerTick • (x • step j)):=by
 let a:= 2*x; let p:= gaugeShift P.par.block a; rw [← P.halfDouble]; apply Subtype.ext; change household W (traction j p ((loneTrip C).issued z' (F s)))= household W ((loneTrip _).issued z' (F s)); unfold traction
 have he (c:ℤ)(V:Trip Unit): fluent j c (V.issued z' (F s)) = (playback V j c).issued z' (F s):=funext fun i=> P.bulb_reflect j z' V s c i
 rw [he,he,play_hopping]; congr 3; unfold hopping turnoverX loneTrip; congr 1; · funext i; simp only [affine,Signed.act_one]; congr 1; unfold p a; funext t; by_cases h:t=j <;> simp [h,gaugeShift, sidesPerTick]; ring
lemma cruise_position (X o:Cover)(L₀ : List Axis)(h:L₀.Nodup) : P.cruise L₀ o (Δ s X)= Δ s (fun i=> if i∈L₀ then X i+(P.sidesPerTick:ℤ)*o i else X i):=by
 induction L₀ with
 | nil=>simp_rw [List.not_mem_nil, ite_false]; rfl
 | cons i L₀ ih=>
    rw [P.cruise_step,AlgHom.comp_apply,ih (List.Nodup.tail h), P.moving_lamp]; apply congrArg (P.tariffQ z' s); funext j; by_cases c:j=i <;> simp_all [List.nodup_cons]
lemma charged_sum (X o:Cover) : P.chartAll o (Δ s X)=Δ s (X+P.sidesPerTick • o):=by
 rw [chartAll,P.cruise_position X o _ Vacancy.ordinate_one]; congr; simp_rw [if_pos (Vacancy.ordinates _)]; rfl -- tune mul
lemma reflect_visit (x:Cover): P.reflectTest j (P.visitOne s x)=P.visitOne s (opposeQ j x):=by
 unfold visitOne; rw [P.scale_mirror,Complex.star_def,Complex.conj_ofReal]; exact congrArg _ (P.reflect_charge j x) -- tune
lemma charged_visit (x y:Cover): P.chartAll x (P.visitOne s y)= P.visitOne s (y+P.sidesPerTick • x):=by
 unfold visitOne; rw [map_smul]; exact congrArg _ (P.charged_sum y x)
lemma charge_colors (x:Cover): P.tariffQ z' s x∈ enclave P.calibration:= (enclave_spec W).mpr fun m=> Trip.issued_invar z' (loneTrip x) (F s) ((W).c m)
lemma clock_colors (x:Cover): P.visitOne s x ∈ enclave P.calibration:= Subalgebra.smul_mem (enclave W) (P.charge_colors x) _ -- binder s ambiguous
lemma tariff_scalar (x y:Cover): (P.tariffM z' s x y)=Δ s y *Δ s x:=by rw [tariffM,P.visit_unit_pair]; apply Subtype.ext; funext n i; let N0:= (W).c n; change (loneTrip x).issued z' (F s) N0 i*(loneTrip y).issued z' (F s) N0 i= _*(loneTrip x).issued z' (F s) N0 i; unfold Trip.issued pension chalkOp; rw [smul_mul_assoc,one_mul]; change _=_•(1:FC _) *_; rw [smul_mul_assoc,one_mul,smul_smul,smul_smul,mul_comm]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.charged_visit
