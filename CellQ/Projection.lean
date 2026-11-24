import Crape.Oblivion
import Crape.Arsenal
import CellQ.Collate
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
namespace PledgeT
open Calico
open Py.Rate.Pitching.Focus
variable (P:Spine) {U:P.Roster}(M:Morn P.par.K)
-- Qualifying per reference height. Markov on price.Basic threshold ~2^s sqrt(Wx). all suffice vs boost.S
local notation "K"=>P.calibration
open YM.Gleam.Luster YM.Gleam.Luster.Almanac Grade LocalLimit Papal CF.Pannier.Chancel Checkers Flint
local notation "pio"=>P.par.R.L
local notation "Xb"=>Vale.hat pio P.par.x
include P
lemma turn_p (j:ℕ):1 ≤ Xb j:= P.run.oneP.trans (Vale.crown ..)
lemma temporal : Grade (-claimV) parcelF:=Grade.pitch _
lemma range_grade : Grade 0 (fun x=> (2*((P.calibration.ℓ+ (22+2*((((YM.Pressure.radiusB x):ℝ)^3)+(YM.Pressure.radiusB x:ℝ))))+16*(P.calibration.B.val:ℝ)+(22+2*((((YM.Pressure.radiusB x):ℝ)^3)+(YM.Pressure.radiusB x:ℝ))))+(addgap P.calibration:ℝ))) :=by
 have ht:= ((Grade.radiusBill.pwr 3).grow (b:=0) (by norm_num)).plus Grade.radiusBill
 let h:= (Grade.block (22:ℝ)).plus (ht.scaleB 2)
 exact ((((((Grade.block _).plus h).plus (Grade.block _)).plus h).scaleB 2).plus (Grade.block _))
lemma earnings_wafer (a:ℝ) :∀ᶠ s:ℕ in atTop, shardRa P M a s (Calico.amount P s) (reachQ P s) ≤ (payday P s*Real.exp (2*(|a|+|M.Mult|)+1))^2*Real.exp 1:=by
 let k:=Grade.scaleB (4:ℝ) (range_grade P)
 have he:=Grade.mul (temporal (P:=P)|>.scaleB 7) ((k.pwr 4).grow (b:=0) (by norm_num))
 filter_upwards [(Py.Rate.stage_slope P.par.V P.par.x).eventually ((he.roots (by norm_num [claimV,tauA,ratioV])).eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num)))] with s h
 unfold shardRa; gcongr
 unfold reachQ minB Calico.amount; rw [(P.run.meter.boot s).2.1]; push_cast
 refine le_trans (le_of_eq (?_)) h -- ℓ+K order; closure. ring
 ring
lemma shard_retains (a:ℝ):∀ᶠ j:ℕ in atTop,∀ d:ℕ,shardRa P M a j (Calico.amount P j) d≤ wafer P M j (Calico.amount P j) d:=by
 -- normalized receipt even at all d, enough height. buy 7 parcelF≤1/2 and H coeff by amount.
 let Z:=2*(|a|+|M.Mult|)+1
 obtain ⟨c,hc⟩:=exists_nat_ge Z
 set b:=c+100
 let Y:=P.run
 filter_upwards [(Py.Rate.stage_slope P.par.V P.par.x).eventually (((temporal (P:=P)).roots (by norm_num [claimV,ratioV,tauA])).eventually (ge_mem_nhds (show (0:ℝ)<1/14 by norm_num))), (Py.Rate.stage_slope P.par.V P.par.x).eventually (YM.Work.E08.eventual_radiusB b), Papal.clocks_roof Y M.Mult a] with j ht hx hγ d
 -- obtain eligible hypo from clocks_roof with choose i,k.L if not need.Scalar. payday ≤1 via Scales yg. easier eventual. actually clocks_roof require k large.Protocol exists k.Y.uv Tendsto. choose. or Scales minute.
 let x:=Xb j; have he:1≤x:=turn_p P _
 have hv:1≤SectorNext.Remainder.Scales.y SU.group pio x:=by
    unfold YM.SectorNext.Remainder.Scales.y YM.Pressure.betaF; apply he.trans (le_add_of_nonneg_right _); exact mul_nonneg (Gauge.slopeConstant_pos Thera.yet_one).le (Real.log_nonneg (Nat.one_le_cast.mpr P.par.R.L.property))
 let v:=payday P j
 have hf:v ≤1:=by have ht:=SectorNext.Remainder.Scales.yg2 SU.group pio (zero_lt_one.trans_le hv); unfold v payday; change (YM.SectorNext.Remainder.Scales.g _ _ _)^2 ≤ 1; nlinarith only [ht,hv,mul_le_mul_of_nonneg_right hv (sq_nonneg (YM.SectorNext.Remainder.Scales.g SU.group pio x))]
 have hm:0≤v:=sq_nonneg _
 let V:=Calico.amount P j
 have hp: b ≤ V:=by unfold V Calico.amount; rw [(P.run.meter.boot j).2.1]; omega
 let L:ℝ:=4*((2*(d+V):ℕ)+(addgap P.calibration):ℝ); have hl:(c:ℝ)+1≤ L:=by
    unfold L; push_cast; have he: (c:ℝ)+100≤V:=by exact_mod_cast (by exact hp : c+100≤V)
    have hx (k:ℕ):0≤(k:ℝ):=Nat.cast_nonneg _; linarith only [he,hx d,hx (addgap P.calibration)]
 let Y':=Decaf.cupcost P.par Y.τ M.Mult Y.meter.a j
 have hy: 0≤ Y':= add_nonneg (abs_nonneg _) (abs_nonneg _)
 change (v*Real.exp Z)^2 * Real.exp ((7*parcelF x)*L^4)≤ Real.exp ((Y'+1)*L^4)
 apply (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg hm (Real.exp_pos _).le) (mul_le_of_le_one_left (Real.exp_pos _).le hf) _) (Real.exp_pos _).le).trans
 rw [←Real.exp_nat_mul,← Real.exp_add]; apply Real.exp_monotone
 have hp':100 ≤ (V:ℝ):=by exact_mod_cast (by change c+100≤V at hp; omega : 100 ≤ V)
 have hL :4≤L:=by unfold L; push_cast; linarith only [hp',Nat.cast_nonneg (α:=ℝ) d,Nat.cast_nonneg (α:=ℝ) (addgap P.calibration)]
 have hv:4*(c:ℝ)≤L^4:=by nlinarith only [show (c:ℝ)≤ L by linarith only [hl],hL,pow_le_pow_right₀ (show 1 ≤ L by linarith only [hL]) (show 2≤4 by norm_num),mul_le_mul_of_nonneg_left hL (show 0≤L by linarith only [hL])]
 have h0:0≤L^4:=by positivity
 have hh:7*parcelF x≤1/2:=by linarith only [ht]
 push_cast; nlinarith only [hv,hc,mul_le_mul_of_nonneg_right hh h0, mul_nonneg hy h0]
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
