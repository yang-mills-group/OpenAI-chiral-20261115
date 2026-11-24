import YM.SU5.SatinWard.Resolution.Muff
import YM.SU5.SatinWard.Resolution.Cypress
import YM.SU5.SatinWard.Resolution.Domic
import YM.SU5.SatinWard.Resolution.Waive
import YM.SU5.SatinWard.Resolution.Belfry
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
namespace Internal -- Proof shape Aries
open Preparation.Tabletop CasaF
local notation "Y"=> P.run
local notation "T"=> P.calibration
local notation "L"=> P.par.R.L
local notation "ζ"=>P.sidesPerTick
local notation "t" i:max=> P.macroStep i
noncomputable abbrev deltaWing (P:Spine)(d:ℕ):ℕ:= d+P.sidesPerTick+P.calibration.ℓ+1
variable (M:P.par.R.L.val%16=1){s v j:ℕ} (p x:Cover){a:Cover} (qa:ResidualPermit a){F:Cover→Family P.calibration}{w:ℕ} (k:Domicile w F)(u:Axis)
local notation "ξ" r:max => P.clockPlate s r p
local notation "H!" v:max=> rentWidth P j v
local notation "hA"=> P.calibration.ℓ
local notation "ψ" v:max=> deltaWing P (rentWidth P j v)
noncomputable abbrev tauprint (M:P.par.R.L.val%16=1)(qa:ResidualPermit a): Cover:= (nodeHome P M a qa).choose
noncomputable abbrev chapterFoot (p:Cover) : P.Test:= P.art (F p) (aux_test (k.valid p))
noncomputable abbrev clockF (u:Axis)(d:ℤ):Cover:= (gaugeT P.calibration d) • step u
lemma gaugeM(d:ℤ): gaugeT P.calibration d=P.jump128*d:=by rw [gaugeT]; unfold Heat.gaugeShift; change 4*(P.par.block.val:ℤ)*_= _; unfold Spine.jump128; push_cast; ring
lemma Gauge_time (d:ℤ)(v:Axis): nodeC (p+ clockF P u d) v=nodeC p v+(ruler P.par.block*d) * (step u:Cover) v:=by change (2:ℕ) • (p v+(gaugeT P.calibration d) • (step u:Cover) v)+1=(2:ℕ) • p v+1+ _; rw [gaugeM,nsmul_eq_mul,nsmul_eq_mul,zsmul_eq_mul]; unfold ruler jump128; push_cast; ring
lemma relation_core (x:Cover):nodeC (p+P.jump128 • x)= nodeC p+ ζ • x:=by
 funext i; change (2:ℕ) • (p i+P.jump128 • x i)+1=(2:ℕ) • p i+1+P.sidesPerTick • x i; simp only [nsmul_eq_mul,sidesTick_eq,jump128]; push_cast; ring
lemma chapter_step (d:ℤ): P.shifts u d (chapterFoot P k p)=chapterFoot P k (p+clockF P u d):= Subtype.ext (k.travel ..)
lemma calendar_moves (x:Cover): P.chartAll x (chapterFoot P k p)= chapterFoot P k (p+P.jump128 • x):=by
 let H(Q:List Axis):= p+ P.jump128 • fun i:Axis=> if i∈Q then x i else (0:ℤ); have h(Q:List Axis)(u:Q.Nodup):P.cruise Q x (chapterFoot P k p)=chapterFoot P k (H Q):=by
    induction Q with
    | nil=> change chapterFoot P k p= _; rw [show H []=p from by unfold H; rw [show (fun i:Axis=> if i∈([]:List Axis) then x i else (0:ℤ))=(0:Cover) from funext fun _=>by simp, smul_zero,add_zero]]; -- hmm `P.cruise` change.
    | cons j Q ih=>
       rw [P.cruise_step,AlgHom.comp_apply,ih (List.Nodup.of_cons u),chapter_step]; apply congrArg (chapterFoot P k); funext i; unfold H clockF; rw [SlabMark.moves]; by_cases w:i=j; · subst i; simp [List.nodup_cons.mp u|>.1, gaugeM,nsmul_eq_mul]
       simp [w]
 unfold chartAll; rw [h _ ordinate_one]; unfold H; simp only [ordinates,if_true]
local notation "homeQ"=>pavilion (homeTag P a) w
include qa in
lemma home_bounds (p₀:Cover)(x':nodeC p₀=homeTag P a): Between T u (-ruler P.par.block*(deltaWing P w:ℤ)) (ruler P.par.block*(deltaWing P w:ℤ)) (pavilion (nodeC p₀) w):= by
 rw [x']; intro z₁ h; let q:= (pav_v (homeTag P a) z₁ w).1 h u; have hp:= abs_le.mp (homeCost P a qa u); have h:0<ruler P.par.block:= ruler_gene _
 let x:= w+P.sidesPerTick+P.calibration.ℓ+1
 have v: (↑x:ℤ) ≤ ruler P.par.block*(x:ℕ):= le_mul_of_one_le_left (by positivity) (by omega); unfold deltaWing; unfold x at v; rw [neg_mul]; omega
-- keep width for thickness.T budget.
lemma wing_pos (w:ℕ): 0<deltaWing P w:=by unfold deltaWing; positivity
lemma wing_price (j:ℕ) : ∀ᶠ s in atTop,16*deltaWing P (rentWidth P j s) ≤ moonSpan P s:=by
 let f:=12+2*j+petalD+P.sidesPerTick+P.calibration.ℓ+1; filter_upwards [(Yoke.waist P.run 0).eventually (eventually_ge_atTop f)] with s e; let h:= P.thresholdF s; change f ≤ h at e; unfold rentWidth deltaWing; have ht:4 ≤ h:=by unfold f at e; omega
 have hv:16*(h+f)≤10*(h+1)^4:=by
    have hu:h ≤(h+1)^3:= Nat.le_trans (by omega : h≤h+1) (le_self_pow₀ (by omega) (by decide)); rw [show (h+1)^4=(h+1)^3*(h+1) from pow_succ _ 3]; apply Nat.le_trans _ (Nat.mul_le_mul_left 10 (Nat.mul_le_mul (hu) (Nat.le_of_lt (by omega:4<h+1)))) -- tune 3= 30; require 4
    omega
 unfold f h at hv; change _ ≤10*(P.thresholdF s+1)^4; omega
variable (pL:64≤P.par.R.L.val)
include pL in
lemma wing_room (j:ℕ) : ∀ᶠ s in atTop,∀ v,s≤v→∀ w, w≤ rentWidth P j v→ (16*(deltaWing P w:ℝ))*t v ≤ moonClock P s:=by
 filter_upwards [eventually_forall_ge_atTop.mpr (wing_price P j),clocksPast P pL] with s e hz v h w u
 let W:= moonClock P s; let d:=deltaWing P w; have ht:16*d≤ moonSpan P v:= (Nat.mul_le_mul_left 16 (by unfold d deltaWing; omega)).trans (e v h); have hP:moonClock P v≤W:=(hz s le_rfl v h).trans (mul_le_of_le_one_left (clockP ..).le (pow_le_one₀ (by norm_num) (by norm_num))); exact (mul_le_mul_of_nonneg_right (by exact_mod_cast ht:16*(d:ℝ)≤ (moonSpan P v:ℝ)) (P.macroStep_pos _).le).trans hP
-- record prices.ALL extended temporal lags.
noncomputable def cloakF (v:ℕ):P.Apron:= let A:= tauprint P M qa; ⟨v,(fun _=>deltaWing P w),fun _=> wing_pos P _,chapterFoot P k A,pavilion (nodeC A) w,k.valid _,(enclave_spec ..).2 (k.neutral _),fun i=> home_bounds P qa i A ((nodeHome P M a qa).choose_spec)⟩ -- order qa position? check
lemma real_cloak (v:ℕ) : (cloakF P M qa k v).realWidth P u=(↑(deltaWing P w):ℝ)*P.macroStep v:=by change P.tock v (deltaWing P w)=_; rw [P.tock_price]; norm_cast
lemma cloak_pocket (x: Cover)(t':nodeC x=P.clockPlate s v p)(u:Cover)(r:P.clockPlate s v p=homeTag P a+P.sidesPerTick • u): P.chartAll u (cloakF P M qa k v).F=chapterFoot P k x:=by
 let P':=tauprint P M qa; change P.chartAll u (chapterFoot P k P')= _; rw [calendar_moves]; apply congrArg (chapterFoot P k); apply Satin.nodeC_inj; rw [relation_core,show nodeC P'=homeTag P a from (nodeHome P M a qa).choose_spec,t',r]
#print axioms calendar_moves
#print axioms wing_room
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
