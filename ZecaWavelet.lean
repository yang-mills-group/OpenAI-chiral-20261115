import ZecaNepenthe
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)

local notation "z'"=> Yoke.witnessZ
local notation "κ"=>P.sidesPerTick
local notation "κz"=> (P.sidesPerTick:ℤ)


lemma point_stable (n:ℕ):P.pointEra (n+1) ≤ P.pointEra n+1:=by
 have H₁:P.diameterEra n ≤ P.diameterEra (n+1):=by
   rw [diameter_view,diameter_view]
   have u:Real.exp 1 ≤ (F n):= P.large.trans (Vale.crown ..)
   have h:1≤Real.log (F n):= by rw [←Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) u
   exact pow_le_pow_left₀ (Real.log_nonneg h) (Real.log_le_log (zero_lt_one.trans_le h)
     (Real.log_le_log (P.f_here _) (P.base_height (Nat.le_succ _)))) _
 have e:P.decades n ≤ P.decades (n+1):= Nat.ceil_mono (by gcongr)
 unfold pointEra; omega


open CF.Roots (cape_B)

lemma wave_slope (n:ℕ): P.baseK n ≤ P.baseK (n+1) := by
 have u:Real.exp 1 ≤ (F n):= P.large.trans (Vale.crown ..)
 have h:1≤Real.log (F n):= by rw [←Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) u
 have e(r:ℕ): P.thresholdF r= radiusB (F r):=(P.run.meter.boot r).2.1
 have q:P.thresholdF n ≤ P.thresholdF (n+1):=by
   rw [e n,e (n+1)]
   exact Nat.ceil_mono (pow_le_pow_left₀ (zero_le_one.trans h)
      (Real.log_le_log (P.f_here _) (P.base_height (Nat.le_succ _))) _ )
 unfold baseK axleQ repeatD rural cape_B
 gcongr

lemma crest (f:ℕ):∃ r,P.pointEra r=f:=by
 have h:∃ r,f≤P.pointEra r:=(P.future_payment.eventually_ge_atTop f).exists
 let r := Nat.find h
 refine ⟨r,(?_ : P.pointEra r ≤ f).antisymm (Nat.find_spec h)⟩
 match g:r with
 | 0=>simp [pointEra]
 | r'+1=>
   have a:P.pointEra r' < f:=lt_of_not_ge (Nat.find_min h (show r' < r by omega))
   exact (P.point_stable _).trans a

/-- Land near each dyadic stage. -/
lemma seawall (T : ℝ)(ht : 0<T):
 ∃ (M₀:ℝ), 0<M₀ ∧ ∃ u:ℕ→ℕ,Tendsto u atTop atTop ∧
    ∀ᶠ n in atTop, P.jetS (u n)*T ≤ ((1/2:ℝ)^n) ∧
       (1/2:ℝ)^n ≤ P.jetS (u n)*M₀ := by
  let e:ℝ:=1/2; let d:ℕ→ℝ:=fun f=>P.macroStep f*P.baseK f
  have dh(f):0<d f:=mul_pos (P.macroStep_pos _) (Nat.cast_pos.mpr (P.payment_pos _))
  choose y hy using P.crest
  have dy(f):d f=P.jetS (y f):=by rw [jetS_base,hy]
  have yp:Tendsto y atTop atTop:=
    tendsto_atTop_mono (f:= id) (fun f=>show f ≤ y f from (hy f).symm.le.trans (Nat.sub_le ..)) tendsto_id
       -- replace
  have g:Tendsto (fun f=>d f*T) atTop (𝓝 0):=by
    simp_rw [dy]
    simpa only [Function.comp_def,zero_mul] using (P.jetS_go.comp yp).mul_const T
  have px(n):0<e^n:= pow_pos one_half_pos _
  have dt(n):∃ f,d f*T ≤ e^n:= (g.eventually (ge_mem_nhds (px n))).exists
  let b n:= Nat.find (dt n)
  have b0(n):d (b n)*T ≤ e^n:= Nat.find_spec (dt n)
  have e0:Tendsto (fun n:ℕ=>e^n) atTop (𝓝 0):=
    tendsto_pow_atTop_nhds_zero_of_lt_one one_half_pos.le (by norm_num)
  have bz:Tendsto b atTop atTop:=by
    refine Filter.tendsto_atTop.mpr fun k=>?_
    induction k with
    | zero=>exact Eventually.of_forall (fun _=>Nat.zero_le _)
    | succ k ih=>
      filter_upwards [ih, e0.eventually (gt_mem_nhds (mul_pos (dh k) ht))] with n nk l
      have t:b n≠k:=fun q=> (not_le.mpr l) (q ▸ b0 n)
      exact Nat.succ_le_of_lt (lt_of_le_of_ne nk t.symm)
  have lp:0<(P.par.R.L.val:ℝ):= Nat.cast_pos.mpr (P.par.R.L.property)
  refine ⟨T * P.par.R.L.val,mul_pos ht lp,y ∘ b,yp.comp bz,?_⟩
  filter_upwards [bz.eventually_gt_atTop 0] with n v
  change P.jetS (y (b n))*T ≤ e^n ∧ e^n ≤ P.jetS (y (b n))*_
  rw [←dy]
  refine ⟨b0 n,?_⟩
  obtain ⟨l,k⟩:= Nat.exists_eq_succ_of_ne_zero v.ne'
  have a:l < Nat.find (dt n):= show l < b n from by omega
  refine le_trans (le_of_lt (lt_of_not_ge (Nat.find_min (dt n) a))) ?_
  rw [k]
  have w:=P.daysF _ _ (Nat.le_succ l)
  rw [show l.succ-l=1 by omega,pow_one] at w
  unfold d
  rw [←w]
  apply le_trans _ (le_of_eq (show (↑(L).val :ℝ) * P.macroStep (l+1)

   *↑(P.baseK (l+1)) *T=_ from by ring))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
     (by exact_mod_cast P.wave_slope l) (mul_pos lp (P.macroStep_pos _)).le) ht.le
#print axioms seawall
