import SatinThinRampart

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
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}{d:ℕ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
-- One common regulator convergence workflow. P HERE chosen Station. 
open Worth Pays CF.BProof
-- revenue for remarkable width purchases. Pay along this very hat. Value travel at much LARGER than powers logs, using small exhaustion. 
variable (d:ℝ)(g:0<d)
#print Plans
abbrev axleQ (D:ℕ):= repeatD P.par P.width D + reserve P.par P.width + frameRadius j
private lemma costRura: Worth.Pays 0 0 6 (fun x:ℝ=> (rural (radiusB x):ℝ)):=by
 unfold rural Roots.cape_B; push_cast; have ht: Worth.Pays 0 0 6 (fun x=> (↑(radiusB x):ℝ)^3):=by have h:=pot rising 3; norm_num at h; exact h -- 2*3 simp
 have hz: Worth.Pays 0 0 6 (fun x=>(↑(radiusB x):ℝ)):= Worth.Pays.merit rising (by norm_num [Worth.Earlier]); exact plus (plus (plus ht ht) hz) hz
lemma width_ledger: Worth.Pays 0 0 6 (fun x:ℝ=> (P.axleQ j (radiusB x):ℝ)):=by
 have h:=costRura; push_cast at h; unfold axleQ repeatD; push_cast; have hT: ∀ A:ℝ,Worth.Pays 0 0 6 (fun x=> A):=fun q=> Worth.Pays.merit (Pays.constant q) (by norm_num [Worth.Earlier]); exact plus (plus (plus (hT _) h) (hT _)) (hT _)
include g
lemma earns_widthT (b:ℝ): ∀ᶠ s:ℕ in atTop,b*(P.axleQ j (P.thresholdF s)) ≤ trailℓ d (F s):=by
 filter_upwards [(turnover Λ).eventually (leap (p:=d) (q:=0) (Worth.Pays.scale b (P.width_ledger j)) (Or.inr (Or.inl ⟨rfl,g⟩)))] with s h
 rw [show P.thresholdF s=radiusB (F s) from (P.run.meter.boot s).2.1]; exact h
lemma weather_bill : ∀ᶠ s:ℕ in atTop,P.repeatBill (scout P.par d s) s:=by
 let f' x:= plusAgain Q (repeatD Λ P.width (radiusB x)); let u(x:ℝ):= Nat.ceil (trailℓ d x); let q(x:ℝ):= (u x+ f' x:ℕ)
 have ht: Worth.Pays 0 0 6 (fun x=> (f' x:ℝ)):=by
    have h:=costRura; push_cast at h; unfold f' plusAgain stepAgain repeatD; push_cast; have hp(x:ℝ):= Worth.Pays.merit (Pays.constant x) (w:=0) (p:=0) (q:=6) (by norm_num [Worth.Earlier]); exact Pays.scale _ (plus (plus (hp _) h) (hp _))
 have h1: Worth.Pays 0 d 0 (fun x=> (q x:ℝ)):=by unfold q; push_cast; exact plus (helmBound d g) (Worth.Pays.merit ht (Or.inr (Or.inl ⟨rfl,g⟩)))
 have h0:∀ᶠ x:ℝ in atTop, 14* Worth.meterC x*(4*(q x:ℝ))^4≤ coin x 0 0 0:= leap (Worth.Pays.times (Pays.scale 14 (Pays.whole ..)) (pot (Pays.scale 4 h1) 4)) (Or.inl (by norm_num [r_meter]))
 filter_upwards [(turnover Λ).eventually h0] with s h
 unfold repeatBill labW; rw [show P.thresholdF s=radiusB (F s) from (P.run.meter.boot s).2.1]; rw [coin_zero] at h; rw [Nat.cast_mul]; norm_num only [Nat.cast_ofNat]
 exact h
omit g
lemma repeat_shrink {u v:ℕ}(h:P.repeatBill v f)(k:u≤v): P.repeatBill u f:=by
 unfold repeatBill at *; have hq:0≤14*Worth.meterC (F f):=mul_nonneg (by norm_num) (coin_pos ..).le; apply le_trans ?_ h; gcongr
abbrev plateau (s:ℕ): Cover:= fun j:Axis=> (P.axleQ j (P.thresholdF s))
lemma seat_plan (x:Cover) (k:P.plateau f j≤ x j) : Plans j x f P:=by
 have hz: P.labW f+P.calibration.ℓ + frameRadius j=P.axleQ j (P.thresholdF f):=rfl; change ((P.axleQ j (P.thresholdF f)):ℤ) ≤ _ at k; constructor -- unfold before constructor won't work
 all_goals simp only [nodeC,Pi.add_apply,Pi.one_apply,two_smul]; omega
include g
lemma seat_many : ∀ᶠ s:ℕ in atTop, twiceT (P.plateau s) j ≤ scout P.par d s:=by
 filter_upwards [P.earns_widthT j d g 6] with s h; unfold twiceT; let q:= P.axleQ j (P.thresholdF s); let x:= F s; have ht: (6:ℝ)*q ≤ scout P.par d s:=h.trans (Nat.le_ceil _); have hp:1≤ q:=by unfold q axleQ repeatD; omega
 have hz:6*q≤ scout P.par d s:=by exact_mod_cast ht
 rw [show nodeC (P.plateau s) j=(q:ℤ)+q+1 from ?_]; omega
 unfold plateau; simp [nodeC,q,two_smul]
lemma offers_plans : ∀ᶠ s:ℕ in atTop,(∀ x:Cover, twiceT x j ≤ scout P.par d s → P.repeatBill (twiceT x j) s) ∧ ∃ x:Cover, Plans j x s P ∧ P.repeatBill (twiceT x j) s:=by
 filter_upwards [P.weather_bill d g, P.seat_many j d g] with s h u; exact ⟨fun x v=> P.repeat_shrink h v,P.plateau s,P.seat_plan j _ le_rfl, P.repeat_shrink h u⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.offers_plans
