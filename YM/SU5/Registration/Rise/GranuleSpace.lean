import YM.SU5.Registration.Rise.LatestSlots
import YM.SU5.Registration.Rise.PadTransfer
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

/-! # Clock-column long estimates in this election. From phase-independent prices
on mean to ANY spectrum point including x chosen to read the thin probes. Width of
each box MUST stay common here over every tall-scale actor arm of the comparison.
ClockBooking's earned bound is applied at level v (changed coarse-phase probe),
using long banner & No cheap error estimate at volume varying with height.
-/
open SlabMark.ClockBooking
open Aria Casting MacroGrid
local notation "β"=> ruler P.par.block
local notation "β'"=> (16*P.par.block.val:ℕ)
local notation "Z" f:max v:max w:max=> ((P.par.R.L.val:ℕ)^(v-f)*w:ℕ)

/-! # Tying `StampHere` to the actual spacetime registration.

`quoteSpot` sample exact existing mesh placements from granule, extended by arbitrary zero
if not yet in that license, then show its physical coordinates converge. This is not
a continuation nor a small-norm comparison on an ``approximately'' tied root. While
we have time bound (and continuities) also on the colored Hilbert, we'll only have
spatial-price convergence on the spatially continuous part (takes care of adjoints too).
-/
open Germ Alliance
local notation "T"=>timeMesh P.par
variable (x:P.Spectrum0 3) (g:ℕ)(l:List Axis)
local notation "ξ"=> P.advocate 3 x j
local notation "M" s:max w:max=> whenly (timeMesh P.par) s w
local notation "O" s:max=>P.rowClock j g s l
local notation "Y'"=>P.rootSpace g f l
local notation "Π" s:max=>P.clockPlate f s Y'
local notation "A'" s:max=> (P.basePlay x g s).pivot P l
local notation "ζ" s:max=> pivotQ (P.granule (P.megaK g s)) l
local notation "µ" t:max=> P.macroStep t

noncomputable def quoteSpot (g f:ℕ)(l:List Axis)(v:ℕ): Cover:= if h:∃ x:Cover,P.clockPlate f v (P.rootSpace g f l)= pivotQ (P.granule (P.megaK g v)) l+P.sidesPerTick • x then h.choose else 0
local notation "spot" i:max=> P.quoteSpot g f l i
variable (u:g≤f)(L':Odd P.par.R.L.val)
lemma pin_covered : P.pinTime j g f l < (M f (O f):ℝ) := by
 let z:=nodeC (P.rootSpace g f l) j; let A:= P.sidesPerTick; let N₀:= (z.natAbs:ℕ)
 have h:0<z:= P.point_bought j f g l
 have hE:0< (A:ℝ):=Nat.cast_pos.mpr P.sides_pos
 have hz:z=(N₀:ℤ):=by unfold N₀; omega
 have hv: (z:ℝ)= (N₀:ℝ):= by exact_mod_cast hz
 let k:ℝ:= µ f; have hn:0<k:= P.macroStep_pos f; change (z:ℝ)*k/A < ↑(whenly T f (O f))
 unfold whenly; rw [NNReal.coe_mul, NNReal.coe_natCast]; change (z:ℝ)*k/A < (↑(O f):ℝ)*k; rw [div_lt_iff₀ hE, mul_right_comm _ k,hv]
 have hw: N₀ < O f:=by unfold rowClock twiceT; change N₀< 2*N₀+1; omega
 exact mul_lt_mul_of_pos_right (((Nat.cast_lt (α:=ℝ)).mpr hw).trans_le (le_mul_of_one_le_right (by positivity) (show (1:ℝ)≤ (A:ℝ) by exact_mod_cast (Nat.succ_le.mpr P.sides_pos)))) hn
lemma allowance_pivot : (A' v).allowance P j = M v P.roomy:= by
 apply NNReal.eq; change (( (A' v).allowance P j):ℝ)= _; rw [← Apron.width_real,Apron.pivot_w, P.play_width, whenly, NNReal.coe_mul, NNReal.coe_natCast]; rfl
private lemma eta_pivot (v:ℕ) : |(((ζ v) j):ℝ)|≤ (P.echoFoot:ℝ):=by
 -- as in `Promenade.shadow_width`
 obtain h|h:= pivot_alone (P.granule (P.megaK g v)) l j <;> rw [h]; swap; · rw [Int.cast_neg, abs_neg]; exact (abs_of_nonneg (P.tiny_one_ledger v _).1).trans_le (P.tiny_one_ledger v _).2
 exact (abs_of_nonneg (P.tiny_one_ledger v _).1).trans_le (P.tiny_one_ledger v _).2
include u L'
lemma quote_spot_agrees (he:f≤v) : Π v=(ζ v)+P.sidesPerTick • (spot v):=by unfold quoteSpot; rw [dif_pos (P.charge_race g f v u he l L')]; exact (P.charge_race g f v u he l L').choose_spec
lemma quote_moving : Tendsto (fun i=>P.meshPose i (P.quoteSpot g f l i)) atTop (𝓝 (fun j:Axis=>P.pinTime j g f l)):=by
 let y(i:ℕ):= ζ i; let a:ℝ:= P.sidesPerTick; have ha:0<a:=Nat.cast_pos.mpr P.sides_pos
 let ε(i:ℕ):=(P.echoFoot:ℝ)* µ i/ a; have he:Tendsto ε atTop (𝓝 0):=by simpa only [mul_zero,zero_div] using ((P.macroStep_zero.const_mul (P.echoFoot:ℝ)).div_const a)
 apply tendsto_pi_nhds.mpr; intro j
 let d(i:ℕ):ℝ:= ((y i j):ℝ)* µ i/a
 have hd:Tendsto d atTop (𝓝 0):= squeeze_zero_norm' (Eventually.of_forall fun i=> (show ‖d i‖ ≤ ε i from ?_)) he
 · let x:= P.pinTime j g f l; have h: Tendsto (fun i=>x-d i) atTop (𝓝 x):=by simpa only [sub_zero] using tendsto_const_nhds.sub hd
   exact h.congr' ((eventually_ge_atTop f).mono fun i hi=> (P.quote_height j l hi _ (P.quote_spot_agrees g l u L' hi)).symm)
 unfold d ε; simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos ha, abs_of_pos (P.macroStep_pos _)]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (P.eta_pivot j g l i) (P.macroStep_pos i|>.le)) ha.le
lemma quote_fits : ∀ᶠ i:ℕ in atTop,P.StampHere j ((P.basePlay x g i).pivot P l) i (Z f i (O f)) (P.quoteSpot g f l i):=by
 let R:ℝ:= M f (O f); let a(v:ℕ):ℝ:=(P.roomy:ℝ)* µ v; let d(v:ℕ):ℝ:= P.meshPose v (spot v) j; let h:=P.pinTime j g f l; have hd:Tendsto d atTop (𝓝 h):= tendsto_pi_nhds.mp (P.quote_moving g l u L') j
 have ha:Tendsto a atTop (𝓝 0):=by simpa only [mul_zero] using P.macroStep_zero.const_mul (P.roomy:ℝ)
 have he:Tendsto (fun i:ℕ=> R-a i) atTop (𝓝 R):=by simpa only [sub_zero] using tendsto_const_nhds.sub ha
 filter_upwards [ha.eventually_lt hd (P.pin_p j g f l), hd.eventually_lt he (P.pin_covered j g l), eventually_ge_atTop f] with i v w t
 have hP:(A' i).realWidth P j=a i:= ((A' i).width_real P j).trans (by rw [P.allowance_pivot j x g l, whenly,NNReal.coe_mul,NNReal.coe_natCast]; rfl)
 refine P.gives_here j (A' i) _ _ _ ?_ (hP.trans_le (show a i < d i from v).le) ?_
 · exact ((P.basePlay x g i).pivot_s P l).le
 rw [hP, show M i (Z f i (O f))= M f (O f) from matchR (timeMesh P.par) f i (O f) t]; exact (show d i<R-a i from w).le
include x in
lemma quote_time_val : Tendsto (fun i:ℕ=> whenly (timeMesh P.par) i (((P.quoteSpot g f l i) j).toNat)) atTop (𝓝 ((P.pinTime j g f l).toNNReal)):= by
 have hv:Tendsto (fun i:ℕ=> P.meshPose i (spot i) j) atTop (𝓝 (P.pinTime j g f l)):= tendsto_pi_nhds.mp (P.quote_moving g l u L') j
 refine (continuous_real_toNNReal.continuousAt.tendsto.comp hv).congr' ?_
 filter_upwards [P.quote_fits j x g l u L'] with i q
 change (P.meshPose i (spot i) j).toNNReal=_; rw [q.center P j (A' i) i (Z f i (O f)) (spot i),Real.toNNReal_coe]
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms Spine.quote_time_val
