import SatinThinBreakers

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
/-! # charge clock extended apertures to EVERY axis & T seam arc. -/
local notation "zℝ" => (P.sidesPerTick:ℝ)
local notation "zℤ" => (P.sidesPerTick:ℤ)
local notation "N'" f:max s:max l:max j:max=> (nodeC (P.rootSpace f s l) j)
lemma node_ceiling(s f:ℕ)(l:List Axis): N' f s l j≤ P.baseK s + (2*frameRadius j+ 2*P.sidesPerTick:ℕ):=by
 have ht:= (P.broadly j s f l).2; unfold baseK axleQ; let he:= frameRadius; change P.rootSpace f s l j ≤ ((P.labW s + P.calibration.ℓ+ he j:ℕ):ℤ)+zℤ at ht
 -- simp only with footprints abbrev issue
 let Y' := P.rootSpace f s l; change nodeC Y' j ≤ _; change Y' j ≤ _ at ht; simp only [nodeC,two_smul,Pi.add_apply,Pi.one_apply]; change Y' j+Y' j+1 ≤ ((2*(P.labW s+P.calibration.ℓ+ he 3)+1:ℕ):ℤ)+_; unfold he at *; omega
lemma earns_newsprint(d:ℝ)(u:0<d): ∀ᶠ s:ℕ in atTop,∀ (f:ℕ)(l:List Axis), twiceT (P.rootSpace f s l) j ≤ scout P.par d s:=by
 -- use scale multiple
 let c:ℕ:= 16*(frameRadius j+ P.sidesPerTick+1); let X(s:ℕ):= hat P.par.R.L P.par.x s
 filter_upwards [P.earns_widthT 3 d u (c:ℝ)] with s t f l
 let b:= P.axleQ 3 (P.thresholdF s); let x:= P.rootSpace f s l; have h : c*b ≤ scout P.par d s:=by exact_mod_cast (show (c:ℝ)*b≤ (scout P.par d s:ℝ) from t.trans (Nat.le_ceil (trailℓ d (X s))))
 refine le_trans ?_ h; have he:= P.node_ceiling j s f l; have hb:1≤ b:= by unfold b axleQ repeatD; omega
 have hn:= Nat.mul_le_mul_left (frameRadius j+ P.sidesPerTick+1) hb; rw [Nat.mul_one] at hn
 unfold twiceT c; rw [Nat.mul_assoc]; change (nodeC (P.rootSpace f s l) j) ≤ (↑(2*b+1):ℤ)+_ at he; have ht:=P.point_bought j s f l; have hp:b≤ (frameRadius j+ P.sidesPerTick+1)*b:= Nat.le_mul_of_pos_left _ (by omega); omega
abbrev pinTime(f s:ℕ)(l:List Axis) : ℝ:= (nodeC (P.rootSpace f s l) j:ℝ)*P.macroStep s /zℝ
lemma pin_p(f s:ℕ)(l:List Axis) : 0 < P.pinTime j f s l:=by let r:=(nodeC (P.rootSpace f s l) j); exact div_pos (mul_pos (Int.cast_pos.mpr (P.point_bought j s f l)) (P.macroStep_pos _)) (Nat.cast_pos.mpr P.sides_pos)
lemma pin_approach (f:ℕ)(l:List Axis): Tendsto (fun s=>P.pinTime j f s l) atTop (𝓝 0):=by
 let d:=2*frameRadius j+ 2*P.sidesPerTick; let v:ℝ:= (d:ℝ); let Y(r:ℕ):=v*P.macroStep r/zℝ; have ht:Tendsto Y atTop (𝓝 0):=by simpa only [mul_zero,zero_div,Y] using ((P.macroStep_zero.const_mul v).div_const zℝ); -- newline after tactic inner by!
 let W0(s:ℕ):= P.flightCap s+Y s; have hw:Tendsto W0 atTop (𝓝 0):=by simpa only [add_zero] using P.flight_soon.add ht
 refine squeeze_zero (fun s=>(P.pin_p ..).le) (fun s=>?_) hw; have he: (nodeC (P.rootSpace f s l) j:ℝ)≤ (P.baseK s:ℝ)+v:=by
   have h:= (Int.cast_le (R:=ℝ)).mpr (P.node_ceiling j s f l); push_cast only [Int.cast_add,Int.cast_natCast] at h; exact h
 unfold W0 Y flightCap; rw [← add_div,← _root_.add_mul]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he (P.macroStep_pos s|>.le)) (Nat.cast_nonneg _)
-- calendar
variable (l:List Axis)
local notation "Y₀" f:max s:max=> P.rootSpace f s l
abbrev lampR (f s v:ℕ) : Prop:= v ≥ s ∧ s ≥ f -- unused
local notation "shadow_" f:max v:max=> pivotQ (P.granule (P.megaK f v)) l
private lemma shadow_width (v:ℕ) : |(( (shadow_ f v) j):ℝ)|≤ (P.echoFoot:ℝ):=by
 obtain h|h:= pivot_alone (P.granule (P.megaK f v)) l j <;> rw [h]; swap; · rw [Int.cast_neg, abs_neg]; exact (abs_of_nonneg (P.tiny_one_ledger v _).1).trans_le (P.tiny_one_ledger v _).2
 exact (abs_of_nonneg (P.tiny_one_ledger v _).1).trans_le (P.tiny_one_ledger v _).2
lemma lap_quote(s v:ℕ)(p:s ≤ v)(o:Cover) : (P.clockPlate s v o j:ℝ)*P.macroStep v=(nodeC o j:ℝ)*P.macroStep s:=by
 unfold clockPlate; rw [Pi.smul_apply,nsmul_eq_mul]; push_cast only [Int.cast_mul,Nat.cast_pow,Int.cast_natCast,Int.cast_pow]; linarith only [congrArg ((nodeC o j:ℝ)*·) (P.daysF v s p)]
lemma quote_height(u: s ≤ v) (X:Cover)(g:P.clockPlate s v (Y₀ f s)=(shadow_ f v)+P.sidesPerTick • X) : P.meshPose v X j=P.pinTime j f s l - (((shadow_ f v) j):ℝ) * P.macroStep v/zℝ:=by
 unfold pinTime; rw [← P.lap_quote j s v u, ← sub_div, ← _root_.sub_mul, P.pose_w]; have h:= congrFun g j; have he: (P.clockPlate s v (Y₀ f s) j:ℝ)= (( ( (shadow_ f v) j):ℤ):ℝ)+ zℝ*(X j:ℝ):=by
    rw [h,Pi.add_apply,Pi.smul_apply,nsmul_eq_mul]; push_cast only [Int.cast_add,Int.cast_mul,Int.cast_natCast] -- tune symmetry
 rw [he]; apply (eq_div_iff (show zℝ ≠ 0 from (Nat.cast_pos.mpr P.sides_pos).ne')).mpr; ring
lemma quote_time {e:ℝ}(h:f ≤ s)(t:P.pinTime j f s l < e)(p:Odd P.par.R.L.val): ∀ᶠ v:ℕ in atTop,v≥s ∧ ∃ X:Cover,P.clockPlate s v (Y₀ f s)=(shadow_ f v)+P.sidesPerTick • X ∧ P.roomy*P.macroStep v < P.meshPose v X j ∧ P.meshPose v X j ≤ e:=by
 let t':= P.pinTime j f s l; let c(v:ℕ):ℝ:= (P.echoFoot:ℝ)*P.macroStep v/zℝ; let d(v:ℕ):ℝ:= ((( (shadow_ f v) j):ℤ):ℝ)*P.macroStep v/zℝ
 have hc:Tendsto c atTop (𝓝 0):=by simpa only [mul_zero,zero_div,c] using ((P.macroStep_zero.const_mul (P.echoFoot:ℝ)).div_const zℝ)
 have hd:Tendsto d atTop (𝓝 0):= squeeze_zero_norm' ((Eventually.of_forall fun r=> (show ‖d r‖ ≤ c r from ?_))) hc
 have ht:Tendsto (fun r:ℕ=> t'-d r) atTop (𝓝 t'):=by simpa only [sub_zero] using tendsto_const_nhds.sub hd
 have hw:Tendsto (fun r:ℕ=> (P.roomy:ℝ)*P.macroStep r) atTop (𝓝 0):=by simpa only [mul_zero] using (P.macroStep_zero.const_mul (P.roomy:ℝ))
 filter_upwards [eventually_ge_atTop s,hw.eventually_lt ht (P.pin_p j f s l), ht.eventually (ge_mem_nhds t)] with v v0 u q; obtain ⟨X,V⟩:= P.charge_race f s v h v0 l p; exact ⟨v0,X,V,u.trans_eq (P.quote_height j l v0 X V).symm, le_trans ((P.quote_height j l v0 X V).le) q⟩ -- invalid method
 simp only [d,Real.norm_eq_abs]; rw [abs_div, abs_mul, abs_of_pos (P.macroStep_pos _), abs_of_pos (show 0< zℝ from Nat.cast_pos.mpr P.sides_pos)]; exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (P.shadow_width j l r) (P.macroStep_pos _|>.le)) (Nat.cast_nonneg _)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.quote_time
