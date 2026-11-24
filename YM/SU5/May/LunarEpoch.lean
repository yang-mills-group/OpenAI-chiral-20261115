import YM.SU5.May.TorqueRent
import YM.SU5.May.LunarFloor
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 32000
set_option maxRecDepth 5000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.Torque
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open SlabMark MeshClock Tilted WindRose
open Fock Lat Laurent Wilson Cube Finset Branch Scree RG Spire Vale Pastry Peaks Dial Phase Lifted Skye Tapestry.Exhibition Tapestry.Altitude Tenant Rush Tulip
open PolarArchives Brazier
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))
open LocalLimit.Intermediate Harbour
open Hygrometry Hygrometry.MeterFunding May.Lunar
open Push.SectorMeasure
open Advance.Depths
local notation "𝗠" i:max j:max=> Journey.side Y i j
variable (m t s R:ℕ) (P:Ramp)
open May.TorqueBeam Therapies Advance.Whorl FloeRoom
local notation "σ" m:max=> (((Y.ir m).val):ℝ)
abbrev analogK (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (m:ℕ):= ((((Y.ir m).val:ℕ):ℝ)^(1/20:ℝ))
noncomputable def flowK (Y:Course Λ (VolumeCape.Dream.Nimbus l)) (m:ℕ) := Nat.floor (analogK Y m)
noncomputable def level:ℝ:= 1/40
lemma level_p : 0 <level:=by unfold level; norm_num
local notation "D" i:max=> flowK Y i
local notation "T" i:max=> turnUp Y i
local notation "Pμ" i:max => precisionAt Λ (turnUp Y i)
lemma flow_grows : Tendsto (flowK Y) atTop atTop:= tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num:(0:ℝ)<1/20)).comp (tendsto_natCast_atTop_atTop.comp Y.ir_grows.tendsto_atTop)) -- tune ↑ val→
lemma earth_m: (flowK Y m:ℝ)^20≤ σ m:=by
 unfold flowK; set a:= analogK Y m; apply (pow_le_pow_left₀ (show 0 ≤ (Nat.floor a:ℝ) from Nat.cast_nonneg _) (Nat.floor_le (by unfold a analogK; positivity)) 20).trans_eq; unfold a analogK; rw [←Real.rpow_mul_natCast (by positivity)]; norm_num
lemma moon_m : (( ((σ m)^level):ℝ)^ (2:ℕ)) < (flowK Y m:ℝ)+1:=by unfold level flowK; rw [←Real.rpow_mul_natCast (by positivity)]; rw [show (1/40:ℝ)* ↑(2:ℕ)=1/20 from (by norm_num)]; exact Nat.lt_floor_add_one _
noncomputable def bindingC(Λ:Preparation):ℝ:= (Λ.block.val:ℝ)*2*halfer
private lemma earth_1:1 < bindingC Λ:= by
 unfold bindingC; rw [mul_assoc]; have h:1 ≤ (Λ.block.val:ℝ):=by exact_mod_cast (show 1 ≤ Λ.block.val from Λ.block.property)
 apply lt_of_lt_of_le _ (le_mul_of_one_le_left (show (0:ℝ) ≤ 2*halfer from mul_nonneg zero_le_two halfLegal.le) h); linarith only [half_bill]
lemma ocean_l : rimB (Journey.side Y m s)= bindingC Λ*(σ m)*precisionAt Λ s:=by
 unfold rimB; have hp:=size_t Y m 0 s; rw [Nat.zero_add] at hp; rw [hp]; unfold bindingC resist precisionAt; ring
private lemma h_tend (Λ:Preparation):1<(Λ.R.L.val:ℝ):=by exact_mod_cast (show 1< Λ.R.L.val by have ht:=Λ.R.coarse; omega) -- tune
lemma zenithL : Tendsto (precisionAt Λ ∘ turnUp Y) atTop atTop:= (tendsto_pow_atTop_atTop_of_one_lt (h_tend Λ)).comp (tendsto_atTop.mpr (fun i=> ((securities Y i 1 one_pos)).mono fun _ h=> h.1.le)) -- H param
lemma fundsReb : ∀ᶠ m in atTop, (flowK Y m:ℝ)^10 ≤ rimB (𝗠 m (T m)) ∧80≤ rimB (𝗠 m (T m)) ∧tuition P (flowK Y m) ≤ Real.exp (-(((σ m)^level):ℝ)):=by
 have ht:=flow_grows Y
 let B:=volE*(apron P+1); have hV:= volP; have hP:= apron_p P; let hf(m):=(flowK Y m:ℝ)
 filter_upwards [(tendsto_natCast_atTop_atTop.comp ht).eventually_ge_atTop (1000:ℝ), zenithL Y |>.eventually_ge_atTop 1,(Real.tendsto_exp_atTop.comp ((tendsto_natCast_atTop_atTop.comp ht).atTop_div_const (show (0:ℝ)<8 by norm_num))).eventually_ge_atTop B] with m mm hm hs -- syntax
 let D':ℝ:=flowK Y m; let L:=turnUp Y m; let R:= rimB (𝗠 m L); change 1000 ≤ D' at mm; change B ≤ Real.exp (D'/8) at hs; change 1≤ precisionAt Λ L at hm; let r:ℝ:= σ m; have hx:(1:ℝ)≤D':=le_trans (by norm_num) mm
 have he:D'^10 ≤ r:= (pow_le_pow_right₀ hx (show 10≤20 by omega)).trans (earth_m Y m); have hg:r≤R:=by rw [show R = bindingC Λ*r*precisionAt Λ L from ocean_l ..]; exact (le_mul_of_one_le_left (show 0≤r from Nat.cast_nonneg _) earth_1.le).trans (le_mul_of_one_le_right (mul_nonneg (zero_lt_one.trans earth_1).le (Nat.cast_nonneg _)) hm)
 have hy: 1000 ≤ D'^10:= le_trans mm (by nth_rw 1 [←pow_one D']; exact pow_le_pow_right₀ hx (by norm_num)); refine ⟨he.trans hg,le_trans (by norm_num) (hy.trans (he.trans hg)),?_⟩
 have hcZ:0≤D':=zero_le_one.trans hx; have hp: r^level ≤ D'/8:=by
    let x:=r^level; have hv:x^2 ≤ D'+1:= (moon_m Y m).le; apply (sq_le_sq₀ (show 0≤r^level from Real.rpow_nonneg (by unfold r; positivity) _) (by positivity)).1; refine hv.trans ?_; nlinarith only [mm]
 apply (mul_le_mul_of_nonneg_right hs (tollVal _).le).trans; rw [tollV,←Real.exp_add]; apply Real.exp_monotone; change D'/8+-D'/4 ≤ -(r^level); linarith only [hp]
#print axioms ocean_l
#print axioms fundsReb
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Screened.Torque
