import YM.SU5.Six.Aprons
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Set
open Cheer (Narrow)
variable {P:Spine}{c r:ℕ→ℕ}(B:Launch P c r)
local notation "F"=> P.sidesPerTick
local notation "ε"=> (P.sidesPerTick:ℝ)
local notation "ρ" i:max=> P.dew (c i) (r i)
include B
lemma roundsSlow {X:ℕ→ℝ}{p:ℝ}(u:∀ n,0≤X n)
    (h:Tendsto (fun n=>X n/(r n:ℝ)) atTop (𝓝 p)) : Tendsto (fun n=>(↑⌈X n⌉₊:ℝ)/(r n:ℝ)) atTop (𝓝 p):= by
  have ht:Tendsto (fun n=>(r n:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp B.eager.tendsto_atTop
  have hv:Tendsto (fun n=>(X n+1)/(r n:ℝ)) atTop (𝓝 p):=by
    simp_rw [add_div]; simpa using h.add (tendsto_const_nhds.div_atTop ht (a:=1))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le h hv ?_ ?_
  · exact fun i=> div_le_div_of_nonneg_right (Nat.le_ceil _) (by positivity)
  exact fun i=> div_le_div_of_nonneg_right (Nat.ceil_lt_add_one (u i)).le (by positivity)
lemma pulse_physical : Tendsto (fun i:ℕ=> (P.laterPulse (r i):ℝ)/(r i:ℝ)) atTop (𝓝 ε⁻¹):= by
  apply roundsSlow (X:=fun i=>(r i:ℝ)/ε) B (fun i=>by positivity)
  refine tendsto_const_nhds.congr fun i=> ?_
  have hp:P.sidesPerTick>0:=P.sides_pos; have ht:=B.unitSize i
  field_simp
lemma crewName (x:ℕ→ℕ) {p:ℝ}(h:Tendsto (fun i=>(x i:ℝ)/(r i:ℝ)) atTop (𝓝 p)) : P.bargain r (fun i=> (x i:ℤ)) (ε/2*p):=
  (h.const_mul (ε/2)).congr fun i=> by dsimp only [sidesPerTick,crewB,Heat.gaugeShift]; push_cast; ring
lemma increment_ratio : P.dimensionS c r (fun i=>whenly (timeMesh P.par) (c i) (P.laterPulse (r i))) (1/2):= by
  have H:= P.priceV c r (fun i=> (P.laterPulse (r i):ℤ)) _ (crewName B _ (pulse_physical B)) B.unitSize
  have ht:0< ε:= by exact_mod_cast P.sides_pos
  rw [show ε/2* ε⁻¹=1/2 from by field_simp] at H
  exact H.congr fun i=>congrArg (·/ρ i) (natural_time (timeMesh P.par) (c i) _)
lemma limit_roof : Tendsto (fun i=>(P.probeRoof (r i):ℝ)/(r i:ℝ)) atTop (𝓝 5):=by
  let u:ℝ := 3*P.calibration.ℓ+1
  have ht:Tendsto (fun n=>(r n:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp B.eager.tendsto_atTop
  have he := ((show Tendsto (fun i=>u/(r i:ℝ)) atTop (𝓝 0) from tendsto_const_nhds.div_atTop ht).add_const (4:ℝ)).add ((pulse_physical B).const_mul ε)
  rw [mul_inv_cancel₀ (show ε≠0 from Nat.cast_ne_zero.mpr P.sides_pos.ne'),zero_add,show (4:ℝ)+1=5 by norm_num] at he
  refine he.congr fun i=>?_
  dsimp only [probeRoof,u,Function.comp_apply]; push_cast
  field_simp [(show (r i:ℝ)≠0 from Nat.cast_ne_zero.mpr (B.unitSize i).ne')]; ring
lemma limit_times_width : Tendsto (fun i=>P.probeWidth (c i) (r i) 3/(ρ i)) atTop (𝓝 (5/2)):=by
  have he:Tendsto (fun i=>(P.probeClock (r i) 3:ℝ)/(r i:ℝ)) atTop (𝓝 (5/ε)):=by
    let a(i):ℝ:= (P.probeRoof (r i):ℝ)/ε
    have hp : Tendsto (fun i=>a i/(r i:ℝ)) atTop (𝓝 (5/ε)):= ((limit_roof B).div_const ε).congr fun i=> by dsimp [a]; ring
    have ht:Tendsto (fun n=>(r n:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp B.eager.tendsto_atTop
    have hx:= (tendsto_const_nhds.div_atTop ht (a:=1)).add (roundsSlow B (X:=a) (fun i=>by unfold a; positivity) hp)
    rw [zero_add] at hx
    refine hx.congr fun i=>?_
    rw [probeClock,Function.update_self,Nat.cast_add,add_div,Nat.cast_one]
  have hh:= P.priceV c r (fun i=> (P.probeClock (r i) 3:ℤ)) _ (crewName B _ he) B.unitSize
  have hp:0< ε:= by exact_mod_cast P.sides_pos
  rw [show ε/2*(5/ε)=5/2 from by field_simp] at hh; exact hh
lemma limit_space_width {j:Axis}(p:j≠3):Tendsto (fun i=> P.probeWidth (c i) (r i) j/(ρ i)) atTop (𝓝 0):= by
  have ht:Tendsto (fun n=>(r n:ℝ)) atTop atTop:= tendsto_natCast_atTop_atTop.comp B.eager.tendsto_atTop
  have he:Tendsto (fun i=>(P.probeClock (r i) j:ℝ)/(r i:ℝ)) atTop (𝓝 0):= by simp_rw [probeClock,update_of_ne p]; exact tendsto_const_nhds.div_atTop ht
  have hp:= P.priceV c r (fun i=> (P.probeClock (r i) j:ℤ)) _ (crewName B _ he) B.unitSize
  rw [mul_zero] at hp; exact hp
private lemma shrinkWidth (j:Axis){p:ℝ}(h:Tendsto (fun i=> P.probeWidth (c i) (r i) j/(ρ i)) atTop (𝓝 p)) : Tendsto (fun i=> P.probeWidth (c i) (r i) j) atTop (𝓝 0):= by
  have ht:= h.mul (P.proper_dew c r B)
  rw [mul_zero] at ht
  exact ht.congr fun i=> div_mul_cancel₀ _ (P.dew_pos _ (B.unitSize i)).ne'
lemma limit_width (j:Axis) : Tendsto (fun i=> P.probeWidth (c i) (r i) j) atTop (𝓝 0) := by
  by_cases h:j=3; · subst j; exact shrinkWidth B _ (limit_times_width B)
  exact shrinkWidth B j (limit_space_width B h)
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
