import YM.SU5.SatinWard.Resolution.BroochA
import YM.SU5.SatinWard.Resolution.Carnation
import YM.SU5.SatinWard.Resolution.Journal
import YM.SU5.SatinWard.Resolution.Synod
import YM.SU5.SatinWard.Resolution.Achilles
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
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
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
open BProof Pressure
open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
namespace Regulator
local notation "Ω" s:max=> hat P.par.R.L P.par.x s
open CasaF.Signboard CF.Tap SignSlot ShapeLab Emu
open CF.Fir _root_.YM.Regis.Circuit.SpringDay.Spring
variable {s:ℕ}
local notation "ζ"=> CF.Papyrus.Franc.SatinForce.Flash
local notation "K₁"=> principalKid
local notation "K₀"=> Op SU.Slot
-- economy grouping spin then family.Q equals trace pairing
namespace Orchid
open _root_.YM.Regis.Circuit.SpringDay.Spring
variable (j q:Axis)
noncomputable def hornLane(z:ℝ):Gaia:= WithLp.toLp 2 (fun i:Axis=> if i=j then z else (80:ℝ))
abbrev longJ(j:Axis)(z:ℝ): Axis→ℝ:= WithLp.ofLp (hornLane j z)
abbrev cashPeak (j q:Axis):ℝ:= if j=q then -1 else 1
abbrev cyVal(j q:Axis)(x:Gaia):ℝ:= cashPeak j q * (64*kinCost q x)
noncomputable def lipRise : Gaia:= (2000:ℝ) • (YM.basis j:Gaia) -- 1k to 3k; default instance Nat SMul ℝ annotated? cast
local notation "v0"=> hornLane j 1000
local notation "v1"=> hornLane j 3000
lemma hornJ (i:Axis)(z:ℝ):(hornLane j z).ofLp i = if i=j then z else 80:=rfl
lemma roseWeight : v0+lipRise j=v1:=by
 ext1 i; simp only [PiLp.add_apply,lipRise,PiLp.smul_apply,YM.basis,hornJ,PiLp.single_apply]; by_cases h:i=j <;> norm_num [h] -- simp tap
lemma R_sq (z:ℝ): ‖hornLane j z‖^2=z^2+3*80^2:=by rw [EuclideanSpace.norm_sq_eq]; simp_rw [hornJ]; fin_cases j <;> norm_num [Axis, Fin.sum_univ_succ,Real.norm_eq_abs,sq_abs] <;> (repeat' (first| rw [if_pos (by decide +kernel)]| rw [if_neg (by decide +kernel)]| split_ifs<;>try omega )); all_goals ring -- maybe eq default norm cast
lemma at_i (z:ℝ):hornLane j z ≠0:=by rw [← norm_ne_zero_iff]; intro h; apply ne_of_lt (?_:0< ‖hornLane j z‖^2) (show (0:ℝ)= _ by rw [h]; ring); rw [R_sq]; positivity
lemma gradientNorm (x:Gaia) : ‖x‖^2=∑ i:Axis, (x.ofLp i)^2:= by rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs,sq_abs]
lemma fieldHeight (x:Gaia)(p:x≠0) : kinCost j x = -8*Maxwell.normal^2*(‖x‖^2)⁻¹^4*(2*(x.ofLp j)^2-‖x‖^2):=by
 unfold kinCost wingKernel; simp_rw [Maxwell.first_Green p]; let r:=-2*Maxwell.normal*(‖x‖^2)⁻¹^2; have hx(i:Axis): -2*Maxwell.normal*x.ofLp i*(‖x‖^2)⁻¹^2=r*x.ofLp i:=by unfold r; ring
 simp_rw [hx,mul_pow (r:ℝ),←mul_sum,←gradientNorm]; unfold r; ring
lemma rectangle_pos :0 < cyVal j q v0 ∧0 < cyVal j q v1∧cyVal j q v1 < cyVal j q v0:=by
 have h:0< Maxwell.normal^2:=by have h:=Maxwell.normal_pos; positivity; -- positivity type
 unfold cyVal; simp_rw [fieldHeight _ _ (at_i j _),R_sq,hornJ]; unfold cashPeak; by_cases hq:j=q <;>simp only [hq,↓reduceIte]; -- careful Ne.symm garbage
 all_goals try rw [if_neg (Ne.symm hq), if_neg (Ne.symm hq)]
 all_goals norm_num <;> constructor <;> linarith only [h]
#print axioms rectangle_pos
lemma cRemain (x:Gaia)(p:x≠0): ContinuousAt (cyVal j q) x:=by
 have he(k:Axis): ContinuousAt (fun x=> wingKernel x k) x:=(gradGradientSmooth p _).continuousAt -- `n` implicit?
 have h:ContinuousAt (fun x=>∑ i:Axis,(wingKernel x i)^2) x:=tendsto_finsetSum (x:=𝓝 x) univ (fun i _=> (he i).pow 2)
 exact continuousAt_const.mul (continuousAt_const.mul (continuousAt_const.mul ((continuousAt_const.mul ((he q).pow 2)).sub h)))
lemma q_even (x:Gaia)(p:x≠0): kinCost q (-x)=kinCost q x:=by simp only [fieldHeight _ _ p,fieldHeight _ _ (neg_ne_zero.mpr p),norm_neg,WithLp.ofLp_neg,Pi.neg_apply,even_two.neg_pow] -- lemma name
structure JReady (j q:Axis)(u:ℝ)(d:Gaia):Prop where
 off : d≠0
 near :u ≤ cyVal j q d
 far : u ≤ cyVal j q d-cyVal j q (d+lipRise j)
 farOff : d+lipRise j ≠0
 bot :∀ i:Axis,60 ≤ d i
 top :∀ i:Axis,d i ≤ 1700 -- far top add 2k
lemma sensor :∃ u:ℝ,0 < u∧ ∀ᶠ d in 𝓝 (v0), JReady j q u d:=by
 let f:=cyVal j q; obtain ⟨p,t,r⟩:=rectangle_pos j q; have p':0<f v0-f v1:= sub_pos.mpr r; obtain ⟨u,u₀,tU⟩:= exists_between (lt_min p p'); have h:= tU.trans_le (min_le_left ..); have h':= tU.trans_le (min_le_right ..)
 have he:ContinuousAt (fun d=>f (d+lipRise j)) v0:= (show ContinuousAt f (v0+lipRise j) by rw [roseWeight]; exact cRemain _ _ _ (at_i j 3000)).comp (g:=f) (f:=fun x:Gaia=> x+lipRise j) (continuous_id.add continuous_const).continuousAt
 have P: ContinuousAt f v0:=cRemain j q _ (at_i j 1000); refine ⟨u,u₀,?_⟩
 have hmk:∀ᶠ d:Gaia in 𝓝 v0,∀ i:Axis,60 ≤ d i ∧ d i≤1700:=by
   refine eventually_all.mpr (fun i=>?_); let X:Gaia→L[ℝ]ℝ:= EuclideanSpace.proj i; have h:60<X v0∧ X v0<1700:=by change 60 < WithLp.ofLp (v0) i ∧ WithLp.ofLp (v0) i < _; rw [hornJ]; split_ifs <;> norm_num
   exact ((X.continuous.tendsto _).eventually (lt_mem_nhds h.1)).and ((X.continuous.tendsto _).eventually (gt_mem_nhds h.2)) |>.mono (fun i p=>⟨le_of_lt p.1,le_of_lt p.2⟩)
 filter_upwards [eventually_ne_nhds (at_i j 1000), P.eventually (lt_mem_nhds h), (P.sub he).eventually (lt_mem_nhds (show u<f v0-f (v0+lipRise j) by rw [roseWeight]; exact h')), (show Continuous (fun d:Gaia=> d+lipRise j) from continuous_id.add continuous_const).continuousAt.eventually (eventually_ne_nhds (by rw [roseWeight]; exact at_i j 3000 : v0+lipRise j ≠ 0)), hmk] with d hz ht v a b; exact ⟨hz,le_of_lt ht,le_of_lt v,a,fun i=>(b i).1,fun i=> (b i).2⟩
#print axioms sensor
end Orchid
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
