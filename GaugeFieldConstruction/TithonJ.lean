import GaugeFieldConstruction.UniJ
import GaugeFieldConstruction.FrayTideJ
import GaugeFieldConstruction.SteepleJ
import GaugeFieldConstruction.MovingH
import GaugeFieldConstruction.ZagoraJ
import GaugeFieldConstruction.VirenneJ
import GaugeFieldConstruction.TrollopJ
import GaugeFieldConstruction.ZucatoJ
import GaugeFieldConstruction.KronenJ
import GaugeFieldConstruction.MapicoJ
import GaugeFieldConstruction.LongBowJ
import GaugeFieldConstruction.OrigamiJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.TuristaJ
import GaugeFieldConstruction.WharfΤJ
import GaugeFieldConstruction.MoonθεJ
import GaugeFieldConstruction.LucernaJ
import GaugeFieldConstruction.EmeraldYJ
import GaugeFieldConstruction.Limbra3
import GaugeFieldConstruction.AshtonM
import GaugeFieldConstruction.Accomplished
import GaugeFieldConstruction.Kabul
import GaugeFieldConstruction.Fana
import GaugeFieldConstruction.Garlic
import GaugeFieldConstruction.Ochre
import GaugeFieldConstruction.Coral
import GaugeFieldConstruction.Dales
import GaugeFieldConstruction.Harries
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
namespace RosterJ
variable (P:Spine) {X:Type}[Fintype X][LinearOrder X]
open ProbeθJ Preparation Yoke
-- Pose. Film any from Advent plus f mirrors. only valid Stamps.S.
local notation "KΑ"=>P.calibration
local notation "Kγ"=>P.par
local notation "Lγ"=> P.par.R.L
local notation "ℓν"=>P.par.R.L.val
local notation "HΥ"=> inkΛJ
variable (x:P.VMark) (f s:ℕ) (j:Axis)
open SlabMark SlabMark.Etch BProof BProof.PricePort Gleam Gleam.clocks Py.Rate Py.Rate.LocalLimit
local notation "Δf"=> WorkWJ P f
local notation "Υ_" s:max=> XûJ P.par P.width s
local notation "ωf" s:max=> hat P.par.R.L P.par.x s
abbrev ΚappaDistJ (P:Spine)(f:ℕ):ℝ:= 2*Real.exp (5*saveZ (hat P.par.R.L P.par.x f)*(SlabMark.Etch.ratio P.calibration.B (WorkWJ P f):ℝ))
lemma ΚOfferJ(i n:ℕ)(p:Collapse_J P n i f): SkyWJ P.par (side P.run i f) f≤ (ΚappaDistJ P f)^n:=by
 obtain ⟨r,a,h⟩:=p; have hx:= h.1; have hv:0<r:=a.pos; have hn:1 ≤ n:=by
    by_contra! K
    have t: n=0:=by omega
    rw [t,Nat.mul_zero] at hx
    exact (Nat.not_lt_of_ge hx) (pow_pos (mul_pos (by norm_num) hv) _)

 let s:=saveZ (ωf f); have hs:0≤5*s:= mul_nonneg (by norm_num) ((coin_pos ..).le); let V:=SlabMark.Etch.ratio P.calibration.B (WorkWJ P f); let M:=side P.run i f; let F:=Real.exp (5*s*V)
 have hq:1 ≤ F:=Real.one_le_exp (mul_nonneg hs (Nat.cast_nonneg _)); have h':Real.exp (5*s*sites M) ≤ F^n:=by
    have he: sites M ≤ V*n:=by
       have ht:=a.density h; unfold sites; exact_mod_cast ht
    unfold F; rw[←Real.exp_nat_mul]; exact Real.exp_monotone ((mul_le_mul_of_nonneg_left he hs).trans_eq (by ring))
 change 1+Real.exp _≤(2*F)^n; rw[mul_pow]; have hp:1≤ F^n:=one_le_pow₀ hq; have he: (2:ℝ)≤ 2^n:= le_self_pow₀ (by norm_num) (by omega); nlinarith only [h',hp,mul_le_mul_of_nonneg_right he (zero_le_one.trans hp)]
-- ratio cost rent uniformly even as n path varies.
abbrev WProgJ (P:Spine)(x:ℝ):ℕ:=100*(CapLJ P.par P.width+100+(YM.Pressure.radiusB x)^3)
lemma FiatHighJ : RunRate 0 0 (fun x=>(WProgJ P x:ℝ)):=by
 have ht: RunRate 0 0 (fun x:ℝ=> (YM.Pressure.radiusB x:ℝ)):= ceiling_b (BProof.PL.log_y.pow 2) (Eventually.of_forall fun x=>sq_nonneg _)
 unfold WProgJ; push_cast; refine RunRate.cmul ((RunRate.const _).add ?h) 100
 case h=> simpa using (ht.pow 3)
lemma InterestϖJ : RunRate 0 0 (fun x=>(SlabMark.Etch.ratio P.calibration.B (WProgJ P x):ℝ)):=by
 let B:=P.calibration.B; have he:=FiatHighJ P
 unfold SlabMark.Etch.ratio SlabMark.Etch.pitch; simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
 apply RunRate.cmul _ 128; simpa only [zero_mul,WProgJ,Nat.cast_mul,Nat.cast_ofNat] using ((he.cmul (16*(B.val:ℝ))).pow 4)
lemma RentFJ : Tendsto (ΚappaDistJ P) atTop (𝓝 2):=by
 let F(u:ℝ):= 5*saveZ u*(SlabMark.Etch.ratio P.calibration.B (WProgJ P u):ℝ)
 have h: Tendsto F atTop (𝓝 0):= ((show RunRate (-gratuity/2) 0 (fun i:ℝ=>5*saveZ i) from (RunRate.coins ..).cmul _).mul (InterestϖJ P)).tends (Or.inl (by norm_num [gratuity]))
 have hz:Tendsto (fun i:ℕ=>Real.exp (F (ωf i))) atTop (𝓝 1):=by simpa only [Function.comp_def,Real.exp_zero] using (Real.continuous_exp.continuousAt.tendsto.comp (h.comp (Py.Rate.LocalLimit.turnover P.par)))
 simpa using (hz.const_mul (2:ℝ)) -- tune Volk.WProg casts
lemma meansOmJ : ∃ z':ℝ,1≤z'∧∀ f:ℕ, ΚappaDistJ P f≤z':=by
 obtain ⟨C,v⟩:=(RentFJ P).bddAbove_range
 exact ⟨max 1 C,le_max_left ..,fun i=>(v (Set.mem_range_self _)).trans (le_max_right ..)⟩ -- mem_range_self arity tune
#print axioms ΚOfferJ
#print axioms meansOmJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
