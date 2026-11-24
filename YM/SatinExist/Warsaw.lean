import YM.SatinExist.Beryl
import YM.SatinExist.Embassy
import YM.SatinExist.Era
import YM.SatinExist.TitleE
import YM.SatinExist.Taint
import YM.SatinExist.Road
import YM.SatinExist.Lunary
import YM.SatinExist.Bond
import YM.SatinExist.Turret
import YM.SatinExist.Lede
import YM.SatinExist.Teres
import YM.SatinExist.ShiftE
import YM.SatinExist.Policed
import YM.SatinExist.Shield
import YM.SatinExist.Cameo
import YM.SatinExist.Hall
import YM.SatinExist.Fence
import SatinThinRampart
import SatinThinAngle
import YM.SatinExist.Glacis
import SatinThinSegno

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
/-! # Train cost comparison on elected printed heights. -/
-- support of tested pair. Need dSpacing condition eventually at roots. Using real checkpoint geometry. Only prices here. 
variable (X:Cover){C e A:ℝ}
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
local notation "aK"=>P.nomadic
local notation "bK"=>P.engine
set_option linter.unusedSectionVars false
open Aria Casting MacroGrid
variable (N₁:P.NightCop) (x:P.Spectrum0 3)(A0:ℝ) (B0:ℝ)(b':ℝ)
local notation "T"=> ℕ × ℕ
variable (v:ℕ→ℕ)(a:ℕ→ (ℕ×ℕ)→ℝ)
local notation "Z"=> P.advocate 3 x j
variable (B:ScoutAnthem P x A0 B0 f r b' v a)
local notation "a₁" i:max=> a i (f,r)
variable (p:f<r)(J:List Axis)
local notation "w" s:max=> P.columnW j s f J
local notation "X'" s:max=> P.rootSpace f s J
local notation "Q'" s:max=> P.column_bill j s f J
local notation "Tk" s:max t:max=> P.spotDuty j (X' s) (w s) (Q' s) x t
variable (hO:Odd P.par.R.L.val)(τ:Aglomerate f r a)(s:ℕ)
local notation "κ"=> P.advocate 3 x j
local notation "λ'"=> P.ManyF j (P.advocate 3 x j)
local notation "ψ"=> P.ColorHil j (P.advocate 3 x j)
local notation "η₀" s:max=> P.fixedStar j f s J
local notation "M₁" i:max=> (P.basePlay x f (v i)).pivot P J
local notation "b₁" i:max=> ((a i (f,r):ℝ):ℂ)
local notation "Z₁" t:max i:max=> b₁ i • P.pillar j κ (M₁ i) (-t) t 0
local notation "Δ" s:max=> P.turtle j s f J
local notation "Ω"=> P.seasons j κ
open SatinTails
open SatinNucleus
variable (u:StrictMono v)(q:ℕ → Coalition)
local notation "Y!"=> P.cinema x f r v a q u
include B u
lemma yuletime : Tendsto (fun i:ℕ=>(((Y!) i).pivot P J).realWidth P j) atTop (𝓝 0):=by
 have hx:Tendsto (fun i=> (P.roomy:ℝ)* P.macroStep (v i)) atTop (𝓝 0):=by simpa only [mul_zero,Function.comp_apply] using (P.macroStep_zero.comp u.tendsto_atTop).const_mul (P.roomy:ℝ)
 exact hx.congr fun _=> by rw [Apron.pivot_w,cinema,P.pleading_w];
omit B u
structure ActualScarab (P:Spine) (x:P.Spectrum0 3)(A:ℕ→P.Apron)(j:Axis)(J:List Axis)(Y₁:ℝ→ (P.ManyF j (P.advocate 3 x j)).Op) : Prop where
 prices : Mosaic P j (P.advocate 3 x j) (fun i=> (A i).pivot P J) (fun _=>1) Y₁
 order : ∃ K>(0:ℝ),∃ z:ℕ,∀ᶠ t in 𝓝[>] 0, ‖Y₁ t‖ ≤ K/t^z
local notation "R₀"=> (P.rewardK f r)
include B u p N₁ τ hO
lemma culmination : ∃ U:ℝ→(λ').Op, ActualScarab P x (P.cinema x f r v a q u) j J U:=by
 obtain ⟨Y',g⟩:=sails_tall P j N₁ x A0 B0 b' v a B p J hO τ
 let T'(t:ℝ):=(R₀:ℂ) • Y' t
 refine ⟨T',⟨?_,?_⟩⟩
 · refine ⟨P.yuletime j x A0 B0 b' v a B J u q, fun t p=>?_⟩ -- order tune
   refine (P.crewCanvas x j f r v (fun i=> (a i (f,r))) u q J t g p).sameC (Eventually.of_forall (fun i=> by exact (one_smul ℂ _).symm)) rfl
 obtain ⟨d,h,n,hk⟩:= P.altitude j N₁ x A0 B0 b' v a B p J hO τ Y' g
 let b:= ‖(R₀:ℂ)‖; refine ⟨(b+1)*d,by unfold b; positivity,n,?_⟩; filter_upwards [hk,self_mem_nhdsWithin] with t p x; unfold T'; rw [norm_smul]; change b * _ ≤ _; refine ((mul_le_mul_of_nonneg_left p (norm_nonneg _)).trans (le_trans ?_ (mul_div_assoc (b+1) .. |>.symm.le))) -- order
 apply mul_le_mul_of_nonneg_right (by linarith); have ht:0<t:=x; positivity
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
