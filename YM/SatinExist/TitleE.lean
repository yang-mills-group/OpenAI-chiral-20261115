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
local notation "χ"=>P.advocate 3 x j
local notation "X'" s:max=> P.rootSpace f s J
local notation "Q'" s:max=> P.column_bill j s f J
local notation "Tk" s:max t:max=> P.spotDuty j (X' s) (w s) (Q' s) x t
include B N₁ p
-- uniform across all s at *these field campuses*, etc.
lemma gym_train : ∃ W'> (0:ℝ),∃ z≥(1:ℝ),∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop, ‖( (a i (f,r)):ℂ) • P.spotDuty j (P.rootSpace f s J) (P.columnW j s f J) (P.column_bill j s f J) x (v i)‖ ≤ W'*z^s :=by
 obtain ⟨D,H₀⟩:= P.column_paid j f J A0; let T':=zoomC P.par.R.L; let K':=4*T'; have he:1≤ T':=zoomC_p _
 let M:=zoomM P.par.R.L; have h:0<M:=zoomM_p _
 have hp:0≤D:=by obtain ⟨t,h⟩:=H₀.exists; exact le_trans (Real.sqrt_nonneg _) h.1
 let P':=K'*(2*D+ 2*(D/M))+1; have ht:0<K':=mul_pos (by norm_num) (zero_lt_one.trans_le he)
 refine ⟨P',show 0<P' by unfold P'; positivity,T',he,?_⟩
 filter_upwards [H₀,eventually_ge_atTop r] with s ⟨g,t⟩ e
 let f₀:= X' s; let w₀:= P.columnW j s f J
 filter_upwards [(P.ant_climbs x A0 B0 b' v a B).eventually_ge_atTop (s+1)] with i hv
 obtain ⟨c,l,U⟩:= P.ant_pass x A0 B0 b' v a B i; have N:f ≤ s:= le_trans p.le e
 have u₀:s < s+1:= Nat.lt_succ_self _; have v₀:r ≤ s+1:= e.trans u₀.le
 let k:= U.plans _ (show chargeSpan f (v i) (s,s+1) from ⟨N,u₀,hv⟩)
 have hg: ∀ᶠ i:ℕ in atTop, Credentials P.run (P.nomadic i) (P.engine i) A0 s (s+1) ∧ ShelterCost B0 P.run s (P.nomadic i) (P.engine i):= (k.treasury.room).mono (fun i y=>⟨ (y.1.Q).part _ _ _ le_rfl u₀.le hv,y.2⟩)
 let y₀:= Tk s (s+1)
 let u:=4*T'^(s+1-r)
 let y:= Tk s (v i); let d:ℝ:= a i (f,r)/a i (s,s+1);
 have hu: dist ( (a i (f,r):ℂ) • y) ( (d:ℂ) • y₀) ≤ u * (2*(Real.sqrt (P.poleX s w₀ A0+3)/M^(s+1-s))):= P.daylight_eight j f₀ N₁ x A0 B0 b' v a B N w₀ (Q' s) p u₀ v₀ hv
 have hY:‖y₀‖ ≤ 2*D:= le_trans (P.solo_frame ..) (mul_le_mul_of_nonneg_left ((P.natural_income j f₀ w₀ (Q' s) u₀.le N₁ hg).trans g) (by norm_num)) -- pass
 have hz:0≤u:=by unfold u; positivity
 have hB': ‖ (d:ℂ) • y₀‖ ≤ u*(2*D):=by rw [norm_smul,Complex.norm_real, Real.norm_eq_abs]; apply mul_le_mul _ hY (norm_nonneg _) hz; exact ((P.badgeWage x A0 B0 b' v a B N p u₀ v₀ hv)).1
 have hV: u≤ K'*T'^s:= by unfold u K'; rw [mul_assoc,←pow_succ']; gcongr; omega
 calc _ ≤ ‖( (a i (f,r):ℂ) • y)-( (d:ℂ) • y₀)‖ + ‖(d:ℂ) • y₀‖:= norm_le_norm_sub_add ..
      _ ≤ u*(2*(D/M))+u*(2*D):=by
         apply add_le_add _ hB'; rw [dist_eq_norm, Nat.add_sub_cancel_left, pow_one] at hu; exact hu.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right t h.le) (by norm_num)) hz)
      _ ≤ P' * T'^s:=by
         rw [←mul_add]; refine (mul_le_mul_of_nonneg_right hV (by positivity)).trans ?_
         unfold P'; have he':0 ≤ T'^s:=by positivity
         nlinarith only [he']
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
