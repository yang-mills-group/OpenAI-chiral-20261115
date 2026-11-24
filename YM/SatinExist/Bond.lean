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
include B
lemma ant_pass (i:ℕ):∃ c w,Workforce A0 B0 f (v i) P c (a i) w:=let ⟨_,V⟩:= B.station; V.cruise i
lemma ant_climbs: Tendsto v atTop atTop:=let ⟨_,V⟩:= B.station; V.fast.tendsto_atTop
lemma ant_above (i:ℕ):r ≤ v i := let ⟨_,V⟩:= B.station; V.up i
variable (N:s≥f)(w:ℕ)(V:Watchdesk (f:=s) P j X w)(p:f<r)
local notation "G" i:max=> P.spotDuty j X w V x i
local notation "F" i:max=> (((a i (f,r)):ℂ) • G (v i))
local notation "R" i:max t:max=> a i (s,t)
local notation "μ" t:max=> Real.sqrt (poleX P s w A0+3) / (zoomM P.par.R.L^(t-s))
local notation "D" i:max t:max=> a i (f,r) / (R i t)
local notation "η" t:max=> 4 * zoomC P.par.R.L^(t-r)
include p N
lemma badgeWage (z:s<t)(q:r ≤ t)(e:t≤v i): |(a i (f,r)) / (R i t)| ≤ 4*zoomC P.par.R.L^(t-r) ∧ D i t * R i t = a₁ i:=by
 obtain ⟨c,w,h⟩:= ant_pass P x A0 B0 b' v a B i
 have ht:= h.career _ _ (show chargeSpan f (v i) (f,r) from ⟨le_rfl,p,le_trans q e⟩) (show chargeSpan f (v i) (s,t) from ⟨N,z,e⟩) q
 let f:=zoomC P.par.R.L
 by_cases hk:a i (s,t)=0
 · change |_/_| ≤ 4*f^(t-r) ∧ _; simp only [Prod.mk.eta] at ht; rw [hk] at ht; rw [abs_zero,mul_zero] at ht; simp only [hk,mul_zero,div_zero,abs_zero]; constructor
   · have hv:1≤ f:=zoomC_p _; positivity
   exact Eq.symm (abs_eq_zero.mp (le_antisymm ht (abs_nonneg _)))
 rw [abs_div]; exact ⟨(div_le_iff₀ (abs_pos.mpr hk)).2 ht,div_mul_cancel₀ _ hk⟩
include V N₁
lemma daylight_eight (z:s<t)(q:r ≤ t)(e:t≤v i): dist (F i) (( (D i t :ℝ):ℂ) • (G t)) ≤ (η t) * (2* (μ t)) :=by
 obtain ⟨c,w',h⟩:= ant_pass P x A0 B0 b' v a B i; let Q':= h.plans _ (show chargeSpan f (v i) (s,t) from ⟨N,z,e⟩)
 obtain ⟨hp,hT⟩:= badgeWage P x A0 B0 b' v a B N p z q e
 let z':ℂ:=↑(D i t); let ψ:ℂ:=↑(R i t); let b₁:=(G t); let b₂:=(G (v i))
 have hi:(F i)=z' • ψ • b₂:=by rw [smul_smul]; unfold ψ z'; rw [←Complex.ofReal_mul,hT]
 rw [hi]; change dist _ (z' • b₁) ≤ _; rw [dist_eq_norm,←smul_sub,norm_smul]; change ‖z'‖*‖ _‖≤ _
 have hB:0 ≤ η t:= by have he:=zoomC_p P.par.R.L; positivity
 exact mul_le_mul (by unfold z'; simpa only [Complex.norm_real,Real.norm_eq_abs] using hp) (le_trans (wind_le P j X w V x (s:=t) (v:=v i) ψ) (mul_le_mul_of_nonneg_left (P.path_paid_weight j X w V z.le e Q' N₁) (by norm_num))) (norm_nonneg _) hB
variable (h:Aglomerate f r a)
include h
lemma wear_winner : ∃ y:(P.ColorHil j (P.advocate 3 x j)).Op,Tendsto (fun i=> F i) atTop (𝓝 y):=by
 let E:= Real.sqrt (poleX P s w A0+3); let L₁:= zoomM P.par.R.L
 have he: 0 < L₁:= zoomM_p _; have ht:L₁ /8 = zoomC P.par.R.L:=by unfold L₁ zoomC zoomM; ring
 have hx(t):4*zoomC P.par.R.L^t * (2*E/L₁^(t-s))= 8*E*L₁^s*(1/8)^t ∨ t < s:=by
    rcases le_or_gt s t with u|u; swap; · exact Or.inr u
    refine Or.inl ?_; have hf:L₁^s* L₁^(t-s)=L₁^t:=by rw [←pow_add]; congr 1; omega
    rw [←ht,div_pow,div_pow (1:ℝ),←hf]; field_simp; try ring -- tune
 have hz:= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num:(0:ℝ)≤1/8) (by norm_num:(1/8:ℝ) <1); let M:= 8*E*L₁^s; have hf:Tendsto (fun t:ℕ=> M*(1/8)^t) atTop (𝓝 0):=by simpa only [mul_zero] using hz.const_mul M
 let Le(i:ℕ):= F i; refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.mpr ?_)
 intro ε e; obtain ⟨t,a',b,c⟩:= ((eventually_ge_atTop r).and ((eventually_gt_atTop s).and (hf.eventually (gt_mem_nhds (show 0 < ε/4 from by positivity))))).exists
 have hp: η t * (2*(μ t)) < ε/4:=by
   apply lt_of_le_of_lt _ (show M*(1/8)^t < _ from c); unfold M; rw [←(hx t).resolve_right b.asymm]; rw [mul_div_assoc]; -- tune direction
   have hq:0≤2* (μ t):=by have hv:=Real.sqrt_nonneg (poleX P s w A0+3); change 0≤ 2*(E/L₁^ _); positivity
   apply mul_le_mul_of_nonneg_right _ hq; gcongr; exact zoomC_p _; omega
 obtain ⟨y,u⟩:= h.caught (s,t) N b a'; let T':= (y:ℂ) • (G t); let B'(i:ℕ):=( (D i t:ℝ):ℂ) • G t; have hh:Tendsto B' atTop (𝓝 T'):= (Complex.continuous_ofReal.continuousAt.tendsto.comp u).smul_const (G t)
 obtain ⟨n,xq⟩:= eventually_atTop.mp (( (P.ant_climbs _ _ _ _ _ _ B).eventually_ge_atTop t).and (Metric.tendsto_nhds.mp hh (ε/4) (by positivity)))
 have hr(i:ℕ)(p1:n ≤ i): dist (Le i) T' < ε/2:=by
    obtain ⟨c,hg⟩:=xq i p1
    exact lt_of_le_of_lt (dist_triangle _ (B' i) _) (by linarith only [show dist (Le i) (B' i)< ε/4 from lt_of_le_of_lt (P.daylight_eight j X N₁ x A0 B0 b' v a B N w V p b a' c) hp, (show dist (B' i) T'< ε/4 from hg)]) -- .. pass
 refine ⟨n,fun i hi=>lt_of_le_of_lt (dist_triangle_right (Le i) (Le n) T') (by linarith only [hr i hi,hr n le_rfl])⟩
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
