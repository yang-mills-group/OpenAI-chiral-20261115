import SatinThinPerch
import SatinThinReality
import SatinThinIron
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
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "κ"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ
local notation "B"=> P.basePlay x f r
local notation "K" f:max r:max=> P.megaK f r
local notation "W'" => P.tallWorth r
local notation "q!" i:max s:max=> P.runP f r i s
local notation "p!" i:max s:max=> P.meshPose r (q! i s)
local notation "O"=> P.charmF
local notation "oQ"=> opposeQ 3
local notation "oR"=> opposeR 3
open Regis.Circuit SatinJets
local notation "r!" f:max r:max=> ((P.rewardK f r):ℝ)
local notation "Cσ"=> Yoke.canonWeight
local notation "H!" i:max b:max=> P.strollQ x f r i b
local notation "Hu" i:max b:max=> P.strollV x f r i b
local notation "RΔ"=>P.invoiceV x f r r 1
abbrev lantern(f r:ℕ) : ℝ:= P.glareF f r 1 1 0 x + ∑ a:Seven, ∑ k:Seven, P.glareF f r (SatinJets.stride k) (SatinJets.stride a) P.charmF x
lemma lantern_cont (f r:ℕ) : Continuous (fun x:P.Spectrum0 3=> P.lantern x f r):= Continuous.add (P.mistake_live ..) (continuous_finsetSum _ fun _ _=> continuous_finsetSum _ fun _ _=> P.mistake_live ..)
lemma lantern_available (f r:ℕ): P.glareF f r 1 1 0 x≤ P.lantern x f r ∧ ∀ s t:Seven,P.glareF f r (SatinJets.stride t) (SatinJets.stride s) P.charmF x≤ P.lantern x f r:= by
 let F(k v a:ℕ):= P.glareF f r k v a x; have hx(i k v:ℕ): 0 ≤ F i k v:= norm_nonneg _; let Z(i j:Seven):= F (SatinJets.stride j) (SatinJets.stride i) (O); have hp(i):0≤ ∑ j,Z i j:=Finset.sum_nonneg fun i _=>hx ..; refine ⟨le_add_of_nonneg_right (sum_nonneg fun i _=> hp i),fun s t=>?_⟩; refine le_trans ?_ (le_add_of_nonneg_left (hx 1 1 0)); exact (single_le_sum (f:= Z s) (fun i _=> hx ..) (mem_univ t)).trans (single_le_sum (f:=fun i=>∑ j,Z i j) (fun i _=>hp i) (mem_univ s))

local notation "Φ"=> P.Spectrum0 3
local notation "μ'"=> P.pillars 3
private lemma genre {x:Φ→ℝ} (h:Continuous x):Integrable x μ':= h.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma lantern_go {C:ℝ}(Z:∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k:ℕ,(P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → Yoke.ShelterCost C P.run s i k) : Tendsto (fun r=>∫ x,P.lantern x (P.pointEra r) r∂(P.pillars 3)) atTop (𝓝 0):=by
 let F (f r:ℕ):Φ→ ℝ:= P.glareF f r 1 1 0; let g1(t s:Seven)(f r:ℕ):Φ→ ℝ:= P.glareF f r (SatinJets.stride s) (SatinJets.stride t) O; let Hb(t:Seven)(f r:ℕ)(x:Φ):=∑ s:Seven,(g1 t s f r x)
 have h(t s:Seven)(f r:ℕ) : Continuous (g1 t s f r):=P.mistake_live ..; have ht(f r:ℕ):Continuous (F f r):=P.mistake_live ..; have hn(t:Seven)(f r:ℕ):Continuous (Hb t f r):=continuous_finsetSum _ fun j _=> h t j f r -- tune
 have he (r:ℕ): (∫ x,P.lantern x (P.pointEra r) r ∂μ')= (∫ x,F (P.pointEra r) r x∂μ')+∑ i:Seven,∑ j:Seven,∫ x,g1 i j (P.pointEra r) r x ∂ μ':=by
    unfold lantern; let f:=P.pointEra r; rw [integral_add (f:=F f r) (g:=fun x=>∑ i:Seven,Hb i f r x) (P.genre (ht f r)) (P.genre (continuous_finsetSum _ fun i _=>hn i f r)),integral_finsetSum _ (fun i _=>P.genre (hn i f r))]; congr 1; refine sum_congr rfl fun i v=>?_ ; exact integral_finsetSum _ (fun j _=> P.genre (h i j f r))
 simp_rw [he]; have hu(i): Tendsto (fun r=>∑ j:Seven,∫ x, g1 i j (P.pointEra r) r x ∂ μ') atTop (𝓝 ((∑ _:Seven,(0:ℝ)))):= tendsto_finsetSum _ (fun j _=>P.glare_go (SatinJets.stride j) (SatinJets.stride i) O (Nat.add_pos_left (stride_p _) _) Z); simp only [sum_const_zero] at hu; have hv: Tendsto (fun r=>∑ i:Seven,∑ j:Seven,∫ x,g1 i j (P.pointEra r) r x∂μ') atTop (𝓝 (∑ _:Seven,(0:ℝ))) := tendsto_finsetSum _ (fun i _=> hu i); simp only [sum_const_zero] at hv; have hs:Tendsto (fun r=>∫ x,F (P.pointEra r) r x∂μ') atTop (𝓝 0):= P.glare_go 1 1 0 (by decide) Z; simpa only [zero_add] using hs.add hv -- tune
-- normalized gap P
abbrev census (f:ℕ)(r:ℕ)(v:ℕ)(u:r ≤ v)(g:f ≤ r)(z:ℝ)(x:P.Spectrum0 3) := ‖P.stateVox 3 x v (P.cameo 3 (P.baseRoot f) z g u (P.lent_anchor f))‖^2
def reliableP (f r:ℕ)(b:ℝ): Prop:=∀ y:P.ManyF 3 (P.advocate 3 x 3), dist y (P.invoiceV x f r r 1) ≤ b→ LinearIndependent ℂ (fun i: SatinJets.Seven=> P.epochW x f r i y)
lemma min_positive : 0< min7:= div_pos focus_positive (by norm_num)
lemma reliable_pp {b:ℝ}(u:P.reached f r)(p:0<P.tallWorth r)(hx: P.lantern x f r ≤ min7/4)(J:P.Ellis 3 x)(t:marginD (max7+min7+1) b min7)(q:0≤b): P.reliableP x f r b:=by
 let Z:=P.invoiceV x f r r 1; let A:= P.epochW x f r; let W0:= Γ (P.launchPad r O); have hg:= min_positive; have h0:= P.lantern_available x f r; intro y v; refine stable_plan (G) A W0 (fun v=>P.cart_norm ..) (fun i:Seven=>(Η).shrinks _) q Z y (P.base_weight x u p (h0.1.trans hx)) (fun i j=>?_) (P.dBase_interval r).1 hg t v
 have e':= (h0.2 i j).trans hx; change ‖ _ * inner ℂ (W0 (A i Z)) (A j Z)-_‖≤_; unfold W0 A Z; rw [P.together_epoch x u,P.together_pos x u,← P.glare_seven x i j J u p]; exact e'
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.lantern_go
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.reliable_pp
