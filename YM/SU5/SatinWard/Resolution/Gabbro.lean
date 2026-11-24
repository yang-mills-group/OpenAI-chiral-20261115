import YM.SU5.SatinWard.Resolution.Norias
import YM.SU5.SatinWard.Resolution.Apricity
import YM.SU5.SatinWard.Resolution.Nectar
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
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
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
namespace Internal

open Preparation.Tabletop Harmonic CasaF Signboard Ceremo LitCurrent LitCurrent.Chamber
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
local notation "σ" v:max=> P.macroStep v
local notation "ζ"=> P.jump128
open Motet SoulField Verdance Mezzo SatinWard.Installment
namespace Imperial

/- Lining incidence, with E estimator small-step. Keep exactly compressed-prices
 in this stage. (Adjoint tests have separate qualification through actual lease.) -/
variable {D:ℕ→ℕ}(η:Type)[Fintype η]{v j f0:ℕ}{a b H A φ:ℝ} (q:Cover)(p:ResidualPermit q) (M:P.par.R.L.val%16=1)(k:Axis)(t:Fin 8)
local notation "ρ" => P.par.block.val
local notation "κ" => ζ -- macro
local notation "LH"=> liner k t
local notation "Yt" b:max=> castY t b
local notation "So" t:max=> CLine q k t
local notation "Y" v:max=> home P (So t) v
local notation "Zt" b:max v:max=> home P (So (Yt b)) v
local notation "Pt" t:max=> lifeC q p k t
local notation "p*t"=> lifeC q p k t -- tokens
variable (U:Soul)(vo:Axis)
local notation "VBar" i:max z:max => JpriceApp P (So i) M (Pt i) z vo v
local notation "Top" b:max=> (VBar (Yt b) U)
local notation "UV" z:max=> cloakF P M (Pt t) (substar (v:=v) (j:=ρ) P vo k z) v
local notation "Εw" k:max => Motet.dewy P.par k
local notation "Ε" k:max=> (↑(Εw k):ℂ)
local notation "UR" b:max=> (P.chartAll (liner k t b) (VBar (Yt b) U).F)
variable {s:ℕ} (i:Axis)(x:P.Spectrum0 i)(hp:f0 ≤ v){l r:ℝ}
local notation "tₖ" i:max u:max => P.tock v ((u:Cover) i)
local notation "Q₀"=> home P (So t) v i
local notation "𝔤"=> P.Grips i x v (-(l-Q₀)) (r+Q₀)
local notation "ℛ"=>P.charter i x
local notation "Σ★"=> P.locate i x
local notation "Hσ" A:max => (fun l r=> P.rawBase i x A (l-home P (So t) v i) (r+home P (So t) v i))
local notation "𝒵" b:max => galley P i x v (liner k t b) (Hσ (Top b)) l r
local notation "δ₀"=>moonClock P s
variable {o: Cover}(uv:StretchClock P P.par.block.val s v (CLine q k t) o)
variable (W:HeartClock P f0 H A a b φ P.par.block.val M D η)(ht7:f0 ≤ s)
variable (hl:2*moonClock P s ≤ l)(hr:2*moonClock P s≤ r)
variable (K:P.NightCop)(lι:Wage3){U':Soul}{D':ℕ→ℕ} (Hχ: Velas P η A H f0 v P.par.block.val vo k lι U D')(Hd:Tendsto D' atTop atTop)
-- MotionLap on those projected transfers
local notation "Kℓ" => ShapeLab.leg lι
local notation "Φv" u:max=> annoFace P i x v (Y v) (VBar t u)
local notation "Φℓ" b:max=> Beam P q k t v b
local notation "φ🌸" z:max=> (fun (t:Fin 8)=> annoFace P i x v (home P (So t) v) (VBar t z))
local notation "γb" b:max z:max=> bead P q k t i x v (φ🌸 z) l r b
local notation "μ" => sprintCost P.par.R.L
local notation "Ψε" b:max => bondMonth P η A s b
local instance (priority:=high)(P:Spine)(i:Axis)(x:P.Spectrum0 i) : NormedSpace ℝ (P.ManyF i x).Op:= opRn (P.ManyF i x)
variable (c:s<v) (pT:Tendsto D atTop atTop)(e:Melodic P η A f0 D) (R:Resonant P η A H f0 P.par.block.val)[Nonempty η] {a₁ b₁ φ' :ℝ}(Wa:HeartClock P f0 H A a₁ b₁ φ' P.jump128 M D η)
local notation "Z₀" i:max=> trueKey P pT e K i
local notation "Ψ𝓡" b:max=> (priceX P pT e vo (So b) M K (Pt b) i x)
local notation "Φ" z:max => fun b:Fin 8=> priceX P pT e vo (So b) M K (lifeC q p k b) i x z
local notation "βQ" b:max z:max=> bead P q k t i x v (Φ z) l r b
local notation "δη" z:max=> spindle P q k t i x v (Φ z) l r -- clock frontier
open SatinWard
open OS.Semigroup OS.Semigroup.Marble PSE MarbleFace MezzoBill Velas OS.Semigroup.BasinWake Treaty Choreographer OS.Semigroup.Gear
variable {C' d₀:ℝ} {t' β Wp} {R':P.Register} (T₁:CouncilGrant P R' d₀ C' t' D Wp β) (H': PublicKernel P D Wp) (a₀:Axis)(x₁:P.Spectrum0 a₀)(J:P.Ellis a₀ x₁)
local notation "Lx"=> P.par.R.L
variable (Lh:64≤ P.par.R.L.val) (Ra: Resonant P η A H f0 P.jump128)
local notation "Zc" τ:max=> (poleLens P η K pT e R τ vo k)
private lemma tapered {X:Type*}[NormedAddCommGroup X]{f g:ℕ→ X}{x:X}(p:Tendsto f atTop (𝓝 x)) {C:ℕ→ℝ} (g':Tendsto C atTop (𝓝 0))(h:∀ᶠ i:ℕ in atTop,‖g i-f i‖ ≤ C i) : Tendsto g atTop (𝓝 x) := by
 have t:Tendsto (fun i=>g i-f i) atTop (𝓝 0):=tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) h g'); simpa using t.add p
include p in
lemma cohereB (t':Bool): Tendsto (fun v=> Beam P q k t v t') atTop (𝓝 0):=tendsto_pi_nhds.mpr (fun i=>(tapered (f:=fun _=>0) tendsto_const_nhds (C:=fun i=>3*P.macroStep i) (by simpa using P.macroStep_zero.const_mul (3:ℝ)) (Eventually.of_forall (fun v=> (by rw [sub_zero]; exact Beam_paid (v:=v) P q p k t i t')))))
local notation "Τω" b:max=> priceX P pT e vo (So b) M K (lifeC q p k b) i x U
variable (hl':0<l)(hr':0<r)
include W T₁ J H' Lh R Ra Wa pT K e hl' hr'
theorem gleam_v (t':Bool): Tendsto (fun v=> bead P q k t i x v (Φ U) l r t') atTop (𝓝 ((Τω (Yt t')) l r)):=by
 let Ψ:= (Τω (Yt t')); let p':= (Pt (Yt t')); let F:= currentTemp Ψ l r; let Y':= Ψ l r; let Q(a:Vantage) := Σ★ a Y'; let a(v:ℕ):= Beam P q k t v t'; have e₀:= payStrength P η (So (Yt t')) p' M vo k i x Wa pT e K T₁ H' a₀ x₁ J Lh Ra U hl' hr'; have he:Tendsto a atTop (𝓝 0):= cohereB P q p k t t'; have ht₀:Tendsto Q (𝓝 0) (𝓝 (Q 0)):= e₀.2.1.continuousAt; have ht₁:Tendsto F (𝓝 0) (𝓝 (F 0)):= e₀.2.2.continuousAt; rw [show Q 0=Y' from P.locate_zero ..] at ht₀; rw [show F 0=Y' from (by unfold F Y' currentTemp; rw [add_zero,sub_zero])] at ht₁
 let u:= F ∘ fun v:ℕ=> a v i; have hu:Tendsto u atTop (𝓝 Y'):= ht₁.comp (tendsto_pi_nhds.mp he i); refine tapered (f:= Q ∘ a) (ht₀.comp he) (tendsto_iff_norm_sub_tendsto_zero.mp hu) (Eventually.of_forall fun i'=>?_); change ‖Σ★ (a i') (u i')-Σ★ (a i') Y'‖≤ _; rw [←P.locate_sub,P.locate_cost]
theorem av_plate : Tendsto (fun v=> (Ψ𝓡 t) ((Zc v) U) l r) atTop (𝓝 ((Τω (castY t true)) l r+(Τω (castY t false)) l r)):=by
 let Q(t':Bool):= gleam_v P η q p M k t U vo i x W K pT e R Wa T₁ H' a₀ x₁ J Lh Ra hl' hr' t'; obtain ⟨s,hq,h₁,h₂⟩:= singularVisit P η M Wa l r hl' hr'; obtain ⟨E₀,e₀,T⟩:= crown_year P η M vo W K pT e R Wa; let S:=moonClock P s; have Hp:0<S:= clockP ..; let G:=fun v:ℕ=> (σ v)^(15/8:ℝ); have hg:Tendsto G atTop (𝓝 0):=by unfold G; have i:= Tendsto.rpow P.macroStep_zero (tendsto_const_nhds (x:=(15/8:ℝ))) (Or.inr (by norm_num)); rwa [Real.zero_rpow (by norm_num)] at i
 let f v:= spindle P q k t i x v (Φ U) l r; let E:=fun v:ℕ=> E₀*μ^s*G v*‖U‖; apply tapered (f:=f) ((Q true).add (Q false)) (C:=E) (by simpa [E] using ((hg.const_mul (E₀*μ^s)).mul_const ‖U‖)); filter_upwards [eventually_gt_atTop s] with v y; rw [norm_sub_rev]; exact T v s hq y q p i x k t U l r (by linarith only [h₁,Hp]) (by linarith only [h₂,Hp]) -- S fold issues
omit hl' hr'
end Imperial
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
