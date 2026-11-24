import YM.SU5.SatinWard.Resolution.HighSea
import YM.SU5.SatinWard.Resolution.BiFur
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

namespace Lighthouse
variable (p':0<l)(q':0<r)
local notation "Fx"=> priceX P pT e
include p' q' W Wa K T₁ H' pT e R Ra Lh J
lemma lemTide (u:credential): levy P i x (Fx vo u.val M K u.2 i x U) l r k= levy P i x (Fx vo q M K p i x U) l r k:=by
 let P' := Fx vo u.val M K u.2 i x U; let Q:= Fx vo q M K p i x U; have k(a b:ℝ)(t:0<a)(v:0<b): P' a b= Q a b:=(aliasJ P η q p M U vo i x W K pT e R Wa T₁ H' a₀ x₁ J Lh Ra t v u).symm
 unfold levy; split
 · apply Filter.EventuallyEq.deriv_eq; filter_upwards [Ioo_mem_nhds (show -l< (0:ℝ) from (by linarith)) q'] with i hx; exact k (l+i) (r-i) (by linarith only [hx.1]) (by linarith only [hx.2])
 change (fderiv ℝ (fun z:Vantage=>Σ★ z (P' l r)) 0) _ = _; rw [k _ _ p' q']
open LitCurrent.AuroraX
variable (Vχ:Soul→ₗ[ℝ]ℝ)(Wχ:DerLedger P η M Wa pT e K Vχ) (y:P.Spectrum0 3)
include Wχ y
lemma aliasK (u:credential): pricedPSE P M i x p Wa.tally l r= pricedPSE P M i x u.2 Wa.tally l r:=by
 obtain ⟨v,H⟩:= (AmberEnergy P η M Wa pT e K T₁ H' a₀ x₁ J Lh Ra Vχ Wχ y).exists; obtain ⟨ht,D'⟩:= H true 0; let z₀:= (trueKey P pT e K v).symm (phaseI true 0)
 apply (smul_right_injective ((P.ManyF i x).Op) (show (↑(Vχ z₀):ℂ)≠0 from (Complex.ofReal_ne_zero.mpr ht))) -- lemma mostly syntax.
 dsimp only; unfold z₀
 rw [←D' q p i x l r p' q', ←D' u.val u.2 i x l r p' q']; exact Finset.sum_congr rfl (fun t _=> (lemTide P η q p M t z₀ t i x W K pT e R Wa T₁ H' a₀ x₁ J Lh Ra p' q' u).symm)
#print axioms aliasK
end Lighthouse
end Imperial
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
