import YM.SU5.SatinWard.Resolution.Venue
import YM.SU5.SatinWard.Resolution.NeedleY
import YM.SU5.SatinWard.Resolution.Fez
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
open Preparation.Tabletop ShapeLab SignSlot Emu
open CasaF.Signboard LitCurrent LitCurrent.AuroraX
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
open SoulField Verdance Mezzo SatinWard.Installment
open OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
open MezzoBill
namespace Dovetail

/-! Same regulator convergence including external-lag powers before claiming WP. want uniform-li bound in v for both.T.Ages.Future. This module first finances reflection at stages used. -/
variable {v m:ℕ}(q:Cover)(p:ResidualPermit q)(M:P.par.R.L.val%16=1)(z:Soul)(i:Axis)(x:P.Spectrum0 i)(mu:Axis)
local notation "σ" v:max=> P.macroStep v
local notation "ℛ"=> P.locate i x
local notation "π"=> P.reprise i x
local notation "ℜ"=> P.charter i x
local notation "fee" i:max => home P q i
variable {s f0:ℕ}{Z:ℕ→ℕ}{C H A d c dσ:ℝ}{η:Type}[Fintype η](ρ:Piano P f0 C H A η Z) (q₂:payable P v 2)
local notation "q'"=> flipline i q
local notation "p'" => makesColor q p i
local notation "JV" u:max=> JpriceApp P q M p u mu v
local notation "Ju" u:max=> JpriceApp P (flipline i q) M (makesColor q p i) u mu v
local notation "K$"=> soloV P v q₂ q p pseV
local notation "K'"=> soloV P v q₂ (flipline i q) (makesColor q p i) pseV
local notation "φ♠"=> (↑(colorPay i mu):ℂ)
local notation "Uw"=> (kinWidth P:ℝ)*P.macroStep v
local notation "Uf"=> (choirWidth P:ℝ)*P.macroStep v
local notation "δ₀" v:max=> moonClock P v
variable (p₁:f0 ≤ v)(pHw:Tendsto Z atTop atTop)(W:HeartClock P f0 H A d c dσ P.jump128 M Z η)(e:Melodic P η A f0 Z)(K:P.NightCop)[Nonempty η]{l r:ℝ}
local notation "hℓ"=> home P q v
local notation "PS"=> pricedPSE P M i x p ρ
local notation "Px"=> pricedPSE P M i x (makesColor q p i) ρ
local notation "Tμ" v:max => psScale P ρ v
local notation "Cℓ" F:max => annoFace P i x v (home P q v) F
local notation "Ζℓ" F:max => annoFace P i x v (home P (flipline i q) v) F
local notation "v★" s:max=> trueKey P pHw e K s

namespace Freeport
open Polaris
local notation "root"=> rayPost
-- transparent to future WP bus; house these on this exact ray root. Period stance. Holder in smears at large v preserves this. anchor identity in propositions. x with a₀=3 even when changing rotations; don't choose different v or x.
noncomputable def brass (v:ℕ)(q:Cover) := if h:f0 ≤ v then ((psScale P ρ v:ℝ):ℂ) • RunK P q (ρ.date.stock _ h).2 else 0
noncomputable def cornea (v:ℕ)(t: Axis)(u:Soul)(w: Cover):= RunH P M ((trueKey P pHw e K v) u) v w t
local notation "birthJ" v:max=> cornea P M pHw e K v mu z
local notation "A☆" x:max=> priceX P pHw e mu rayPost M K rayP i x z
local notation "B☆" x:max=> pricedPSE P M i x rayP ρ
local notation "A◇" x:max v:max=> realFreshF P pHw e mu rayPost M K rayP i x z v
local notation "B◇" x:max v:max=> heyC P rayPost rayP i x ρ v
variable (x₁:P.Spectrum0 3)(J:P.Ellis 3 x₁)(y: Bool→ Cover)(T: ℝ)
local notation "U"=> P.advocate 3 x₁ i
local notation "PSΓ"=>P.singleState 3 v x₁
local notation "πV" v:max=> landingY P v y
local notation "δ" v:max=> moonClock P v
local notation "Θt" v:max=> home P rayPost v
local notation "h♠"=> home P rayPost v
noncomputable abbrev choices(h:f0≤v): Bool→ P.Apron:= fun i'=> cond i' (soloV P v (ρ.date.stock _ h).2 rayPost rayP pseV) (JpriceApp P rayPost M rayP ((trueKey P pHw e K v) z) mu v)
local notation "ΖQ" v:max=> (↑(psScale P ρ v):ℂ)
local notation "ν" s:max=> P.macroStep s
variable (f:Polaris.straight i T (landingY P v y))(g:broadV T (landingY P v y))(hu:moonClock P v ≤ T)
abbrev stampY(v:ℕ): Bool→ℂ:=fun b=> if b then (↑(psScale P ρ v):ℂ) else (1:ℂ)
local notation "F"=> choices P M z mu ρ pHw e K p₁ -- order tune
lemma PetalY : P.laysM ∘P.vtile v ∘ y= fun t'=> (landingY P v y) t'-(home P rayPost v):=by funext i; change _=(_+_) - _; abel
include hu
lemma given : Unchained P (choices (v:=v) P M z mu ρ pHw e K p₁) (home P rayPost v) T:=by
 intro b i; have hy:= home_room P rayP v i; cases b; · change _+(JpriceApp P rayPost ..).realWidth P i ≤ _; rw [Hmu_width]; have he:= windMoney P ρ p₁; linarith only [hu,he,hy] -- notation `..` might fail
 change _+(soloV P v (ρ.date.stock _ p₁).2 rayPost rayP pseV).realWidth P i ≤ _; rw [solo_width]; have h:= windowLaw P ρ p₁; linarith only [h,hu,hy]
-- stamps realization marker2. estimator representation.ps.Scale. supply word support later.
local notation "Jour" v:max p:max=> cornea P M pHw e K v mu z p
local notation "Pse" v:max p:max=> brass P ρ v p
lemma GoldY : stampY P ρ v true • P.chartAll (y true) ((choices P M z mu ρ pHw e K p₁) true).F=Pse v (y true):=by rw [brass, dif_pos p₁]; rfl -- proof uses hu accidentally? keep only p₁ omit
omit hu in
lemma plex (v:ℕ)(x:P.Spectrum0 i)(h:f0≤v) : stampY P ρ v true • annoFace P i x v (home P rayPost v) ((choices P M z mu ρ pHw e K h) true) = heyC P rayPost rayP i x ρ v:=by
 funext l r; let p:=(ρ.date.stock v h).2; rw [hey_info P rayPost rayP i x ρ p h]; rfl
local notation "Θ"=> (landingY P v y)
local notation "Wf"=> Jour v (y false)
local notation "Wβ"=> Pse v (y true)
include f g hu J
structure Jewel : Prop where
 pairs: PSΓ (Wf*Wβ)= Cruise P i (P.advocate 3 x₁ i) (realFreshF P pHw e mu rayPost M K rayP i (P.advocate 3 x₁ i) z v) (heyC P rayPost rayP i (P.advocate 3 x₁ i) ρ v) (landingY P v y) T
 sectorJ: PSΓ (Wf)= SingleF P i U (realFreshF P pHw e mu rayPost M K rayP i (P.advocate 3 x₁ i) z v) ((landingY P v y) false) T
 sectorP: PSΓ (Wβ)= SingleF P i U (heyC P rayPost rayP i (P.advocate 3 x₁ i) ρ v) ((landingY P v y) true) T
 -- real width and plenum expenses recorded elsewhere
#check Jewel
include p₁
lemma earned : Jewel (v:=v) P M z i mu ρ pHw e K x₁ y T:=by
 let A:= choices P M z mu ρ pHw e K p₁; let c:= stampY P ρ v
 have h(t:Bool):(A t).s=v:=by cases t<;> rfl
 let j:=markerPair P (landingY P v y) T i A (home P rayPost v) c h y (PetalY P y) (given P M z mu ρ p₁ pHw e K T hu) f g 3 x₁ J; have u(t:Bool):=(markerOne P (landingY P v y) T i A (home P rayPost v) c t h y (PetalY P y) 3 x₁ J)
 let gX(t:Bool): P.Test:= c t • P.chartAll (y t) (A t).F; let Φ(t:Bool):= c t • annoFace P i (P.advocate 3 x₁ i) (A t).s (home P rayPost v) (A t)
 have e₀:gX false=Wf:=one_smul ..; have t₀:gX true=Wβ:= GoldY P M z mu ρ p₁ pHw e K y T hu -- order; might need p₁ in given
 have h₀:Φ false=A◇ U v:=one_smul ..; have y₀:Φ true=B◇ U v:=plex P M z i mu ρ pHw e K v _ _
 constructor
 · rw [←e₀,←t₀, ←h₀, ←y₀]; exact j.symm
 · rw [←e₀, ←h₀]; exact u false
 rw [←t₀, ←y₀]; exact u true
#print axioms earned
end Freeport
end Dovetail
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
