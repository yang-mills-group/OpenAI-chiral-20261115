import YM.SU5.SatinWard.Resolution.Diva
import YM.SU5.SatinWard.Resolution.RunLens
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
local notation "Y"=> P.run
open Worth Pays BProof Aria Casting MacroGrid Selected Reconstruction.Atlas
local notation "σ" v:max=> P.macroStep v
local notation "ζ"=> P.jump128
variable {D:ℕ→ℕ}(η:Type)[Fintype η]{v j f0:ℕ}{a b H A φ:ℝ} {Z:Visit→ Cover → Family P.calibration} {χ:Division}{d:PitchZ}
variable (E:Ceremo P η v P.jump128 f0 a b φ H A χ D Z d)(q:Cover)(p:ResidualPermit q) (M:P.par.R.L.val%16=1)
local notation "Ξ" u:max=> cloakF P M p (E.earnedZ P η u) v
local notation "Δ"=> cloakF P M p (logStarCore P η E) v
local notation "X" v:max=> hat P.par.R.L P.par.x v
local notation "Yw" v:max=> (hueW P.par.R.L (X v))
local notation "h★" v:max=> (↑(Yw v):ℂ)
local notation "h△" v:max=>(↑(qHull P.par.R.L (X v)):ℂ)
local notation "h❖" v:max=>(↑(jHull P.par.R.L (X v)):ℂ)
local notation "TΔ" i:max=> Ξ (some i)
open Motet SoulField Verdance Mezzo SatinWard.Installment
variable (U:Soul)(vo ti:Axis)
local notation "Vx" z:max => JpriceApp P q M p z vo v
local notation "UV" z:max=> cloakF P M p (substar (v:=v) (j:=ζ) P vo ti z) v
local notation "Εw" k:max => Motet.dewy P.par k
local notation "Ε" k:max=> (↑(Εw k):ℂ)
local notation "UR" b:max=> (P.chartAll (incMove ti b) (Vx U).F)
noncomputable abbrev currentFront (U:Soul):P.Test:=(UV U).F
lemma stocked_front : currentFront (v:=v) P q p M vo ti U= Ε v • (UR true+UR false):=by
 let w:= tauprint P M p; have he(b:Bool): UR b= chapterFoot P (letterShape (J:=P.calibration) (Λ:=P.par) vo v U) (w+pmZ ζ ti b):=by
    change P.chartAll _ (chapterFoot P (letterShape (J:=P.calibration) (Λ:=P.par) vo v U) w)=_; rw [calendar_moves,show ζ • (incMove ti b)= pmZ ζ ti b from ?_]; unfold incMove pmZ; cases b<;>simp
 rw [he,he]; rfl
variable {s:ℕ}
variable (i:Axis)(x:P.Spectrum0 i)(hp:f0 ≤ v){l r:ℝ}
local notation "tₖ" i:max u:max => P.tock v ((u:Cover) i)
local notation "Q₀"=> home P q v i
local notation "𝔤"=> P.Grips i x v (-(l-Q₀)) (r+Q₀)
local notation "ℛ"=>P.charter i x
local notation "Hσ" A:max => (fun l r=> P.rawBase i x A (l-home P q v i) (r+home P q v i))
local notation "𝒵" b:max => galley P i x v (incMove ti b) (Hσ (Vx U)) l r
local notation "δ₀"=>moonClock P s
variable {o: Cover}(uv:StretchClock P P.jump128 s v q o)
variable (W:HeartClock P f0 H A a b φ P.jump128 M D η)(ht7:f0 ≤ s)
variable (hl:2*moonClock P s ≤ l)(hr:2*moonClock P s≤ r)
include uv
lemma hor_3 : 3*P.macroStep v ≤ moonClock P s :=by linarith only [restTick P uv.ph,uv.enough,P.macroStep_pos v]
include hl hr
-- keep clues α coherence at physical operator.
lemma circadian : (Hσ (UV U)) l r= Ε v • (𝒵 true + 𝒵 false):=by
 have ht:=abs_le.mp (home_room P p v i); let d:=moonClock P s; let Θ:3*P.macroStep v≤ d:= hor_3 P q uv
 have h₁ :𝔤 (UV U).F ((Hσ (UV U)) l r):=by
    have hz: (UV U).realWidth P i≤ d:= by rw [real_cloak]; linarith only [clockP P s,uv.fit (show 2*P.jump128≤rentWidth P P.jump128 v from (by unfold rentWidth; omega))]
    exact P.grasp_fixed i x (UV U) (a:=l-Q₀) (by linarith only [Θ,hz,hl,P.macroStep_pos v, ht.2]) (b:=r+Q₀) (by linarith only [Θ,hz,hr,P.macroStep_pos v, ht.1])
 let h₂(b:Bool) : 𝔤 (UR b) (𝒵 b):=by
    have hq:(Vx U).realWidth P i≤ d:= by unfold JpriceApp; rw [real_cloak]; linarith only [clockP P s,uv.fit (Nat.zero_le _)]
    have t:=abs_le.mp (inc_wallet (v:=v) P i ti b); refine gripsH (l:=l) (r:=r) P i x q (Vx U) (incMove ti b) (h:=rfl) ?_ ?_ -- notation works? binders implicit terms all goals below
    all_goals first | rfl | linarith only [t.1,t.2,Θ,hq,hl,hr,ht.2,ht.1,P.macroStep_pos v]
 apply h₁.unique; change 𝔤 (currentFront (v:=v) P q p M vo ti U) _; rw [stocked_front]; exact ((h₂ true).add (h₂ false)).smul _ -- `Vel.`
local notation "φ🌸" z:max => charm P q M vo p i x hp z
noncomputable abbrev arity(Ψ:P.RawLag i x)(u:ℕ)(l r:ℝ):= galley P i x u (incMove ti true) Ψ l r+ galley P i x u (incMove ti false) Ψ l r
local notation "𝒟v" x:max=> arity P ti i x -- x metav argument!
#check @arity
lemma coMotion : frontPrice P i q M p x hp (substar (v:=v) (j:=ζ) P vo ti U) l r= Ε v • arity P ti i x (φ🌸 U) v l r:=by
 change ℛ (chair P M q hp) ((Hσ (UV U)) l r)= _ ; rw [circadian P q p M U vo ti i x uv hl hr, P.charter_smul,P.charter_add]; let C:=chair P M q hp; congr 1
 have he(b:Bool): ℛ C (𝒵 b) = galley P i x v (incMove ti b) (φ🌸 U) l r:=by
    unfold galley charm lined; simp only; rw [P.charter_sum,P.charter_sum]; unfold C; rw [add_comm (P.vtile _ _)] ; rfl
 exact congrArg₂ (·+·) (he true) (he false)
omit uv
include W ht7 hl hr
variable {d':ℕ→ℕ}
variable (k:P.NightCop)
local notation "μ"=> sprintCost P.par.R.L
open Velas
variable (lι:Wage3)
local notation "Kℓ" => ShapeLab.leg lι
include k in
lemma motionLap (u:s<v)(t:Tendsto d' atTop atTop)(vV: Velas P η A H f0 v P.jump128 vo ti lι U d'): ‖ Ε v • arity P ti i x (φ🌸 Kℓ) v l r- charm P q M vo p i x hp U l r‖≤ θx P η s v A H vo:=by
 obtain ⟨o,h⟩:= W.tally.poses s ht7 q p; let uv:= W.stamps s v q o ht7 u.le p h; obtain ⟨x',z⟩:= placement_m P M s v o
 rw [←coMotion P q p M Kℓ vo ti i x hp uv hl hr]
 let f:=clockP P s; exact clock_x P o x' z t k i u ht7 W.living.1 W.living.2.1 η q M p x uv (by linarith only [f,hl]) (by linarith only [f,hr]) hp vo ti lι vV (healthy P M W ht7) -- may ω placeholders w,v0
#print axioms motionLap
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
