import YM.SU5.SatinWard.Resolution.Hoods
import YM.SU5.SatinWard.Resolution.Chili
import YM.SU5.SatinWard.Resolution.Fez
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
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
open SatinWard
open Worth Pays BProof Aria Casting MacroGrid Selected OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
open SatinWard.Installment Internal Dovetail
open _root_.GarnetAct.Cut Curtain
open _root_.YM.MacroSix.Grid
namespace Polaris
/-! Geometry for the mass-one tests and their stencil corners. Uses stricter housing than just two-point. -/
namespace Rampart
local notation "gΦ"=> Vantage
local notation "ψΔ" v:max=> (P.macroStep v)
local notation "W★" s:max=> moonClock P s
-- viewpoint-t enlarged Cost.Still use P.Apron and every budget inside Ep qualifications.
def Deck (t:ℝ)(p:skit)(w:ℝ): Prop:= ∀ x∈ Metric.closedBall (p false) w,∀ y∈ Metric.closedBall (p true) w, Chili.Coast t (frontage x y)
variable (F G:Curtain)
-- frame address at height.Named with actual 🏕 ~Anchor stances. We need t.S. issue fits. row. Cover.Advance. Tag Π etc.
abbrev orderPost(v:ℕ): Vantage→ Cover := Curtain.shifter (P.macroStep v)
-- PP knows pose.Room pins relation.Co.Key.A harmony. use $apt.har$.
abbrev station(v:ℕ)(y:Cover): Vantage:= home P rayPost v+ P.laysM (P.vtile v y)
local notation "μ"=> F.ppm
local notation "ν"=> G.ppm
local notation "Ω"=> F.ppm.prod G.ppm
lemma gaugeRobot(v:ℕ)(x:Cover): P.laysM (P.vtile v x)= YM.MacroSix.Grid.place (P.macroStep v) x:=by funext i; change P.tock v (x i) =_; rw [P.tock_price]; rfl
lemma stage_after (v:ℕ): ‖home P rayPost v‖ ≤ ψΔ v:= (pi_norm_le_iff_of_nonneg (P.macroStep_pos _).le).2 (fun i=> by rw [Real.norm_eq_abs]; exact home_room P rayP v i) -- implicit proof p might need
lemma approaches (v:ℕ)(x:Vantage): dist (P.laysM (P.vtile v (orderPost P v x))) x≤ P.macroStep v:=by rw [gaugeRobot,dist_comm]; exact distance_tag _ (P.macroStep_pos _) x
lemma seeks (v:ℕ)(x:Vantage) : dist (station P v (orderPost P v x)) x≤2*P.macroStep v:=by
 let y:= P.laysM (P.vtile v (orderPost P v x)); refine (dist_triangle _ y _).trans (?_); change dist (home P rayPost v+y) y+dist y x≤ _; rw [dist_eq_norm, add_sub_cancel_right]; exact (add_le_add (stage_after P v) (approaches P v x)).trans_eq (two_mul _).symm
abbrev twoPoint (x y:Cover): Bool→ Cover:= fun b=> cond b y x
lemma lands (x y:Cover)(v:ℕ): landingY P v (twoPoint x y)= frontage (station P v x) (station P v y):=by funext b; cases b <;> rfl
abbrev kiosk (v:ℕ)(x y:Vantage):= twoPoint (orderPost P v x) (orderPost P v y)
lemma revolving (x y:Vantage): Tendsto (fun v=> landingY P v (kiosk P v x y)) atTop (𝓝 (frontage x y)):=by
 have h(x:Vantage): Tendsto (fun v=>station P v (orderPost P v x)) atTop (𝓝 x):=by rw [tendsto_iff_dist_tendsto_zero]; refine squeeze_zero (fun _=>dist_nonneg) (fun v=>seeks P v x) ?_; simpa using P.macroStep_zero.const_mul (2:ℝ)
 apply tendsto_pi_nhds.mpr; intro i; cases i; exact h x; exact h y
-- *all* purchases Housing. tilted at position centers may not be exactly wall; Epoch suits holds strict.Sharp.Support.Price. Provide Economy support also later. choose r,C basin and call all axes x picks.Widget.T.F.
variable (t:ℝ)(p:skit)(w:ℝ)(vW: Deck t p w)(hw:0<w)
abbrev Seats (n:ℕ)(C:Curtain):= Curtain.kinSet C (P.macroStep n) (P.macroStep_pos _)
local notation "uF" v:max=> Seats P v F
local notation "uG" v:max=> Seats P v G
lemma along_up (v:ℕ)(x:Vantage)(w r:ℝ)(d:ℝ)(h:F.boxS⊆ closedBall x w)(hu:2*ψΔ v + d+w≤ r)(u:Cover)(b:u∈Seats P v F)(y:Vantage) (e:y∈ closedBall (station P v u) d) : y∈ closedBall x r:=by
 obtain ⟨x',h',t⟩:= (Curtain.picked ..).mp b; subst u; refine (dist_triangle y x' x).trans (?_) -- goal expects y∈; Lean defeq ≤.
 have ht:=seeks P v x'; have hd:dist y x' ≤ d+2*ψΔ v:= (dist_triangle y _ x').trans (add_le_add e ht); exact le_trans (add_le_add hd (show dist x' x≤w from h h')) (by linarith only [hu])
-- from deck decide gap.He enough.
lemma anchorsUp (v:ℕ)(x:Vantage)(w r:ℝ)(h:F.boxS⊆ closedBall x w)(hu:2*ψΔ v +w≤ r)(u:Cover)(b:u∈Seats P v F): station P v u∈closedBall x r:=by refine along_up P F v x w r 0 h (by linarith only [hu]) u b _ ?_; simp
-- use property with measurements anywhere in F.boxS×G.boxS.Access.
structure Supported (C D:Curtain)(p:skit)(w:ℝ):Prop where
 basis₀ : C.boxS ⊆ closedBall (p false) w
 basis₁ : D.boxS ⊆ closedBall (p true) w
include vW hw
lemma fullTime (g:Supported F G p (w/2)) : ∀ᶠ n:ℕ in atTop,∀ x∈ Seats P n F,∀ y∈Seats P n G, Chili.Coast t (landingY P n (twoPoint x y)):=by
 have h:Tendsto (fun n=> 2*P.macroStep n+w/2) atTop (𝓝 (w/2)):= by simpa using (P.macroStep_zero.const_mul (2:ℝ)).add_const (w/2)
 filter_upwards [h.eventually (ge_mem_nhds (half_lt_self hw))] with i h x hx y hy; rw [lands]; exact vW _ (anchorsUp P F i _ _ _ g.basis₀ h x hx) _ (anchorsUp P G i _ _ _ g.basis₁ h y hy)
-- interior_margin Credit.L.Point.Compute. Use P.pinFoot and P.asked_at survival even after higher-price grid onset.Measure.Role.
#print axioms fullTime
end Rampart
end Polaris
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
