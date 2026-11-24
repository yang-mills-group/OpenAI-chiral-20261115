import YM.SU5.SatinWard.Resolution.HaloLens
import YM.SU5.SatinWard.Resolution.SandGlass
import YM.SU5.SatinWard.Resolution.TunicW
import YM.SU5.SatinWard.Resolution.Journal
import YM.SU5.SatinWard.Resolution.Waive
import YM.SU5.SatinWard.Resolution.Belfry
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 75000
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
local notation "L★"=> P.par.R.L
local notation "B$"=> P.calibration
variable {v j f0 s w:ℕ}(p x:Cover)(wp:nodeC x=P.clockPlate s v p){a b A c φ H:ℝ}{F T: Family P.calibration}{S S': Finset Cover}
local notation "U$"=> pavilion (P.clockPlate s v p) (rentWidth P j v)
variable {G R:ℕ→Family P.calibration}{D:ℕ→ℕ}(q:Tendsto D atTop atTop)(e:BQueue S G F)(e':BQueue S' R T)
local notation "ι₀"=> Wage3
local notation "iv" i:max=> P.nomadic (D i)
local notation "kv" i:max=> P.engine (D i)
local notation "Mp" i:max=> side P.run (P.nomadic (D i)) v
variable (hb:Almanac P s w p) (hz: Closeted P j p s v w) (pc:S ⊆ pavilion (P.clockPlate s v p) (rentWidth P j v)) (pc':S' ⊆ pavilion (P.clockPlate s v p) (rentWidth P j v)) (k:P.NightCop) (i:Axis)
local notation "κ"=> sprintCost P.par.R.L
open Worth Pays BProof Aria Casting MacroGrid
open Selected Reconstruction.Atlas
open CasaF
variable (D₀:Cover) (M:P.par.R.L.val % 16 =1) (A':P.Apron)(qa:ResidualPermit D₀) (L:P.Spectrum0 i)
local notation "Home" s:max=> homeTag P s
noncomputable abbrev blankRent (P:Spine)(A:P.Apron)(v s:ℕ)(j:Axis):Prop:= A.s=v∧ 16*A.realWidth P j≤ moonClock P s
structure StretchClock (P:Spine)(j s v:ℕ)(o p:Cover):Prop where
    located : ShowField P s (homeTag P o) p
    enough : 16* P.macroStep s≤ moonClock P s
    fit {t:ℕ}: t≤ rentWidth P j v→ (16*(deltaWing P t:ℝ))*P.macroStep v≤ moonClock P s
    ph : s≤v
    art : Closeted P j p s v (moonSpan P s)
variable (uv:StretchClock P j s v D₀ p)
variable (Q:P.Card i v (P.reachLeaf s v (moonSpan P s))) (he:P.voxTest i v Q.val∈enclave P.calibration)
local notation "δ"=> moonClock P s
local notation "σ"=> P.physicalEnergy i L
local notation "ℛ"=> P.charter i L
local notation "HC"=> P.reachLeaf s v (moonSpan P s)
local notation "Φ"=>geoAt P s (nodeC p)
local notation "T"=> (geoAt P s (nodeC p)) i
local notation "τ" v:max=>P.macroStep v
local notation "ν" v:max=> home P D₀ v i
variable (h:blankRent P A' v s i)
include qa uv in
lemma blanks (C:ℝ) (p':16*C≤ δ) : C+ν v≤ T∧ C-ν v≤ δ-T ∧ T ≤ δ ∧ δ-T ≤ δ:=by
 have p:=time_pose P p i qa uv.located; have h₁:= abs_le.mp (home_room P qa s i); have h₂:= abs_le.mp (home_room P qa v i); have tv:= restTick P uv.ph; refine ⟨?_,?_,?_,?_⟩<;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2,p,tv,uv.enough,p']
noncomputable def hangs_it : Prop:= ∀ (t:Cover), P.clockPlate s v p=homeTag P D₀+P.sidesPerTick • t→ P.chartAll t A'.F=P.voxTest i v Q.val
variable {u' d' t r:ℝ} {f:ℕ} (hp:f ≤ v)
local notation "Ω"=> lined P M i L f D₀ hp
local notation "r$" i:max x:max=> A'.realWidth P i + (home P D₀ x i)
lemma rates (i':P.VMark)(U:P.VMark)(ha:P.laysM i'=P.laysM U-P.laysM (chair P M D₀ hp))(l r:ℝ):
 ℛ i' (Ω A' l r)= ℛ U ((A').dye P i L (l-home P D₀ A'.s i) (r+home P D₀ A'.s i)):=by
 unfold lined; rw [P.charter_sum, show i'+chair P M D₀ hp=U from lays_uniq _ (by rw [P.lays_add,ha,sub_add_cancel])]; rfl
include h
lemma recall_shade (p':hangs_it P p i D₀ A' Q)(qa:ResidualPermit D₀)(z:P.VMark)(u: P.laysM z=geoAt P s (nodeC p)-home P D₀ f): ℛ z (lined P M i L f D₀ hp A' T (moonClock P s-T)) = letRoom P p uv.located.cost i Q he L:=by
 obtain ⟨t,r⟩:=position_ticks P p M D₀ uv.ph uv.located; let C:= T; let S:= δ-T; let d:=moonClock P s; let n:= T- ν v; let b:= S+ν v; have hv:= position_p P p M D₀ uv.ph uv.located t r
 have hc:n=P.tock v (t i):=(congrFun hv i).symm; have H:= blanks P p i D₀ qa uv (A'.realWidth P i) h.2; let a:= A'.realWidth P i; have vA: a≤ n:=by unfold n a; linarith only [H.1]
 have vB:a≤b:= by unfold b S a; linarith only [H.2.1]
 rw [rates P i D₀ M A' L hp _ (P.vtile v t) (by rw [hv,u,seated P M D₀ hp]; abel),h.1]; let e':= uv.located.cost.vivid
 have hy:P.tock v (P.reachLeaf s v (moonSpan P s)) -n=b:=by unfold n b S; rw [extending_clock P uv.ph,P.tock_price]; unfold moonClock; rw [Int.cast_natCast]; ring
 let W:= HC; have he':P.ThreadOp i L A'.s (HC) (P.shifts i (t i) A'.F) ((A').dye P i L n b):= A'.dyedHere P i L (t i) n b (by change P.tock A'.s (t i)= _; rw [h.1,hc]) (by change P.tock A'.s W-n= _; rw [h.1]; exact hy) vA vB
 have hH:= he'.shiftCap t; rw [h.1,chartAll,P.cruise_mesh,P.shifts_sum,neg_add_cancel,P.shifts_zero] at hH
 exact hH.unique (let_thread P p uv.located.cost i Q he (p' t r).symm L) -- state charter arguments
lemma lantern (a:A'.realWidth P i+ν v≤ u')(c:A'.realWidth P i-ν v≤ d')(p:u'≤ t)(z:d'≤r) : Ω A' t r=(σ).pad (t-u') (r-d') (Ω A' u' d'):=by
 unfold lined; rw [h.1]; rw [show P.rawBase i L A' _ _= (σ).sand (P.rawBase i L A' (u'-ν v) (d'+ν v)) (t-u') (r-d') from ?_,P.charter_sand]; rfl
 rw [P.rawBase_step i L _ (a:=u'-ν v) (b:=d'+ν v),sub_sub_sub_cancel_right, add_sub_add_right_eq_sub] <;> linarith
omit h
-- stretch earned independently of costs.Arms.Housing.
lemma sky (pL:64 ≤ P.par.R.L.val)(j:ℕ) :∀ᶠ s:ℕ in atTop,∀ D:Cover,ResidualPermit D→∀ v,s≤v→∀ p:Cover,ShowField P s (homeTag P D) p→ StretchClock P j s v D p:=by
 filter_upwards [narrow_clock P pL j,wing_room P pL j,(wait_tends P).eventually_ge_atTop 16] with s h ht he d hd v f p t
 refine ⟨t,?_,fun e=> ht v f _ e,f,h v f _ hd _ t⟩; unfold moonClock; refine mul_le_mul_of_nonneg_right (by exact_mod_cast (show 16≤ moonSpan P s from by rw [pay_half]; omega)) (P.macroStep_pos _).le
-- pay once for each.Economy.Linear.
include uv qa h
variable (Q':P.Card i v (P.reachLeaf s v (moonSpan P s))) (h₂:P.voxTest i v Q'.val∈enclave P.calibration)(hq:hangs_it P p i D₀ A' Q)(B:P.Apron)(k0:blankRent P B v s i) (hc:hangs_it P p i D₀ B Q')
include k0 hc hq he h₂
set_option maxHeartbeats 200000 in
lemma lineup {K:ℝ}(z:ℂ)(u:δ≤ u')(w:δ≤d')(p':‖poleDay P p uv.located.cost i Q - z • poleDay P p uv.located.cost i Q'‖≤K): ‖Ω A' u' d'- z • Ω B u' d'‖≤ K:=by
 let y:= ℛ; let V₁:= blanks P p i D₀ qa uv _ h.2; let V₂:= blanks P p i D₀ qa uv _ k0.2; let t:= T; let r:=δ- t; let U:= Ω A' t r; let V:= Ω B t r
 obtain ⟨p2,tq⟩:=position_ticks P p M D₀ uv.ph uv.located; let g':P.VMark:= P.vtile v p2-chair P M D₀ hp; have hg:P.laysM g'=geoAt P s (nodeC p)-home P D₀ f:=by unfold g'; rw [laysDiff,position_p P p M D₀ uv.ph uv.located p2 tq,seated]; abel
 have e:‖y g' U-z • y g' V‖≤K:=by
    unfold y U V r t; rw [recall_shade P p i D₀ M A' L uv Q he h hp hq qa g' hg, recall_shade P p i D₀ M B L uv Q' h₂ k0 hp hc qa g' hg]; exact (expenses P p uv.located.cost i Q Q' he h₂ z L).trans p'
 let t':= lantern P i D₀ M A' L h hp V₁.1 V₁.2.1 (V₁.2.2.1.trans u) (V₁.2.2.2.trans w); let r':= lantern P i D₀ M B L k0 hp V₂.1 V₂.2.1 (V₂.2.2.1.trans u) (V₂.2.2.2.trans w)
 rw [t',r',←map_smul, ←map_sub]; refine ((σ).pad_le _ _ _).trans ?_; rw [←P.charter_cost i L g', P.charter_sub,P.charter_smul]; exact e
omit uv qa h k0 hc hq he h₂
#print axioms lineup
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
