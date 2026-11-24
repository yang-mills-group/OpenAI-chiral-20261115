import YM.SU5.SatinWard.Resolution.Postern
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
variable (h:s<v) (f:f0 ≤ s) (Hc:1≤H)(Ac:1≤A) (fA:0<a)
local notation "εμ"=> Wage4
local notation "j⊗"=> yardF (spinFrame 3)
local notation "v!"=> hourBound P.run v
variable (η:Type)[Fintype η]
noncomputable abbrev pulseMonth (P:Spine)(η:Type)[Fintype η](A H:ℝ)(s v:ℕ):= monthlyRent P (totalBudget A (Announcement Wage3 η)) (headrent P A H s) s v
variable {Z:Visit → Cover→ Family P.calibration}{M: PitchZ} {d:Division}(L:Ceremo P η v j f0 a b φ H A d D Z M)
local notation "O⋆" => fullStar P.par v j Z
local notation "ΨH" s:max=>pinpr P.par.R.L (hat P.par.R.L P.par.x s)
-- chosen relation. can retell broadside to anyone.
include L in
lemma plotQ (x:Cover)(t:Visit) : InTest P.calibration true (pavilion (nodeC x) (hourBound P.run v)) false (Z t x):=(L.earnedZ P η t).valid x
include L in
lemma logStarCore : Domicile (hourBound P.run v+2*j) (fullStar P.par v j Z):= fullStar_live v P.par (L.earnedZ P η) _
include wp in
lemma rentVisit : pavilion (nodeC x) (hourBound P.run v)⊆ pavilion (P.clockPlate s v p) (rentWidth P j v):= pavilionWidth P p x wp (show P.thresholdF v+12 ≤ P.thresholdF v+12+2*j+petalD from by omega)
include wp in
lemma starVisit : pavilion (nodeC x) (hourBound P.run v+2*j)⊆ pavilion (P.clockPlate s v p) (rentWidth P j v):= pavilionWidth P p x wp (show P.thresholdF v+12+2*j ≤ P.thresholdF v+12+2*j+petalD from by omega)
noncomputable abbrev chiefSpend (t:Visit): (P.Hil i).Op:= daySpend (S:=pavilion (nodeC x) (hourBound P.run v)) P p hb hz (rentVisit P p x wp) (plotQ P η L x t) i
noncomputable abbrev starSpend : (P.Hil i).Op:= daySpend (S:=pavilion (nodeC x) (hourBound P.run v+2*j)) P p hb hz (starVisit P p x wp) ((logStarCore P η L).valid x) i
-- combine.Estim
variable (hv:0<lapQ P.run s)(ht:0 <lapQ P.run v)(u:payable P v 2)
include h f L hb hz k Hc Ac q hv
lemma phaseJ (kμ:Axis):‖chiefSpend P p x wp hb hz i η L (some kμ)-poleDay P p hb i (spinDoor P p x hz i wp kμ M.2.2)‖ ≤ pulseMonth P η A H s v:=by
 obtain ⟨E,U,M₁,t,W,m⟩:= L.anchor
 let G(i):= fun j x=>JField Y (E i) x d (j,false); let p'(n):=beatTurns Y (m n).2.1 (E n) d; let S:= pavilion (nodeC x) (hourBound P.run v); let U':= W.bills (some kμ) x; let hq:=fun i'=>(M₁ i').2.2
 have hx(i':ℕ): Dirfield (side P.run (P.nomadic (D i')) v) (G i') ∧ exhibit Y P.large v (iv i') (U i' (some kμ) x)= G i' kμ (wrap (Mp i') x)∧ Satin.PairIdx Y v (iv i') (kv i'):= ⟨p' i',W.learns x i' (some kμ),(m i').1⟩; have e:=flowingJ P p x wp q U' hb hz (rentVisit P p x wp) k i η hq M.2.2 kμ G (fun n=> (m n).2.2.stakeJ) t.snd_nhds.snd_nhds hx h f (mul_pos (rentP_pos (P:=P.par) _ H A Ac (stretch_funded _).choose_spec.large Hc) hv)
 exact e
-- Q.One.Budget uniform.Lower. and weight star
lemma phaseQ : ‖chiefSpend P p x wp hb hz i η L none - (↑(gatherG M.1):ℂ) • frameWave P none p hb u i pseV‖ ≤ wageMonth P η A H s v:=by
 obtain ⟨E,U,M₁,t,W,m⟩:= L.anchor
 let G(i):= fun x=> qField Y (E i) x d; let hx:= W.bills none x; have he(i):=qTurns Y (m i).2.1 (E i) d
 have hz1(n): ∀ x:Site (side P.run (P.nomadic (D n)) v),AtSupport false univ (G n x) :=fun x=> ((enc Y v (P.nomadic ∘ D) (P.engine ∘ D) (fun i=> (m i).1.2) (fun i=> (m i).2.1) E d none n x).1).mono (subset_univ _)
 let hm':= fun n=>(M₁ n).1; let G':=flowWage P p x wp q hx hb hz (rentVisit P p x wp) k i η hm' M.1 u G (fun n=>(m n).2.2.stakeQ) t.fst_nhds (fun i=>⟨he i,hz1 i,W.learns x i none,(m i).1⟩) h f (mul_pos (rentP_pos (P:=P.par) _ H A Ac (stretch_funded _).choose_spec.large Hc) hv)
 exact G'
include ht in
lemma phaseStar : ‖starSpend P p x wp hb hz i η L - (↑(gatherG M.2.1):ℂ) • frameWave P none p hb u i pseV‖ ≤ wageMonth P η A H s v:=by
 obtain ⟨E,U,M₁,t,W,m⟩:= L.anchor
 let G(i):= fun x=> starField Y (E i) x d; have hv'(n):MaskPoint P.run j v (P.nomadic (D n)) (P.engine (D n)) a b:= (m n).2.1; let S:= pavilion (nodeC x) (hourBound P.run v+2*j); let U':= W.starBudget P.run P.large v (P.nomadic∘D) (P.engine∘D) E d x
 have hx(n): Poisson (side P.run (P.nomadic (D n)) v) (G n) ∧ (∀ x,AtSupport false univ (G n x)) ∧ exhibit Y P.large v (iv n) (fullStar P.par v j (U n) x)= G n (wrap (Mp n) x)∧ Satin.PairIdx Y v (iv n) (kv n):=by
    refine ⟨starTurns Y (hv' n) (E n) d,fun x=>?_,W.starPrice P.run P.large v _ _ hv' E d x n ht,(m n).1⟩; let p:=hv' n; let R:=RootBook P.run (P.nomadic (D n)) (P.engine (D n)) v; let K:=(P.run.voyage (iv n)).CapeT v; obtain ⟨B',H,V'⟩:=metaStamp d K R.p (R.p.B/10) (1/2) x (E n) p.C 24 p.reach p.escap
    exact ((H.ticket.smulM Complex.I).smulM (↑(hueW L★ (hat L★ P.par.x v)):ℂ)).mono (subset_univ _)
 let hm':= fun n=>(M₁ n).2.1; let G':= flowWage P p x wp q U' hb hz (starVisit P p x wp) k i η hm' M.2.1 u G (fun n=>(m n).2.2.stakeS) t.snd_nhds.fst_nhds hx h f (mul_pos (rentP_pos (P:=P.par) _ H A Ac (stretch_funded _).choose_spec.large Hc) hv)
 exact G'
#print axioms phaseJ
#print axioms phaseQ
#print axioms phaseStar
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
