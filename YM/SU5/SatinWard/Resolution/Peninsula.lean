import YM.SU5.SatinWard.Resolution.Fanes
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
noncomputable abbrev monthlyRent (A c:ℝ)(s v:ℕ):= (2:ℝ)* owedP A c*(sprintCost P.par.R.L^(v-s))⁻¹
noncomputable abbrev cycleRoot (C:ℝ)(s v:ℕ){K:Calibration}(A B:Family K): Family K:= C^(v-s) • ((1/2:ℝ) • (A-B))
local notation "ξ" => cycleRoot (sprintCost P.par.R.L) s v
include q k in
lemma cycle_compare (h:s≤v)(u:0<c)(f:∀ᶠ n in atTop, ∃ Z:Site (side P.run (P.nomadic (D n)) s)→ Mark (side P.run (P.nomadic (D n)) v), SeatsPriced A P.run s (P.nomadic (D n)) (P.engine (D n)) v Z c ∧ TwistP P.run (P.nomadic (D n)) s v Z∧ exhibit P.run P.large v (P.nomadic (D n)) (cycleRoot (sprintCost P.par.R.L) s v (G n) (R n))= Z (P.rootAt s (P.nomadic (D n)) p)): ‖daySpend P p hb hz pc e.landing i -daySpend (S:=S') P p hb hz pc' e'.landing i‖ ≤ monthlyRent P A c s v:=by
 let E':= cueSub (cueMono e pc) (cueMono e' pc')
 let B':Family (B$):= ξ F T; let d:ℝ:=κ^(v-s); have hd:0<d:= pow_pos (sprint_pos _) _; have y:0<d*(1/2):= by positivity
 have v₁:F-T=F-T:=rfl; have ht(M G': Family P.calibration):ξ M G'= (↑(d*(1/2:ℝ)):ℂ) • (M-G'):=by rw [Complex.coe_smul,mul_smul]
 have p':BQueue (U$) (fun n=> ξ (G n) (R n)) B':=by unfold B'; simp_rw [ht]; exact cue_scale E' _ _ tendsto_const_nhds
 have t:=chargeFor P p q p' hb hz (by exact subset_refl _) i h u f k -- order scout.
 let z:=P.Hil i; let f': z.Op:= daySpend P p hb hz pc e.landing i; let g': z.Op:= daySpend (S:=S') P p hb hz pc' e'.landing i
 let A': P.Card i v (P.reachLeaf s v w):= cardC P p hz i E'.landing (by exact subset_refl _)
 have hh:daySpend P p hb hz (S:=pavilion (P.clockPlate s v p) (rentWidth P j v)) (Finset.Subset.refl (pavilion (P.clockPlate s v p) (rentWidth P j v))) p'.landing i=(d*(1/2)) • daySpend P p hb hz (S:=pavilion (P.clockPlate s v p) (rentWidth P j v)) (Finset.Subset.refl (pavilion (P.clockPlate s v p) (rentWidth P j v))) E'.landing i:=by
    refine dayScale (S:=pavilion (P.clockPlate s v p) (rentWidth P j v)) (G:=F-T) (F:=B') P p hb hz (subset_refl _) p'.landing i (subset_refl _) E'.landing (d*(1/2:ℝ)) ?_
    exact ((ht F T).trans (Complex.coe_smul ..))
 rw [hh,daySub (F':=F) (G:=T) (S:=pavilion (P.clockPlate s v p) (rentWidth P j v)) (U:=S) (Q:=S') P p hb hz (Finset.Subset.refl _) E'.landing i pc pc' e.landing e'.landing rfl,norm_smul,Real.norm_of_nonneg y.le] at t
 change ‖f'-g'‖ ≤ _; change d*(1/2)*‖f'-g'‖≤ owedP A c at t
 unfold monthlyRent; rw [←div_eq_mul_inv]; apply (le_div_iff₀ hd).2; linarith only [t]
-- 
lemma cycleAt (i:ℕ): exhibit P.run P.large v i (cycleRoot (sprintCost P.par.R.L) s v F T)= sprintCost P.par.R.L^(v-s) • ((1/2:ℝ) • (exhibit P.run P.large v i F-exhibit P.run P.large v i T)):=by unfold cycleRoot; simp_rw [←Complex.coe_smul]; rw [map_smul,map_smul,map_sub]
variable (η:Type)[Fintype η](Q:ℕ→ Coords Wage4)(C:Coords Wage4)(u:payable P v 2)(Z':Option Tilted.Ramp)
noncomputable abbrev volumeFee (F:ResolutionFrame Wage4)(η:Type)[Fintype η](A H:ℝ)(s:ℕ):= rentP P.par.R.L A (yardF F) H F * lapQ P.run s
local notation "aX"=> totalBudget A (Announcement Wage4 η)
variable (M':(n:ℕ)→Site (side P.run (P.nomadic (D n)) v)→ Mark (side P.run (P.nomadic (D n)) v)) (F_:∀ (n:ℕ), ArkLease (Wage4⊕η) P.run cloverFrame (P.nomadic (D n)) (P.engine (D n)) f0 v A (yardF cloverFrame) H (paintClass P.run v (P.nomadic (D n)) (P.engine (D n))) (M' n) (Q n))
variable (μS:Tendsto Q atTop (𝓝 C))(pZ:∀ n,Poisson (side P.run (P.nomadic (D n)) v) (M' n) ∧ (∀x,AtSupport false univ (M' n x)) ∧ exhibit P.run P.large v (P.nomadic (D n)) (G n) = M' n (wrap (side P.run (P.nomadic (D n)) v) x) ∧ Satin.PairIdx P.run v (P.nomadic (D n)) (P.engine (D n)))
local notation "Θ"=> volumeFee P cloverFrame η A H s
lemma past_sides : alloy P s v p⊆ U$ := inclPav _ _ _ (Nat.le_add_left petalD _)
include pZ wp F_ in
lemma carry_m(h:s<v)(f:f0≤ s)(n:ℕ): ∃ Z:Site (side P.run (iv n) s)→ Mark (side P.run (iv n) v), SeatsPriced (totalBudget A (Announcement Wage4 η)) P.run s (iv n) (kv n) v Z (Θ) ∧ TwistP P.run (iv n) s v Z∧ exhibit P.run P.large v (iv n) (cycleRoot (sprintCost P.par.R.L) s v (G n) (atlas P Z' s v p (Q n)))= Z (P.rootAt s (iv n) p):=by
   let X := armF Y (paintClass P.run v (iv n) (kv n)) (M' n) (Q n) h.le; let G':= pressureArm Y (M' n) (costV Z' (multiplier (Q n))) h.le; let E:=(F_ n).pricing _ f h
   obtain ⟨t,u,w,g⟩:= pZ n
   let B:=(starSparks Y h.le (Q n) t u g); let k:= (iv n)
   have hg: SeatsPriced (aX) P.run s k (kv n) v G' (Θ) ∧ TwistP P.run k s v G':=by
      cases Z' with
      | none=> have hz:X=G':=atlasEta P.run h.le _ g; exact hz ▸ ⟨E,B.become Y⟩
      | some U=> have hz:transportT U X=G':=starTiles Y U h.le (Q n) t u g; refine hz ▸ ⟨SeatsPriced.transported _ _ E _ ⟨g.1,g.2.le⟩,(SwingP.transported _ _ B E.fieldT).become Y⟩ -- arg first.L.
   refine ⟨G',hg.1,hg.2,?_⟩; rw [cycleAt,w] -- remove last
   unfold G' pressureArm; dsimp only; rw [plaza_node P h.le p x wp (iv n)]; have he:= bumpRoot P v (P.clockPlate s v p) (costV Z' (multiplier (Q n))) k (wrap (Mp n) x) ((node_of ..).trans (by rw [wp])); rw [show exhibit _ _ _ _ _=glowMark P.run k v _ (wrap (Mp n) x) from he]
private theorem normFog (P:Hilbert)(x y z:P.Op)(t:ℝ)(u:y=z)(v:‖x-z‖≤ t):‖x-y‖≤t:=u.symm ▸ v
include q k μS pZ wp F_
lemma flowingW (h:s<v)(f:f0≤ s)(c₀:0<rentP P.par.R.L A (yardF cloverFrame) H cloverFrame * lapQ P.run s) : ‖daySpend P p hb hz pc e.landing i-frameWave P Z' p hb u i C‖ ≤ monthlyRent P (totalBudget A (Announcement Wage4 η)) (volumeFee P cloverFrame η A H s) s v:=by
 let g':= forecast P Z' p s v u Q C μS; let hh:alloy P s v p⊆ pavilion (P.clockPlate s v p) (rentWidth P j v):=past_sides ..; let Lc:=daySpend P p hb hz hh g'.landing i
 have ht:frameWave P Z' p hb u i C=Lc:=rfl
 have hhκ:= cycle_compare (R:=fun i=>atlas P Z' s v p (Q i)) (pc:=pc) (pc':=hh) (T:=atlas P Z' s v p C) (S':=alloy P s v p) (j:=j) (c:=volumeFee P cloverFrame η A H s) (A:=totalBudget A (Announcement Wage4 η)) P p q e g' hb hz k i h.le c₀ (Eventually.of_forall fun i=> carry_m P p x wp η Q Z' M' F_ pZ h f i)
 let z:=(P.Hil i)
 have ht':((frameWave P Z' p hb u i C):(P.Hil i).Op)= daySpend (S:=alloy P s v p) P p hb hz hh g'.landing i:=rfl
 have w1:= normFog (P.Hil i) (daySpend P p hb hz pc e.landing i) (frameWave P Z' p hb u i C) (daySpend (S:=alloy P s v p) P p hb hz hh g'.landing i) (monthlyRent P (totalBudget A (Announcement Wage4 η)) (volumeFee P cloverFrame η A H s) s v) ht' hhκ
 exact w1
#print axioms flowingW
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
