import YM.SU5.SatinWard.Resolution.Peninsula
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
variable (η:Type)[Fintype η](Q:ℕ→ Coords Wage3)(C:Coords Wage3)(kμ:Axis)
noncomputable abbrev rentX (s:ℕ):= rentP P.par.R.L A (yardF (spinFrame 3)) H (spinFrame 3) * lapQ P.run s
local notation "aX"=> totalBudget A (Announcement Wage3 η)
local notation "Θ"=> rentP P.par.R.L A (yardF (spinFrame 3)) H (spinFrame 3) * lapQ P.run s
variable (M':(n:ℕ)→Axis→ Site (side P.run (P.nomadic (D n)) v)→ Mark (side P.run (P.nomadic (D n)) v)) (F_:∀ (n:ℕ), ArkLease (Wage3⊕η) P.run (spinFrame 3) (P.nomadic (D n)) (P.engine (D n)) f0 v A (yardF (spinFrame 3)) H (spinClass P.run v (P.nomadic (D n)) 3) (M' n 3) (Q n))
local notation "A!"=> Signboard.spineField P.par P.calibration v kμ
variable (μS:Tendsto Q atTop (𝓝 C))(pZ:∀ n, Dirfield (side P.run (P.nomadic (D n)) v) (M' n) ∧ exhibit P.run P.large v (P.nomadic (D n)) (G n)=M' n kμ (wrap (side P.run (P.nomadic (D n)) v) x) ∧ Satin.PairIdx P.run v (P.nomadic (D n)) (P.engine (D n)))
include wp pZ F_ in
lemma carryJ(h:s<v)(f:f0 ≤ s)(n:ℕ): ∃ Z:Site (side P.run (iv n) s)→ Mark (side P.run (iv n) v), SeatsPriced (totalBudget A (Announcement Wage3 η)) P.run s (iv n) (kv n) v Z (Θ) ∧ TwistP P.run (iv n) s v Z∧ exhibit P.run P.large v (iv n) (cycleRoot (sprintCost P.par.R.L) s v (G n) (Signboard.spineField P.par P.calibration v kμ (Q n) x))= Z (P.rootAt s (iv n) p):=by
 obtain ⟨t,hq,e⟩:=pZ n; obtain ⟨U,z⟩:=directionRead P.run aX h.le (Q n) t kμ e ((F_ n).pricing _ f h)
 refine ⟨pupilAim Y (M' n) kμ (Q n) h.le,z,U,?_⟩; rw [cycleAt,hq,Signboard.spinogram]; unfold pupilAim armF; rw [plaza_node P h.le p x wp (iv n)]
include μS in
lemma lessonU (U:ℕ): BQueue (pavilion (nodeC x) U) (fun i=> spineField P.par P.calibration v kμ (Q i) x) (spineField P.par P.calibration v kμ C x):=by
 let S':=pavilion (nodeC x) U; let G:= rungLeaf P.calibration (vigorΩ P.par v) kμ; have ht(z): spineField P.par P.calibration v kμ z x=(∑ i:Wage3,(z i:ℂ) • G i x):=by unfold spineField; rw [ShapeLab.cols_apply,Finset.sum_apply]; simp_rw [Complex.coe_smul]; rfl
 simp_rw [ht]; apply cueWords univ _ _; intro i _; let h : InTest P.calibration true S' false (G i x):=((rungD kμ ..).lift (by omega:0≤ U)).valid x; exact cue_scale (P.pallet h) (fun j=> (↑(Q j i):ℂ)) (C i:ℂ) (Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_pi_nhds.mp μS i))
private lemma normFog (P:Hilbert)(x y z:P.Op)(t:ℝ)(u:y=z)(v:‖x-z‖≤ t):‖x-y‖≤t:=u.symm ▸ v
noncomputable abbrev headrent (A H:ℝ)(s:ℕ):= (rentP P.par.R.L A (yardF (spinFrame 3)) H (spinFrame 3) * lapQ P.run s) -- same as rentX
noncomputable def spinDoor (q:nodeC x=P.clockPlate s v p)(u:Axis)(z:Coords Wage3):P.Card i v (P.reachLeaf s v w):= cardC P p hz i ((Signboard.letterShape (J:=P.calibration) (Λ:=P.par) u v z).valid x) (pavilionWidth P p x q (Nat.zero_le _))
include pZ wp F_ μS q k in
lemma flowingJ (h:s<v)(f:f0≤ s)(c₀:0<headrent P A H s) : ‖daySpend P p hb hz pc e.landing i-poleDay P p hb i (spinDoor P p x hz i wp kμ C)‖ ≤ monthlyRent P (totalBudget A (Announcement Wage3 η)) (headrent P A H s) s v:=by
 let F':= (A! C) x; have t:= lessonU P x Q C kμ μS (v:=v) 0; let S':= pavilion (nodeC x) 0; let hh:S'⊆ pavilion (P.clockPlate s v p) (rentWidth P j v):= pavilionWidth P p x wp (by omega); have g : poleDay P p hb i (spinDoor P p x hz i wp kμ C)= daySpend P p hb hz hh t.landing i:=rfl
 have V':= cycle_compare (R:=fun i=> (spineField P.par P.calibration v kμ (Q i)) x) (pc:=pc) (pc':=hh) (T:=F') (S':=S') (j:=j) (c:=headrent P A H s) (A:=totalBudget A (Announcement Wage3 η)) P p q e t hb hz k i h.le c₀ (Eventually.of_forall fun i=> carryJ P p x wp η Q kμ M' F_ pZ h f i) -- hold.Named
 have w' := normFog (P.Hil i) (daySpend P p hb hz pc e.landing i) (poleDay P p hb i (spinDoor P p x hz i wp kμ C)) (daySpend (S:= S') P p hb hz hh t.landing i) (monthlyRent P (totalBudget A (Announcement Wage3 η)) (headrent P A H s) s v) g V'; exact w'
#print axioms flowingJ
-- averageW cost.Warp lemma arithmetic dedicated
private theorem normAvg (P:Hilbert)(x y z w u:P.Op)(t C:ℝ)(eq:y+z+w= (3*t:ℝ) • u)(a:‖x-y‖≤ C)(b:‖x-z‖≤ C)(c:‖x-w‖≤ C):‖x- (t • u)‖≤C:=by
 have h:= (norm_add_le ((x-y)+(x-z)) (x-w)).trans (add_le_add ((norm_add_le (x-y) (x-z)).trans (add_le_add a b)) c); rw [show x-y+(x-z)+(x-w)= (3:ℝ) • (x-t • u) from by rw [smul_sub,← mul_smul (3:ℝ) t, ←eq]; module, norm_smul,Real.norm_of_nonneg (by norm_num:(0:ℝ)≤3)] at h; linarith only [h] -- mul_smul not smul_smul
noncomputable abbrev wageMonth (P:Spine)(η:Type)[Fintype η](A H:ℝ)(s v:ℕ):= monthlyRent P (totalBudget A (Announcement Wage4 η)) (rentP P.par.R.L A (yardF cloverFrame) H cloverFrame*lapQ P.run s) s v
variable (Q':ℕ→ Coords Wage4)(C':Coords Wage4)(u:payable P v 2)
variable (M'':(n:ℕ)→Site (side P.run (P.nomadic (D n)) v)→ Mark (side P.run (P.nomadic (D n)) v)) (F₁:∀ (n:ℕ), ArkLease (Wage4⊕η) P.run cloverFrame (P.nomadic (D n)) (P.engine (D n)) f0 v A (yardF cloverFrame) H (paintClass P.run v (P.nomadic (D n)) (P.engine (D n))) (M'' n) (Q' n))
variable (μs:Tendsto Q' atTop (𝓝 C'))(pW:∀ n,Poisson (side P.run (P.nomadic (D n)) v) (M'' n) ∧ (∀x,AtSupport false univ (M'' n x)) ∧ exhibit P.run P.large v (P.nomadic (D n)) (G n) = M'' n (wrap (side P.run (P.nomadic (D n)) v) x) ∧ Satin.PairIdx P.run v (P.nomadic (D n)) (P.engine (D n)))
include F₁ pW wp q k μs in
lemma flowWage (h:s<v)(f:f0 ≤ s)(c₀:0<volumeFee P cloverFrame η A H s): ‖daySpend P p hb hz pc e.landing i-(↑(gatherG C'):ℂ) • frameWave P none p hb u i pseV‖ ≤ wageMonth P η A H s v:=by
 have ht (U:Option Tilted.Ramp): ‖daySpend P p hb hz pc e.landing i-frameWave P U p hb u i C'‖ ≤ monthlyRent P (totalBudget A (Announcement Wage4 η)) (volumeFee P cloverFrame η A H s) s v:= flowingW P p x wp q e hb hz pc k i η Q' C' u U M'' F₁ μs pW h f c₀ -- order
 rw [Complex.coe_smul]; exact normAvg _ _ _ _ _ _ _ _ (frame_total_cost P p hb u i C') (ht none) (ht _) (ht _) -- universes typeclass
#print axioms flowWage
end Internal
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
