import Bay.Season
import Bay.Kettle
import YM.SU5.Exchange.Seed.Transit
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Zephyr.Chern
open BPress (PL NPL)
local notation "fluxV"=>Zephyr.Chern.stream
local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine

open Push.Uniform
open Pitching.Focus QuadClock Preparation.Yoke BScale
open Mew Vow.TreasuryFog
open scoped YM.CF.Mew

open Roots


variable {I:Type}[LinearOrder I][Fintype I]
-- let κ positivity etc
namespace Berth

variable (w:Berth) {M L:ℕ} {F C D:ℝ→ℝ} {r:blazeK w.side}
 {σ:I→Seat w.side} {v:I→ Sour.Bag w.side}
 {E B:I→ Aura w.side→ℝ}
 (u:Orbit w.side)
 (y:I→phy w.side)

abbrev sockets (p:IsStarProjection (w.emblem u))(f:phy w.side)(V:Sour.Bag w.side):=
 ∀ x:Wave (Dwell w.side),
 w.pilot u p (acts (∑ i,V i u) x)=acts (f u) (w.pilot u p x)

lemma feeds (p:IsStarProjection (w.emblem u))
 (g:∀ i,w.sockets u p (y i) (v i))
 (z:Mew.Key I)(σ:I→Seat w.side)(L:ℕ)(X:Wave (Dwell w.side)):
 w.pilot u p (acts (∑ Y:Aura w.side, flareM (w.melt σ v L) z u Y) X)=
 acts (Liss.waveΦ (fun i=>y i u) z) (w.pilot u p X):=by
 have hz:
    (∑ Y:Aura w.side, flareM (w.melt σ v L) z u Y)=
     ∑ i,z i • (∑ Y:Aura w.side, v i Y u):=by
   unfold flareM riseV melt
   rw [Finset.sum_comm]
   refine Finset.sum_congr rfl (fun i _=>?_)
   rw [←Finset.smul_sum,←Finset.sum_apply,←Finset.sum_apply,stickSum]

 rw [hz,act_sum,map_sum,Liss.waveΦ,act_sum]

 apply sum_congr rfl
 intro i _
 rw [act_smul,map_smul,g i,act_smul]

variable {w}
 (g:w.Thermal M L F C D r)(mulσ:Multiplicity σ M)
 (d:w.Cached σ v L E B C D)

 -- ket.
abbrev offsetR (w:Berth)(V:RegBudget w.side)(W:ForceBudget w.side):=
  ({w.R with F:=w.R.F+V,K:=w.R.K+W}:GramM w.side)
abbrev swipe (w:Berth)(V:RegBudget w.side)(W:ForceBudget w.side):=
  denZ (w.offsetR V W) w.U w.K
abbrev winE (w:Berth)(U:Mew.Key I→ RegBudget w.side)(V:Mew.Key I→ForceBudget w.side)
  (l:List I)(u:Orbit w.side):Phys w.side:= tipI (fun z=> w.swipe (U z) (V z) u) l

include g mulσ in
lemma primesw (p:IsStarProjection (w.emblem u))
 (j:∀ i,w.sockets u p (y i) (v i))
 (s:ℕ)(δ:1 ≤ s)(τ:Ids w.side)
 (l:List I)(o:ψS σ l) (e:l.length ≤ s)
 (k:FleetS w.R.p.threshold u.1)
 (ind:l.Pairwise (fun i j=>Commute (y i u) (y j u))):
 w.winE (w.flareE d σ s τ) (w.flareF d σ s) l u=
 acts (l.map (fun i=>y i u)).prod (w.volume u) := by

 have T:=farm g.1 σ mulσ (hearth L) d
 refine rackKey (B₁:=w.P.par.block) (N:=Vale.mesh (w.P.run.ir w.i) w.P.par.R.L w.s)
   (R:=w.R)
   w.U w.K u (w.coincert g.1) (flare d.bill) σ w.q (flareM (w.melt σ v L))
   T s w.P.par.height τ p l o (kilnTip d.bill σ τ) (fun i=>?_) (fun i=>y i u) k e ind (fun z _=>feeds w u y p j z σ L)
 exact conducts (B₁:=w.P.par.block) (N:=Vale.mesh (w.P.run.ir w.i) w.P.par.R.L w.s) (R:=w.R)
    (w.coincert g.1) _ _ _ _ T s w.P.par.height τ _ δ _ (sparksRaise σ d.bill
     (d.tie σ (hearth L)) τ i)
end Berth
