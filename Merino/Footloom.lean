import Merino.Pattern
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.CF.Merino
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Drapes Metric
open _root_.Zephyr.Chern
open scoped Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Finset Swell

variable {n:Side}

open Py.Rate.LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Skye Scree Vale RG
open Py (hueW stemS pinpr)
variable (P:Spine)


variable (s i k:ℕ)
local notation "N"=> RegNum P s i
local notation "K"=> LoomM P s i
local notation "R"=> LedgerM P s i k
local notation "q"=> P.par

open MeasureTheory Py.Rate.FullBill

/-- Qualification for claiming the payments on an actual consultation;
the projection requirement is for *all* density inputs, not just
the small-angle jet. -/
structure Hot(m:ℕ):Prop where
  admit: admitM P s i k
  priced: Priced P.par.V R P.par.U K (P.run.charge s) (P.run.debt s)
  usable:∀ z:Orbit N,IsStarProjection (Dial.spar P.par.K.j (R).J.M (K z))
  sky:Skylit (R).p P.par.d K
  yard:24*m≤(R).p.B
  claims: (R).p.B=radiusM P s


lemma Hot.cold{m:ℕ}(h:Hot P s i k m):
    Integrable (denZ R P.par.U K) (Scree.city N):=
  Integrable.of_bound h.priced.permits.meas.aestronglyMeasurable _
    (Eventually.of_forall h.priced.permits.cost.choose_spec)

lemma fired (h:Compass_sol P.run)(m:ℕ):
    onReg P (fun s i k=>Hot P s i k m):=by
  obtain ⟨_,_,_,_,_,_,_,_,gift⟩:=h.pays
  unfold onReg
  filter_upwards [gift,(Work.E01.radiusB_tendsto.comp (turnover P.par)).eventually_ge_atTop
    (24*m+2*P.par.J.n)] with v r hv
  filter_upwards [r] with j t l u
  obtain ⟨_,_,roof,count,ht,_⟩:=t l u.2
  have hB: (LedgerM P v j l).p.B=radiusM P v:=by rw [(calibrated P u.2.le).1]; exact (P.run.meter.boot v).2.1
  change 24*m+2*P.par.J.n ≤ radiusM P v at hv
  exact ⟨u,P.run.each_level j l v u.1 u.2.le,
    fun z=>(P.par.U.broadness _ count _).projection _ ((roof.paid z).shrink P.par.J.hr.le),
    ⟨P.par.dpos,_,_,_,roof,ht,P.par.J.hr.le,by omega⟩,by omega,hB⟩
end YM.CF.Merino
