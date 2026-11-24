import YM.SU5.Selected.Identify
import YM.SU5.FiniteGaugeData.Hills.Domicile
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Budget Azure's `Sphere` for the disclosed physical elected Phi! (1)

Match these *different* ways to choose transfers. Ingress through one Snag vs. the
stock block through the CP18 history. Keeping even the exact mark, not up to price.
Assume that we can choose this Commission with also a Rolled (will prove that separately).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Tapestry.Exhibition
namespace Spine
variable (P : Spine) (j : Axis)
local notation "K" => P.calibration
local notation "Λ" => P.par
local notation "ι" => P.width
local notation "Y" => P.run
local notation "H" => P.large

variable (s : ℕ) (S : Finset Cover) (ρ : P.Register)
local notation "S₊" S:max=> followBox («Λ»:=P.par) (l:=P.width) S
local notation "μ" n:max=> P.period (P.projection.rows n)
local notation "ν" n:max=> P.cutoff (P.projection.columns n)
local notation "π"=> P.history
open Afterglow.Hierarchy
open Hierarchy
private lemma sold_match (F : Family K)(n : ℕ) : sold Y H s n F = distribute Y H s n F:= (sold_v ..) -- last rfl?
private lemma ribbon_matches (f:Charm.W K)(h:Charm.Locator K f S)(n m:ℕ)(t:Offered Y S s n m)
    (p : Tivoli (followBox («Λ»:=P.par) (l:=P.width) S) (P.calibration.c (momentm Y n (s+1)))) :
    block Y H s n m S f.val = composeQ K (GridStep Λ ι S)
      (snag Y H S s n m (Charm.reading K S f h)):= by
  apply stationary_ext Y H (s+1) (S₊ S) n p.hosp (booked ..) (compose_t ..)
  rw [reserved Y H s S n m (show legalAt Y s n m from ⟨t.calendar,t.age⟩) h p]
  let D:=Charm.reading K S f h
  change ingress Y s n m (distribute Y H s n f.val) = _
  rw [←P.sold_match s f.val n,←P.sold_match, snag_pay Y H S s n m t, transitionQ_apply]
  erw [exchanged Y H S s t, Charm.reading_p]
variable {C:Call P.par P.width}{W:Wicket P.par P.width}(R:Rolled P.run P.large P.period P.cutoff W C)
include R
lemma azure_advances (f:Charm.W K) :
    (Charm.next Y H s P.law R f).val=P.projection.refine s f.val:=by
  obtain ⟨S,p⟩:= Charm.testimony K f; let g:= Charm.reading K S f p; let W₀:= GridStep Λ ι S
  rw [Charm.keeps Y H S s P.law R f p]; funext m u
  have ht:Tendsto (fun n:ℕ=>snag Y H S s (μ n) (ν n)) atTop (𝓝 (C S s)):= by
    refine (Metric.tendsto_nhds (a:=C S s)).mpr fun ε e=>?_
    filter_upwards [P.history.growsA.tendsto_atTop.eventually (Hierarchy.path_budget Y (v:=P.period) (A:=snag Y H S s) P.law.pick.grow_k ((R.evening S s).paths) ε e)] with n hn using hn _ (P.history.gate n)
  have hx:Tendsto (fun n:ℕ=> (snag Y H S s (μ n) (ν n) g)) atTop (𝓝 (C S s g)):= cn_apply (X:=Catalog S) («Y»:=Catalog (GridStep Λ ι S)) ht (tendsto_const_nhds (x:=g))
  have hv:Tendsto (fun n:ℕ=>μ n) atTop atTop:=P.law.pick.grow_i.tendsto_atTop.comp P.history.growsA.tendsto_atTop
  apply tendsto_nhds_unique (_ : Tendsto (fun n:ℕ=>block Y H s (μ n) (ν n) S f.val m u) atTop _) (P.block_hist s S _ p m u)
  refine (((Tint.eval_c _ _ m u).continuousAt (x:=C S s g)).tendsto.comp hx).congr' ?_
  filter_upwards [hv.eventually (turning Y H (s+1) W₀),P.history.growsA.tendsto_atTop.eventually (often_offer Y H S s P.law)] with n T V
  exact congrFun (congrFun (P.ribbon_matches s S f p _ _ (V _ (P.history.gate n)) T).symm m) u
#print axioms azure_advances
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
