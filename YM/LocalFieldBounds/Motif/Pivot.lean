import YM.LocalFieldBounds.Motif.Pictorial
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 430000
set_option maxRecDepth 8000
set_option quotPrecheck false
noncomputable section
namespace YM.LocalFieldBounds.Motif
open Filter Function Set Metric MeasureTheory 
open scoped Topology ComplexOrder InnerProductSpace NNReal Classical
open CF.Buffered.Afterglow.Tower.VacuumSelection Spine
open CF.QuadClock.ShapeLab SoulField SatinWard.Installment
open Spine.Fame.Regulator Internal Dovetail Freeport Polaris
open Polaris.Rampart _root_.GarnetAct.Cut
open Set MeasureTheory
open _root_.YM.SatinWFixed Andesite Carton _root_.YM.Boundary Probe
open CF.Py.Rate.LocalLimit Preparation
open CF.Buffered.Afterglow.Tower
open Preparation.Tabletop CasaF.Signboard
open CF.Py.Rate.LocalLimit.Preparation.Yoke
open CF.Ione.Clock CF.Moto CF.LitCurrent AuroraX Verdance Lattice
open CF.QuadClock.SignSlot
open Chili
open YM.WakeFields CF
open Papal.Moon
open SatinWard
universe u

open Resolving ResolutionFrame

attribute [local irreducible] Spine.Register
open CF.Buffered.Afterglow.Journey CF.Buffered.Afterglow.Tapestry

open Metric
variable {X Z:TintDemand}{Q:Supplier}{m:ℕ}{η:Type}[Fintype η][Nonempty η]
  {ε' target:ℝ}(y : Programme.{u} X Z Q m η ε' target)

variable (P:Spine)

variable (f:ℕ→ℕ) (ht:StrictMono f)
local notation "R0" => physicalPeriod P f
local notation "U0" => physicalCut P f
abbrev ν (s:ℕ) := P.run.ir (R0 s)
abbrev ups (s:ℕ) := P.run.uv (U0 s)
include ht
lemma earned_ferry (s:ℕ) :
    ∀ᶠ u in atTop, Ferry P.run s (R0 u) (U0 u) :=
  ht.tendsto_atTop.eventually (P.history.finance s)

lemma mean_sold (s:ℕ) (F:P.Test) :
    Tendsto (fun j => CF.Buffered.Afterglow.Journey.sharp P.run P.large s (R0 j) (U0 j) F.val)
       atTop (𝓝 (P.E s F.val)) := by
  obtain ⟨B,h⟩ := findsBay _ F
  change CF.Buffered.InTest P.calibration true B false F.val at h
  obtain ⟨a,v⟩ := valuation P.run P.large h
  obtain ⟨d,l,m⟩ := P.history.implements s B
  have ha := pay_nonneg (show pay F.val a from v)
  apply Metric.tendsto_nhds.2
  intro ε hε
  let δ:=ε/(a+1)
  filter_upwards [ht.tendsto_atTop.eventually (m δ (by unfold δ; positivity))] with u k
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (k F.val h a v).2.2.2.2.1
  have g:δ*(a+1)=ε := div_mul_cancel₀ _ (by linarith)
  linarith only [g, (by unfold δ; positivity : 0<δ)]

lemma costs :
    StrictMono (fun s=> (ν P f s).val) ∧ StrictMono (ups P f) :=
  ⟨P.run.ir_grows.comp (P.law.pick.grow_i.comp (P.history.growsA.comp ht)),
   P.run.uv_grows.comp (P.law.pick.grow_k.comp (P.history.growsB.comp ht))⟩

omit ht
abbrev rootRate (i k s:ℕ) := ((((P.run.voyage i).X (P.run.uv k)).gram s).beta)
abbrev Fall (s j:ℕ) (F:P.Test) :=
  CF.Buffered.Afterglow.Journey.sharp P.run P.large s (R0 j) (U0 j) F.val


open MeasureTheory
lemma drinks (s:ℕ) (F:P.Test) :
    P.E s F.val = ∫ x:P.Spectrum0 3, P.singleState 3 s x F ∂P.pillars 3 := by
  change P.E s F.val = ∫ x:P.Spectrum0 3,P.chi 3 x (P.reading 3 s F) ∂P.pillars 3
  rw [P.recovery]
  exact (P.occupied 3 s F).symm

/-- Beta in inverse-pivot convention. Coherent realization on *any one
strictly increasing* speed like the Programme tuning f; retains the mean of readings on the chosen-vacuum family of offers at that same resolution.
Sharp approaches the law mean, not claiming it approaches the selected value! -/
structure Pivot (target:ℝ) :Prop where
 fee : 0<P.par.x ∧ target<P.par.x
 recipe : ∀ i k, rootRate P i k 0=P.par.x
 widths : StrictMono (fun j=>(ν P f j).val) ∧ StrictMono (ups P f)
 lawful : ∀ s, ∀ᶠ j in atTop, Ferry P.run s (R0 j) (U0 j)
 pays : ∀ s F,Tendsto (fun j => Fall P f s j F)
   atTop (𝓝 (∫ x:P.Spectrum0 3, P.singleState 3 s x F ∂P.pillars 3))

include ht
theorem pivot : Pivot y.P f target := by
  have h : 0<y.P.par.x := (Real.exp_pos _).trans_le y.P.large
  have t : target<y.P.par.x := y.pose.1.meets
  refine ⟨⟨h,t⟩,y.P.terminalBeta y.U y.pose,costs y.P f ht,earned_ferry y.P f ht,
       fun s F=>?_⟩
  rw [← drinks]
  exact mean_sold y.P f ht s F
omit ht
theorem tied : Pivot y.P y.f target :=
  pivot y y.f y.ht
#print axioms tied
end YM.LocalFieldBounds.Motif
