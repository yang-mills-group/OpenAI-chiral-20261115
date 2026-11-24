import GaugeFieldConstruction.AcrossCadence
import YM.SU5.FiniteGaugeData.Tapestry.Rafters
import YM.SU5.Selected.Overview
import GaugeFieldConstruction.AcrossPrices
import GaugeFieldConstruction.AcrossTapeBound
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option maxRecDepth 4100
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory
  RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder
  InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Tapestry.Altitude Tapestry.Exhibition
open TopologicalSpace
namespace Spine
variable {P : Spine} {s i k : ℕ}
open AcrossLands
open Py.Rate.AcrossShots VolumeRate
variable (P) (v:ℕ→ℝ)
abbrev tapeᵢ := P.period ∘ P.projection.rows
abbrev tapeₖ := P.cutoff ∘ P.projection.columns
local notation "I"=> P.tapeᵢ
local notation "Kq"=> P.tapeₖ
local notation "Λ"=> P.par
private abbrev periodMarkSt(t:ℕ):=P.run.ir (P.tapeᵢ t)
abbrev tapeDepth:= P.run.uv ∘ Kq
local notation "δ"=> P.tapeDepth

lemma paidᵢ : StrictMono I:= P.law.pick.grow_i.comp P.history.growsA
lemma paidₖ : StrictMono Kq:= P.law.pick.grow_k.comp P.history.growsB
lemma tape_whole : Tendsto (fun r=> (P.run.ir (I r)).val) atTop atTop:= P.run.ir_grows.tendsto_atTop.comp P.paidᵢ.tendsto_atTop
lemma tape_stairs : StrictMono δ:= P.run.uv_grows.comp (P.paidₖ)
lemma helmetTape (r): (P.run.ir (I r)).val^5 ≤ δ r:= P.history.gate r
lemma circuitPaysAt (s:ℕ) : ∀ᶠ t in atTop,(P.run.voyage (I t)).kick ≤ Kq t ∧ s≤δ t:= (P.history.finance s).mono fun _r p=>⟨p.depth,p.enters⟩


local notation "Γ" => P.par
local notation "Y" => P.run
local notation "D" => P.tapeDepth
local notation "C" => P.tapeᵢ
local notation "K" => P.tapeₖ
local notation "B" => P.large
local notation "H" => P.Effect
/-- pay all operators at cutoff even with deep step growth. Actual ROster doesn't need this
bound in its reconstruction; needed to perturb entire schedule once and for all. -/
noncomputable abbrev totalTickets:=Tapestry.ticketTape P.run
lemma tickets_hi (i k s:ℕ) : 1≤ P.totalTickets i k s:= Tapestry.tickets_hi Y i k s
lemma totalMono (i k:ℕ): Monotone (P.totalTickets i k):= Tapestry.ticket_tape_mono Y i k
open Tapestry.Fashion
lemma cardBoundSt (S:BillOfWork)(s:ℕ)(q:ℝ)(A:P.Effect) (h:Pocket P.calibration S s q A) :
 ∀ i k:ℕ, ‖breathing P.run P.large s i k A‖ ≤ P.totalTickets i k s * cloudSpan s S * q:=cardBound_tape P.run P.large S s q A h
-- This is definitionally Reconstruction.atCutoff Y ... (compare after importing high).
noncomputable abbrev chronicleCap (i k:ℕ)(A:P.Effect)(u:Pane (side P.run i (P.run.uv k))):= attire (breathing P.run P.large (P.run.uv k) i k A) (u,u)
lemma at_entry_limit (s:ℕ)(A:P.Effect) (h:A∈ shorter P.Test s) (r:ℝ)(v:0≤r)(i k:ℕ)(hg: ‖breathing Y B s i k A‖ ≤ P.totalTickets i k s*r) (hx:s ≤ (Y).uv k) (u): ‖chronicleCap P i k A u‖≤ totalTickets P i k ((Y).uv k)*r :=by
 exact (Tapestry.Ward.pay (breathing Y B ((Y).uv k) i k A) (u,u)).trans (at_entry_bound_tape Y B s A h r v i k hg hx)

lemma at_top_limit (S:BillOfWork)(s:ℕ) :
 ∀ (r:ℝ) (A:P.Effect), Pocket P.calibration S s r A → ∀ i k:ℕ, s ≤ (Y).uv k → ∀ U, ‖chronicleCap P i k A U‖≤ totalTickets P i k ((Y).uv k) * (cloudSpan s S*r) :=by
 intro r A h i k z U; apply at_entry_limit P s A h.funded (cloudSpan s S*r) (mul_nonneg (cloudSpan_pos s S) h.priced) i k _ z; rw [←mul_assoc]; exact P.cardBoundSt S s r A h i k

variable (A:P.Effect)
abbrev localPriceSt (m:Side)(p:BudgetPoint)(q:ℝ)(A:Pane (mid m (Γ).block)→FC (Single (mid m (Γ).block))) := AcrossLands.position m (Γ).U p q A
abbrev consultPrice (i k:ℕ)(β:ℝ):= AcrossLands.position (mesh (P.run.ir i) (Γ).R.L (P.run.uv k)) (Γ).U (P.run.meter.a (P.run.uv k)) β (chronicleCap P i k A)
lemma prim_pay (i k:ℕ) : Envelope (chronicleCap P i k A) := by
  let t:= (Y).uv k; let W:=breathing Y B t i k A; exact Env.along (g:=fun x: Pane (side Y i t)=> (x,x)) (Tapestry.Ward.signs W).env (measurable_id.prodMk measurable_id)
lemma correct_price (S:A∈shorter P.Test s) (v: Pay Y s i k):
    consultPrice P A i k ((P.run.headIn i (P.run.uv k)))=taking P.run P.large i k A:=by
 let t:=(Y).uv k; let Hp:=(Y).headIn i t; let M:=mesh ((Y).ir i) (Γ).R.L t; let N:= side Y i t
 let A':= chronicleCap P i k A
 let l:=(P.run.voyage i).CapeT t; let Q:= (((Y).voyage i).X t).gram t; let f:= attire (breathing Y B t i k A)
 let g(x:Orbit N):= inkMark (m:=M) ((Y).meter.a t) Hp (Γ).U A' x
 have hh(x:Orbit N):
    acts (f (drawn (((Y).voyage i).CapeT ((Y).uv k)) x)) (denZ (((P.run.voyage i).X (P.run.uv k)).gram (P.run.uv k)) (Γ).U ((P.run.voyage i).CapeT (P.run.uv k)) x) =
    acts (f (x.1,x.1)) (Vale.capP («K»:=(Γ).K) (Γ).U ((((Y).voyage i).X ((Y).uv k)).gram ((Y).uv k)).beta ((Y).meter.a ((Y).uv k)) x.1) := by
  rw [(Y).whole i k x]
  by_cases p : flags ((Y).meter.a ((Y).uv k)).threshold x.1 = ∅
  · let Po := (Y).history i k
    have hx : ((Y).voyage i).CapeT ((Y).uv k) x = x.1 :=
      Vale.Grace.Robes.solar x (((Y).voyage i).CapeT ((Y).uv k)) (Po.roof ((Y).uv k)).paid ((Y).meter.a ((Y).uv k)) (Po.pole ((Y).uv k)) p
    change acts (f (x.1, ((Y).voyage i).CapeT ((Y).uv k) x)) _=_
    rw [hx]
  have he: Vale.capP («K»:=(Γ).K) (Γ).U Q.beta ((Y).meter.a t) x.1=0:= Set.indicator_of_notMem (show x.1∉{v:Pane N| flags ((Y).meter.a t).threshold v=∅} from p) _
  change acts (f (drawn l x)) (Vale.capP («K»:=(Γ).K) (Γ).U Q.beta ((Y).meter.a t) x.1)=acts (f (x.1,x.1)) (Vale.capP («K»:=(Γ).K) (Γ).U Q.beta ((Y).meter.a t) x.1)
  rw [he,map_zero,map_zero]

 obtain ⟨z,d,h⟩:=taking_formula Y B ((Y).uv k) _ _ _ ⟨v.1,le_rfl⟩ (Altitude.climbs P.Test v.2 S)
 have hM(x:Orbit N): g x= inner ℂ (Dial.mateK _) (acts (f (drawn l x)) (denZ Q (Γ).U l x)):= congrArg (fun u=> inner ℂ (Dial.mateK _) u) (hh x).symm
 have hv: partitionZ Q (Γ).U l=sharpWeight M (Γ).U ((Y).meter.a t) Hp:=by rw [partitionZ, show denZ Q (Γ).U l= _ from funext ((Y).whole i k)]
 rw [h]; change (∫ x:Orbit N,g x ∂city _) / _= (∫ x:Orbit N,_ ∂city _) / partitionZ Q (Γ).U l; rw [hv,funext hM]
#print axioms correct_price
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
