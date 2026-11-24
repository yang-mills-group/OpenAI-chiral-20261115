import GaugeFieldConstruction.AcrossWallet
import GaugeFieldConstruction.AcrossVolume
import GaugeFieldConstruction.AcrossL1
import GaugeFieldConstruction.AcrossRouting
import YM.CF.Buffered.DonorGram
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
local notation "Γ" => P.par
local notation "Y" => P.run
local notation "B" => P.large
open AcrossLands Tapestry Preparation AcrossShots
variable {n:ℕ}
-- Exposure accountability across differently sized volumes.
-- `RibbonCalendarSt` extends the main current canonical P construction rather than claiming
-- replacement. All v arguments at tapeDepth = **one depth** independent of volume. Supports:
-- `VolumeInk.origin` at all of them, schedule uses narrower class for estimator.
-- For `PassOutlinesSt`, inspecting authenticity of the original local Advert/Mark; not rerunning
-- EVERY Fashion/Plaid calibration with distorted meters from this tape. See also the construction notes.
open Heat Buffered Dial Tapestry.Fashion Py.Rate.Branch
variable (R:P.Register){ε:ℕ→ℝ}(E:IntervalsSchedule P n v ε)

local notation "Kβ" i:max => (P.run.headIn i)
local notation "ℓσ" i:max s:max=> Journey.side Y i s
local notation "X☆" i:max k:max=> ((Y).voyage i).X ((Y).uv k)
local notation "Cℓ" i:max s:max=> ((Y).voyage i).CapeT s
local notation "Μλ" i:max k:max=> Actual (Y).meter ((Y).voyage i).funds ((Y).voyage i).CapeT (Preparation.gaugeFreq Γ ((Y).tile*(Γ).M)) ((Y).uv k)
open AcrossShots Tapestry.Ward LocalLimit
include E
lemma independentCash (t:ℕ)(m:Side)(h:∃ c:Side,mesh m P.par.R.L t=c*P.par.M ∧ n≤ c.val) :
    VolumeInk P.par.K P.par.U (P.run.meter.a t) (v t) (mesh m P.par.R.L t):= by
 obtain ⟨c,g,hc⟩:=h; rw [g]; exact at_volume (L:= (Γ).J) P.par.direct (E.land.min_size.trans hc) ((((Y).voyage 0).paths t).paid.can.pole t) (((E.norms t).cashM c hc).2)
-- In particular for sufficiently large m=c*P.par.M, threshold independent t.
lemma openVolumes (t:ℕ)(c:Side)(h:n≤ c.val) : VolumeInk P.par.K P.par.U (P.run.meter.a t) (v t) (mesh (c*P.par.M) P.par.R.L t):= independentCash P v E t (c*P.par.M) ⟨_,Month.ruler .., h.trans (mesh_ge ..)⟩


abbrev FrontalAccessSt (m:Side)(z n:ℕ):Prop:= ∃ c: Side,mesh m P.par.R.L z=c*P.par.M ∧ n≤ c.val
structure PassOutlinesSt (t:ℝ)(r:Bet ((Y).uv k)) : Prop where
 near : |t|≤ε (P.run.uv k)
 wallet : P.WalletDebtSt (ε:=ε) v i k t r
 -- actual dome, calibrated in exact-β stencil at each resolution s, then quote with NEW bare & ticket
 stamped (s:ℕ)(p:s≤P.run.uv k)(S:BillOfWork)(b:ℝ)(A:P.Effect)(h:Pocket P.calibration S s b A): ‖P.torqueBare v A i k-taking P.run P.large i k A‖≤ε (P.run.uv k)*(cloudSpan s S*b) ∧
    ‖priceHere P A i k r s - taking P.run P.large i k A‖ ≤ ε (P.run.uv k) * (cloudSpan s S*b)
 -- any chosen such lower Mark can really advance, no retag, not just arithmetic reweight. Support with that generated mortgage.
 lower_tape (s:ℕ)(p:s≤ P.run.uv k)(S:Finset Cover)(A:Mark (Journey.side Y i s))(e:AtSupport false (Satin.region S (Journey.side Y i s)) A): ∃ F U, PromptsTape P r A S F U ∧ let T:Mark (side Y i ((Y).uv k)):= F ((Y).uv k); let a(v:Pane (side Y i ((Y).uv k))):=T (v,v); Envelope a ∧ carryCostSt (i:=i) P r s A=AcrossLands.position (mesh ((Y).ir i) (Γ).R.L ((Y).uv k)) (Γ).U ((Y).meter.a ((Y).uv k)) (v ((Y).uv k)) a
   
lemma passesSTELLA (a:P.shoulderTape n ε v i k) : ∃ t r,PassOutlinesSt P (i:=i) (k:=k) (ε:=ε) v t r:=by
 obtain ⟨t,h,r,u⟩:=a.2.2
 exact ⟨_,_,h,u, fun s p S b A p' => ⟨P.uniformMargin v E A p'.funded S b p' i k a p,P.observingSt v E a.1 u s p A S b p'⟩,fun s p S A e=> P.names_at_tape v r a.1 u p S A e⟩
-- Not claiming ALL periods qualify on spares. Get an unbounded collection still after adding actual aperture qualifications (same-mask Normalizes).
lemma spareTape (k:ℕ)(h:¬ ∃ r,P.tapeDepth r=k) : ∃ᶠ i:ℕ in atTop, FrontalAccessSt P ((Y).ir i) k n ∧ (Y).eligible i k (v k) (ε k):=by
 have he : ∀ᶠ i in atTop,(Y).permitLand i k n:=by
    filter_upwards[(Y).late_volume n] with i p; obtain ⟨c,v,h⟩:=p; unfold Course.permitLand; rw [v, Month.ruler]; exact ⟨_,rfl,h.trans (mesh_ge ..)⟩
 exact he.and_frequently (E.spares k h)

abbrev CoupletCalendar (f:P.Effect) := Sound.Couplet P.period id (fun i t=>torqueBare P v f i (P.circuitDepth i t)) (fun i=>rowTake Y B i R.exhibition f) (vistaTake Y B (P.talks R) f) (fun z=> ∀ᶠ i in atTop, legacy Y (P.period i) (P.circuitDepth (P.period i) (z i)))
local notation "κ" => (P.tapeₖ)
local notation "ρ" => P.tapeᵢ
local notation "S_ℓ" => P.shoulderTape n ε v
omit E
structure RibbonCalendarSt (v ε:ℕ→ℝ) (n:ℕ) : Prop where
 calendar : IntervalsSchedule P n v ε
 -- at ALL depths, broad geometry. In particular all multiples as listed.
 independent (m:Side)(z:ℕ)(h:P.FrontalAccessSt m z n) : VolumeInk P.par.K P.par.U (P.run.meter.a z) (v z) (mesh m P.par.R.L z)
 multiples (c:Side)(z:ℕ)(h:n ≤ c.val) : VolumeInk P.par.K P.par.U (P.run.meter.a z) (v z) (mesh (c*P.par.M) P.par.R.L z)
 passes (i k:ℕ)(p:P.shoulderTape n ε v i k) : ∃ t r,PassOutlinesSt P (i:=i) (k:=k) (ε:=ε) v t r
 spares (k:ℕ)(h:¬ ∃ r,P.tapeDepth r=k) : ∃ᶠ i:ℕ in atTop, FrontalAccessSt P ((Y).ir i) k n ∧ (Y).eligible i k (v k) (ε k)
 -- at every fixed period we use a different UV subscript; immutable law. If asking for volume# limit FIRST then UV, no claim on convergence.
 uv (i:ℕ): ∀ᶠ k in atTop, legacy P.run i (P.circuitDepth i k) ∧ P.shoulderTape n ε v i (P.circuitDepth i k)
 ir (u:ℕ→ℕ)(h:∀ᶠ i in atTop, legacy Y (P.period i) (P.circuitDepth (P.period i) (u i))): Tendsto (fun i=>P.circuitDepth (P.period i) (u i)) atTop atTop ∧
         ∀ᶠ i in atTop,P.shoulderTape n ε v (P.period i) (P.circuitDepth (P.period i) (u i))
 existing : ∀ᶠ r in atTop,P.shoulderTape n ε v (P.tapeᵢ (2*r)) (P.tapeₖ (2*r))
 -- genuine UV & strict distinct from old path's beta on even movers (doesn't claim outside)
 counts (i:ℕ): StrictMono (P.circuitDepth i) ∧ StrictMono (fun j=>P.run.uv (P.circuitDepth i j))
 other : ∀ᶠ i:ℕ in atTop, P.run.headIn (P.tapeᵢ (2*i)) (P.tapeDepth (2*i)) < v (P.tapeDepth (2*i))
 estimates (s:ℕ)(A:P.Effect)(p:A∈shorter P.Test s): CoupletCalendar P v R A ∧
       Tendsto (fun t:ℕ=>torqueBare P v A (P.tapeᵢ (2*t)) (P.tapeₖ (2*t))) atTop (𝓝 (vistaTake Y B (P.talks R) A))

lemma compileCalendar : ∃ v ε n, RibbonCalendarSt P R v ε n:=by
 obtain ⟨n,A⟩:= territories P.par.J P.par.direct
 obtain ⟨ε,v,E⟩:= P.lowering A
 refine ⟨v,ε,n,E,fun m k x=> P.independentCash v E k m x, fun c z h=> P.openVolumes v E z c h, fun _ _ p=>P.passesSTELLA v E p, P.spareTape v E,fun i=>(cadence Y _ (P.circuitMono i) i).and (columnPay P v E _),fun _ p=>P.jointPays v E p, P.thinPays v E, fun i=> ⟨P.circuitMono _,(P.independentRead i).2⟩,?_,fun _ p q=>P.supportsRead v R E p q⟩
 filter_upwards [P.thinPays v E] with i hi; have he:= E.tape _ ((P.circleMain i).symm ▸ hi.1); rw [P.circleMain] at he; exact he.1
#print axioms compileCalendar
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
