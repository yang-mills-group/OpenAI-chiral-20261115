import SatinFixedContrastNovember4
import YM.SU5.Assay.PrimerForecast
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
variable {P:Spine}{j:Axis}{s v w:ℕ}{f g:P.Test}
local notation "Λ"=> P.par
local notation "Y"=> P.run
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "b"=> ruler (Λ).block
local notation "V"=> P.law
local notation "L"=> (Λ).R.L.val
local notation "π"=> P.history
local notation "Qt"=> P.projection.clipped
local notation "C₀"=> P.room j
local notation "σ"=> P.shifts j

local notation "μ"=> P.meanBox
local notation "ν"=> P.euclOp
local notation "T"=> P.shiftOp
local notation "Ν"=> whenly (timeMesh (Λ))
local notation "Ω"=> P.floorVec
local notation "S"=> enclave K
local notation "B" M:max=> bay K M true
variable {k:ℤ}{Z U D:Finset Cover}{x:P.Spectrum0 j}{a n r l:ℕ}{d δ:ℝ}
local notation "Q"=> P.viewFrom j a n w k f
local notation "E"=> P.E s
local notation "W"=> P.singleState j s x
local notation "m₀"=> P.period
local notation "h₀"=> P.cutoff
local notation "A"=>P.sterling s
open Aria Six Germ Alliance
structure FloorService (P:Spine)(j:Axis)(s:ℕ)(x:P.Spectrum0 j)(M:Set Vantage)(k:ℤ)(w:ℕ)(Z:Finset Cover)(n:ℕ)(δ:ℝ)(a:ℕ)(f:P.Test)(U D:Finset Cover)(d:ℝ):Prop where
 agency:P.StoreFloor s M Z
 witness:P.WitnessSleeve j s x k w Z n (δ/2) a f
 literal:P.Balcony j k w Z a n f U D d
 purchase: ∀ᶠ i in atTop,∀l,legacy P.run (P.period i) (P.cutoff l) → P.Flight j s x k w Z n δ a f U D i l
variable {M:Set Vantage}
variable (x n) in
lemma FrameFloor.witnesses (R:P.Register)(p:P.FrameFloor s M){α β:ℝ}(q:P.FrameFace j s M α β k w)(v:0<δ):
 ∃ Z a f U D d,P.FloorService j s x M k w Z n δ a f U D d:=by
 obtain ⟨Z,u⟩:=p.stores
 obtain ⟨a,f,y⟩:=(u.space q).witness s x R n (half_pos v)
 obtain ⟨U,D,d,t⟩:=balcony y.toSleeve y.borrowed n
 refine ⟨Z,a,f,U,D,d,u,y,t,?_⟩
 have e:=y.depart t (half_pos v)
 rwa [add_halves] at e
namespace FloorService
variable(p:P.FloorService j s x M k w Z n δ a f U D d)
include p
variable(e:P.Flight j s x k w Z n δ a f U D r l)
local notation "Φ"=> P.pinFoot s
local notation "τ"=> P.tock s
lemma credential (u:P.asked_at s g M):
  g∈B Z∧ P.BEntry j w (σ (-k) g) ∧ Q g∈B (U∪Z∪D) ∧
  (g∈S→Q g∈S)∧ ((∀z∈Φ U,z j≤ τ k - τ n)∧(∀z∈Φ D,τ (k+w)+τ n≤z j)):=
 let v:=p.agency.auth.mp u
 ⟨v,p.witness.claim v,p.literal.budget v,p.witness.presses_color,p.literal.space⟩
lemma earned (u:P.asked_at s g M){y:ℝ}(h:pay g.val y):
 ‖A r l (Q g)-W g‖≤δ*y ∧ ‖e.pressing g-W g‖≤δ*y:=e.cost _ (p.agency.auth.mp u) _ h
lemma cancels (u:g∈P.Spent s M):W g=0 ∧ A r l (Q g)=0∧ e.pressing g=0:=
 ⟨Cinder.value s (Spent.clips u) x, e.cut p.literal p.witness.draws p.agency u,e.extinguish p.literal p.witness.draws p.agency u⟩
lemma impartial {N:Set Vantage}{c:Bool} {z:P.Spectrum0 3} (t:N⊆M)(v:P.Payout z s N g c):
   e.primer g=0 ∧ P.paperSplit s z g=0:=⟨e.paid_forecast p.literal p.witness.draws p.agency t v,v.compare⟩
end FloorService
#print axioms FrameFloor.witnesses
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
