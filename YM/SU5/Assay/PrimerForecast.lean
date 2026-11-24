import SatinFixedContrastNovember4
import YM.SU5.Assay.StoreFloor
import YM.SU5.Assay.PressedWard
import YM.SU5.Assay.Notice
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
variable {τ:ℝ}
variable (p:P.Flight j s x k w Z n τ a f U D r l)
open Aria Six Germ Alliance
namespace Flight
/-- Canonical product of the *actual* pure marginal readings, even for
 normalized biased receipts on the regulator. The proof uses local bills and
 does not need Ward control on tests larger than the box. -/
def primer := (comparison_exists K p.pressing p.pressed_one).choose
lemma prices:Comparison K p.pressing p.primer:= (comparison_exists K p.pressing p.pressed_one).choose_spec
lemma forced (X:P.Test→ₗ[ℂ]ℂ)(h:Comparison K p.pressing X):X=p.primer:=h.unique K p.pressing p.prices
lemma quote (g:P.Test){y:ℝ}(h:g∈B Z)(u:pay g.val y):
    ‖A r l (Q g) - W g‖≤τ*y ∧ ‖p.pressing g-W g‖≤τ*y:=p.cost g h _ u
variable (q:P.Balcony j k w Z a n f U D d)(h:f∈enclave P.calibration)
variable {M N:Set Vantage}(b₁:P.StoreFloor s M Z)
include h q
lemma snuffed (t:g∈B Z)(u:P.GFlame g): p.pressing g=0:=by
 obtain ⟨c,g₀,w,t₀⟩:=u
 have z:=p.color_price q h t g₀
 rw [t₀,map_smul,smul_eq_mul] at z
 have v:(c-1)*p.pressing g=0:=by rw [_root_.sub_mul,z,one_mul,sub_self]
 exact (mul_eq_zero.mp v).resolve_left (sub_ne_zero.mpr w)
include b₁
lemma extinguish (u:g∈P.Spent s M): p.pressing g=0:=by
 exact Submodule.span_induction (p:=fun g _=>p.pressing g=0) (fun _ z=>p.snuffed q h (b₁.auth.mp z.1) z.2) p.pressing.map_zero
   (fun i j _ _ h u=>by rw [map_add,h,u,add_zero]) (fun z g _ h=>by rw [map_smul,h,smul_zero]) u
include p in
lemma cut (u:g∈P.Spent s M): A r l (Q g)=0:=p.zero_raw (p.extinguish q h b₁ u)
lemma paid_forecast {c:Bool}{x:P.Spectrum0 3} (t:N⊆M)(v:P.Payout x s N g c):p.primer g=0:=by
 obtain ⟨z,u₁,_,e,u⟩:=v.loose
 rw[e.1,map_list_sum]; apply List.sum_eq_zero
 intro m hm
 obtain ⟨_,m,rfl⟩:=List.mem_map.mp hm
 obtain ⟨i,r,rfl⟩:= List.mem_map.mp m
 let w:= e.2 i r
 change p.primer (i.1*i.2)=0
 rw [p.prices.factors _ _ w.1 w.2.1,p.prices.link _ w.1,p.extinguish q h b₁ (Spent.mono t (u i r).1),zero_mul]
end Flight
#print axioms Flight.paid_forecast
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
