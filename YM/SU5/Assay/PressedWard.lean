import YM.SU5.Assay.Usher
import YM.SU5.Selected.Euro.Mingle
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
local notation "F"=> σ (k-n-a) (P.riposte j a f)
local notation "G"=> σ (k+w+n) f
variable {τ:ℝ}
variable (p:P.Flight j s x k w Z n τ a f U D r l)
namespace Flight
/-- Reading relative to viewer unit. Remembers exact raw stance of POV at this
 budget. No probability statement about the finite density. -/
def pressing: P.Test→ₗ[ℂ]ℂ where
 toFun g:= A r l (Q g)/ A r l (Q 1)
 map_add' i y:=by
   have h:Q (i+y)=Q i+Q y:=by unfold viewFrom;rw [mul_add,add_mul]
   rw [h,←add_div]
   exact congrArg (· / _) (sharp_plus Y H _ (Q i).property (Q y).property p.tickets)
 map_smul' c i:=by
   have h:Q (c•i)=c•Q i:=by unfold viewFrom;rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]
   rw [h]; exact (congrArg (· / A r l (Q 1)) (sharp_scale Y H s (Q i).val c (m₀ r) (h₀ l))).trans (mul_div_assoc ..)
lemma pressed_one:p.pressing 1=1:=div_self p.lock
include p in
lemma ward_g (q:P.Balcony j k w Z a n f U D d)(u:f∈S)(h:g∈B Z)(t:Cover→SU.E):
 A r l (Q (pennant K t g))=A r l (Q g):=by
 have t₁:F∈S:=P.shifts_keep _ _ (riposte_keeps u)
 have t₂:G∈S:=P.shifts_keep _ _ u
 have f': pennant K t (F)=F:= (colorFixed K).mp t₁ t
 have g': pennant K t (G)=G:= (colorFixed K).mp t₂ t
 have ht: Q (pennant K t g)=pennant K t (Q g):=by unfold viewFrom;rw[map_mul,map_mul,f',g']
 let Z₀:=U∪Z∪D
 rw [ht]; exact (Selection.Mingle.sharp_gauge Y H s _ _ t p.local_lic.hosp
   ⟨p.tickets.depth,p.tickets.enters⟩ (pennantTrace K Z₀ t (q.budget h))).symm
lemma color_price (q:P.Balcony j k w Z a n f U D d)(u:f∈S)(h:g∈B Z)(t:Cover→SU.E):p.pressing (pennant K t g)=p.pressing g:=
 congrArg (· / A r l (Q 1)) (p.ward_g q u h t)
lemma zero_raw (h:p.pressing g=0): A r l (Q g)=0:=(div_eq_zero_iff.mp h).resolve_right p.lock
end Flight
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
