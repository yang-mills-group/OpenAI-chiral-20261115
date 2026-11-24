import YM.SU5.Assay.StencilSeat
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
variable(P j) (a n w:ℕ)
/-- Raw viewer biasing of `g` (caliper [k,k+w]) by `f` (BEntry([0,a])). -/
def viewFrom (k:ℤ)(f g:P.Test):P.Test:=
 σ (k-n-a) (P.riposte j a f) *g * σ (k+w+n) f
/-- Fully charged mark of sighting beginning at the start of the first caliper. -/
private def panelled (f g:P.Test):P.Test:=
 (P.riposte j a f * σ (a+n:ℕ) g)* σ (a+n+w+n:ℕ) f
local notation "J"=> P.panelled j a n w
private lemma panel_shift(k:ℤ)(f g:P.Test): σ (k-n-a) (J f g)=P.viewFrom j a n w k f (σ k g):= by
 unfold panelled viewFrom
 rw [map_mul,map_mul,P.shifts_sum,P.shifts_sum]
 rw [show k-n-a+↑(a+n)=k by omega, show k-n-a+↑(a+n+w+n)=k+w+n by omega]
variable {P j a w}(s)
local notation "d"=> (a+n+w+n+a)
lemma viewFrom_keeps (k:ℤ)(t:f∈S)(h:g∈S): P.viewFrom j a n w k f g ∈ S:=
 Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (P.shifts_keep j _ (riposte_keeps t)) h) (P.shifts_keep _ _ t)
private lemma markPanel (p:P.BEntry j a f)(q:P.BEntry j w g): P.BEntry j d (J f g):=
 ((((p.riposte.right (Nat.le_add_right a n)).concat q).right (Nat.le_add_right _ n)).concat p)
local notation "C"=> P.guardPlate j s n
local notation "β"=> μ j s
private lemma readPanel (p:P.BEntry j a f)(q:P.BEntry j w g):
 β d (J f g)=star (β a f)*C*β w g*C*β a f:=by
 let h:=p.riposte.right (Nat.le_add_right a n)
 unfold panelled guardPlate
 rw [meanBox_concat s ((h.concat q).right (Nat.le_add_right _ n)) p,meanBox_right s (h.concat q),meanBox_concat s h q,meanBox_right s p.riposte,meanBox_star s p]
private lemma viewPanel (p:P.BEntry j a f)(q:P.BEntry j w g):
 P.E s ((J f g).val)=P.framed j s w n g (β a f (Ω j)):=by
 rw [←meanBox_earns s (markPanel n p q),readPanel s n p q]
 let B:=β a f
 let U:=β w g
 change inner ℂ (Ω j) (B.adjoint (C (U (C (B (Ω j)))))) =
    inner ℂ (C (B (Ω j))) (U (C (B (Ω j))))
 have h:(C).adjoint=C:=P.heats_star j (Ν s n)
 set y:=C (B (Ω j));change _=inner ℂ (C (B (Ω j))) (U y)
 rw [ContinuousLinearMap.adjoint_inner_right,← h,ContinuousLinearMap.adjoint_inner_right,h]

/-- Mean pricing of the regulator sighting. The measured claim `g` in its
 actual position, and the viewer positions also. -/
lemma viewFrom_mean {k:ℤ}(p:P.BEntry j a f)(q:P.BEntry j w (σ (-k) g)):
 P.E s ((P.viewFrom j a n w k f g).val)=P.framed j s w n (σ (-k) g) (β a f (Ω j)):=by
 let A:=σ (-k) g
 have h:P.viewFrom j a n w k f g=σ (k-n-a) (J f A):=by
   unfold A;rw [panel_shift,P.shifts_sum,add_neg_cancel,P.shifts_zero]
 rw [h,P.E_invariant]; exact viewPanel s n p q
lemma view_caliper {k:ℤ}(p:P.BEntry j a f)(q:P.BEntry j w (σ (-k) g)):
 P.BEntry j d (σ (-(k-n-a)) (P.viewFrom j a n w k f g)):=by
 let A:=σ (-k) g
 have h:P.viewFrom j a n w k f g=σ (k-n-a) (J f A):=by
   unfold A;rw [panel_shift,P.shifts_sum,add_neg_cancel,P.shifts_zero]
 rw [h,P.shifts_sum,neg_add_cancel,P.shifts_zero];exact markPanel n p q
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
