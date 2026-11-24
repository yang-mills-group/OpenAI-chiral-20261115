import YM.SU5.Assay.WitnessSleeve
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
variable(P j)(k:ℤ)(w:ℕ)(Z:Finset Cover)(a n:ℕ)(f:P.Test)
local notation "F"=> (σ (k-n-a) (P.riposte j a f))
local notation "G"=> (σ (k+w+n) f)
local notation "Q"=> P.viewFrom j a n w k f
local notation "B" D:max=> bay K D true
/-- A literal posing licence for the regulator viewer at the given support
 with the given calipers. U and D are the early & late viewer bills. -/
structure Balcony (U D:Finset Cover)(d:ℝ):Prop where
 pre: P.Sleeve j (k-n-a) a U
 main: P.Sleeve j k w Z
 post: P.Sleeve j (k+w+n) a D
 left:F∈B U
 right:G∈B D
 positive:0<d
 debit: pay (F).val d
 balance: pay (G).val d
variable {P j k w Z a n f}{U D:Finset Cover}{d:ℝ}
lemma BEntry.sleeved (q:P.BEntry j a f)(k:ℤ): ∃U,P.Sleeve j k a U∧σ k f∈B U:=by
 obtain ⟨p,U,h,v⟩:=q
 have t:Between K j (b*k) (b*(k+a)) (plow K j k U):= by
   simpa only [mul_add,add_zero,show ruler (K).B=b from rfl] using Between.relocate K j v k
 exact ⟨_,⟨p,t⟩,P.shifts_support j k _ h⟩
lemma balcony (q:P.Sleeve j k w Z)(p:P.BEntry j a f)(n:ℕ):∃U D d,P.Balcony j k w Z a n f U D d:=by
 obtain ⟨U,h₁,v⟩:=p.riposte.sleeved (k-n-a)
 obtain ⟨D,h₂,t⟩:=p.sleeved (k+w+n)
 obtain ⟨d,e⟩:= Journey.valuation Y H v
 obtain ⟨z,g⟩:= Journey.valuation Y H t
 exact ⟨U,D,max 1 (max d z),h₁,q,h₂,v,t,one_pos.trans_le (le_max_left ..),
  fun x y=> (e x y).trans ((le_max_left ..).trans (le_max_right ..)), fun x y=> (g x y).trans ((le_max_right ..).trans (le_max_right ..))⟩
namespace Balcony
variable(p:P.Balcony j k w Z a n f U D d)
include p
lemma budget (t:g∈B Z): Q g∈ B (U∪Z∪D):=by
 have h₁:F∈B (U∪Z∪D):= tallerBay K U _ ((subset_union_left (s₂:=Z)).trans subset_union_left) p.left
 have h₂:g∈B (U∪Z∪D):= tallerBay K Z _ ((subset_union_right (s₁:=U)).trans subset_union_left) t
 have h₃:G∈B (U∪Z∪D):= tallerBay K D _ subset_union_right p.right
 exact (B (U∪Z∪D)).mul_mem ((B (U∪Z∪D)).mul_mem h₁ h₂) h₃
lemma funding {x:ℝ}(h:pay g.val x):pay (Q g).val (d*x*d):= pay_mul (pay_mul p.debit h) p.balance
end Balcony
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
