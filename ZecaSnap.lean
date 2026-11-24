import ZecaGem
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "κ"=> P.calibration
local notation "ℓ"=> (κ).ℓ
local notation "R"=> ruler P.par.block
local notation "Μ"=> timeMesh P.par
local notation "N"=> notch (timeMesh P.par)
local notation "Γ"=> marks (timeMesh P.par)
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "X"=> P.ColorHil j x

local notation "E"=> (P.physicalEnergy j x).E

variable (D:P.Apron)
local notation "ET" => (P.seasons j x).E
local notation "G" => P.ManyF j x
local notation "r"=> D.realWidth P j

def Snap (s w:ℕ)(F:P.Test)(T:(P.ManyF j x).Op) :=
 ∃ Y:(P.ColorHil j x).Op, P.Fired j x s w F Y ∧ P.coffer j x Y=T
def Cash (s w:ℕ)(F:P.Test)(e:ℝ) := ∃ Y:(P.ColorHil j x).Op, P.Fired j x s w F Y ∧ ‖Y‖≤e

variable {P j x} {s w u :ℕ} {F T:P.Test}
namespace Cash
variable {a b:ℝ} (p:P.Cash j x s w F a)
include p
lemma mul (q:P.Cash j x s u T b) : P.Cash j x s (w+u) (F * P.shifts j w T) (a*b):=by
 obtain ⟨Y,h,g⟩:=p;obtain⟨Z,m,n⟩:=q
 exact ⟨_,h.mul m,(norm_mul_le _ _).trans (mul_le_mul g n (norm_nonneg _) ((norm_nonneg _).trans g))⟩
lemma left (u:ℕ): P.Cash j x s (u+w) (P.shifts j u F) a:=by
 obtain ⟨Y,h,g⟩:=p
 exact ⟨_,h.left u, (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) ((P.physicalEnergy j x).shrinks _)).trans g)⟩
lemma right (u:ℕ): P.Cash j x s (w+u) F a:=by
 obtain ⟨Y,h,g⟩:=p
 exact ⟨_,h.right u, (norm_mul_le _ _).trans ((mul_le_of_le_one_right (norm_nonneg _) ((P.physicalEnergy j x).shrinks _)).trans g)⟩
end Cash
namespace Snap
variable {Y Z:(P.ManyF j x).Op} (p:P.Snap j x s w F Y)
include p
lemma smul (z:ℂ): P.Snap j x s w (z • F) (z • Y):=by
 obtain ⟨Y,m,rfl⟩:=p
 exact ⟨_,m.smul z,map_smul ..⟩
lemma add (q:P.Snap j x s w T Z):P.Snap j x s w (F+T) (Y+Z):=by
 obtain ⟨Y,m,rfl⟩:=p; obtain ⟨Z,n,rfl⟩:=q
 exact ⟨_,m.add n,map_add ..⟩
lemma sub (q:P.Snap j x s w T Z):P.Snap j x s w (F-T) (Y-Z):=by
 obtain ⟨Y,m,rfl⟩:=p; obtain ⟨Z,n,rfl⟩:=q
 exact ⟨_,m.sub n,map_sub ..⟩
lemma unique (q:P.Snap j x s w F Z):Y=Z:=by
 obtain ⟨Y,m,rfl⟩:=p; obtain ⟨Z,n,rfl⟩:=q
 rw [m.unique n]
lemma norm_cash {e:ℝ}(q:P.Cash j x s w F e):‖Y‖≤e:=by
 obtain ⟨Y,m,rfl⟩:=p; obtain ⟨Z,n,v⟩:=q
 rw [m.unique n]
 exact (P.coffer_pay ..).trans v
end Snap
namespace Apron
variable (P j x) {a b:ℝ}
local notation "m"=>D.zoom P s j
lemma snap (u:D.s≤ s) {d:ℤ}
 (h:(D.zoom P s j:ℤ)≤d)(t:d+D.zoom P s j≤w)
 (i:bell Μ s d=a)(o:bell Μ s w=a+b):
 P.Snap j x s w (P.shifts j d (D.full P s)) (P.ruby j x D 0 a b):=by
 have e:= D.fired_spot P j x u d h t
 rw [i,o,add_sub_cancel_left] at e
 exact ⟨_,e,P.coffer_innerCut ..⟩
lemma cash_slice (u:D.s≤ s) {d:ℤ}
 (h:(D.zoom P s j:ℤ)≤d)(t:d+D.zoom P s j≤w):
 P.Cash j x s w (P.shifts j d (D.full P s)) ‖D.engine P j x‖:=by
 exact ⟨_,D.fired_spot P j x u d h t, bun_le (M:=P.ColorHil j x)
     ((P.physicalEnergy j x).shrinks _) ((P.physicalEnergy j x).shrinks _) _⟩

lemma zoom_here:D.zoom P D.s j = D.u j:=by rw [zoom,Nat.sub_self,pow_zero,one_mul]
lemma full_here:D.full P D.s=D.F:=by rw [full,Nat.sub_self];rfl
lemma snap_here {d:ℤ}
 (h:(D.u j:ℤ)≤d)(t:d+D.u j≤w)
 (i:bell Μ D.s d=a)(o:bell Μ D.s w=a+b):
 P.Snap j x D.s w (P.shifts j d D.F) (P.ruby j x D 0 a b):=by
 have p:=D.snap P j x le_rfl (show (↑(D.zoom P D.s j):ℤ)≤d by rwa [zoom_here])
     (w:=w) (by rwa [zoom_here]) i o
 rwa [full_here] at p
end Apron
