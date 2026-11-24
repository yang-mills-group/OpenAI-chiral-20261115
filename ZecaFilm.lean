import ZecaFired
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
-- Distances from APRON centre to left and right end; pitch in fermion unit.
-- (even centeredQ has actual displacement convention, z the pose)
def innerCut (a b:ℝ) (T:(P.ColorHil j x).Op): (P.ColorHil j x).Op :=
 E (a-D.realWidth P j).toNNReal*T*E (b-D.realWidth P j).toNNReal
abbrev rawCat(g:P.VMark)(a b:ℝ):= P.innerCut j x D a b
 (P.charter j x g (D.engine P j x))
def ruby(g:Vantage)(a b:ℝ): (P.ManyF j x).Op:=
 (P.seasons j x).E (a-D.realWidth P j).toNNReal *
   P.tableau j x g (D.engine P j x) *
 (P.seasons j x).E (b-D.realWidth P j).toNNReal

namespace Fired
open Apron
local notation "λ_" n:max d:max => bell (timeMesh P.par) n d
variable {P j x} {w m n:ℕ} {F:P.Test} {U:(P.ColorHil j x).Op}

variable {D}
lemma fillCut (v:r=bell Μ n m) (d:ℤ) (h:(m:ℤ) ≤ d)(t:d+m≤w)
 (q:P.Fired j x n (m+m) (P.shifts j ((m:ℤ)-d) F) U):
    P.Fired j x n w F (P.innerCut j x D (λ_ n d) ((λ_ n w)-(λ_ n d)) U):=by
 let y:ℕ := (d-m).toNat
 let z:ℕ := ((w:ℤ)-(d+m)).toNat
 have hy:(y:ℤ)=d-m:=Int.toNat_of_nonneg (by omega)
 have hz:(z:ℤ)=(w:ℤ)-(d+m):=Int.toNat_of_nonneg (by omega)
 have p1:(bell Μ n d-r).toNNReal= whenly Μ n y:=by

    have :bell Μ n d-r = ((whenly Μ n y):ℝ):=by
       rw [v]; unfold bell whenly
       push_cast; rw [←_root_.sub_mul]; congr 1; exact_mod_cast hy.symm
    rw [this,Real.toNNReal_coe]

 have p2:(bell Μ n w-bell Μ n d-r).toNNReal= whenly Μ n z:=by
    have :bell Μ n w-bell Μ n d-r = ((whenly Μ n z):ℝ):=by
       rw [v]; unfold bell whenly
       push_cast; rw [←_root_.sub_mul,←_root_.sub_mul,sub_sub]; congr 1; exact_mod_cast hz.symm
    rw [this,Real.toNNReal_coe]
 have e:= (q.left y).right z
 rw [P.shifts_sum, show (y:ℤ)+(m-d)=0 from by omega,P.shifts_zero,
      show y+(m+m)+z=w from by omega] at e
 unfold innerCut
 rw [p1,p2]; exact e
end Fired
namespace Apron
variable {w n:ℕ} (u:D.s≤n)
local notation "m"=> D.zoom P n j
include u
lemma fired_photo (y:Cover)(h:(D.zoom P n j:ℤ) ≤ y j)(t:y j+m≤w):
 P.Fired j x n w (P.chartAll y (D.full P n))
   (P.rawCat j x D (P.vtile n y) (bell Μ n (y j))
        (bell Μ n w-bell Μ n (y j))):=by
 obtain ⟨f,p,g,e⟩:= D.transported P j x n u y
 exact Fired.fillCut (D.zoom_bell P j n u).symm _ h t
       ⟨add_pos (D.zoomP P j n) (D.zoomP P j n),f,p,g,e⟩

lemma fired_spot (d:ℤ)(h:(D.zoom P n j:ℤ) ≤ d)(t:d+m≤w):
 P.Fired j x n w (P.shifts j d (D.full P n))
   (P.innerCut j x D (bell Μ n d)
        (bell Μ n w-bell Μ n d) (D.engine P j x)):=by
 obtain ⟨f,p,g⟩:= D.full_realizes P j n u
 have hv:P.voxTest j n f.val ∈enclave κ:= p ▸ P.shifts_keep j _ (D.fullColor P n)
 have :P.Fired j x n (m+m) (P.shifts j ((m:ℤ)-d) (P.shifts j d (D.full P n)))
         (D.engine P j x):=by
    rw [P.shifts_sum,sub_add_cancel]
    exact ⟨add_pos (D.zoomP P j n) (D.zoomP P j n),f,hv,p,congrArg (Φ ·) (Subtype.ext g)⟩
 exact Fired.fillCut (D.zoom_bell P j n u).symm _ h t this
end Apron
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
