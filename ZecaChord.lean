import SatinThinFusionTrumpets
import ZecaVat
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets

variable (P: Spine)(x:P.Spectrum0 3)
local notation "K" => P.calibration
local notation "T" => timeMesh P.par
variable (A:P.Apron)(n:ℕ)
def ladder : P.Apron where
 s:=A.s
 F:= P.tubaField A.s A.F n
 S:= P.tubaStencil A.S n
 u:=fun i=> A.u i + n
 pos:=fun j=>Nat.add_pos_left (A.pos j) _
 realM:=P.tuba_real A.s _ _ A.realM
 shelter:=fun j=> P.tubaShelter j (A.shelter j) n
 bay:=P.tuba_bay A.s _ _ _ A.bay
local notation "r"=> A.realWidth P 3
local notation "δ"=> bell (timeMesh P.par) A.s 1
local notation "e"=>whenly (timeMesh P.par) A.s 1
local notation "W" n:max=> P.ladder A n
lemma ladder_width (j:Axis): (W n).realWidth P j= A.realWidth P j + n*δ:=by
 unfold Apron.realWidth bell; simp only [ladder]; push_cast; ring
lemma rungs_zero (a b:ℝ)(i:r ≤ a)(u:r ≤ b):
 P.ruby 3 x (W 0) 0 a b=P.ruby 3 x A 0 a b:=by
 let h:=(W 0).pureVat P 3 x A.s (A.u 3) a b rfl
        (le_refl _) i u
 exact h.unique (A.pureVat P 3 x _ _ _ _ rfl le_rfl i u)

lemma rungs_next (a b:ℝ)
 (i:(W (n+1)).realWidth P 3 ≤ a)(u:(W (n+1)).realWidth P 3 ≤ b):
 P.ruby 3 x (W (n+1)) 0 a b= (duration e)⁻¹ •
    (P.ruby 3 x (W n) 0 (a+δ) (b-δ) - P.ruby 3 x (W n) 0 a b):=by
 let w:=A.u 3+(n+1)
 have h:=(W (n+1)).pureVat P 3 x A.s w a b rfl (le_refl _) i u
 apply h.unique
 rw [show (W (n+1)).F=(duration e)⁻¹ • (P.shifts 3 1 (W n).F-(W n).F) from ?_]
 · have ht:(W n).u 3 + 1=w:= Nat.add_assoc ..
   exact (((W n).vat P 3 x A.s w a b (n:=1) rfl (by omega) (by omega) i u).sub
      ((W n).pureVat P 3 x A.s w a b rfl (by omega) i u)).smul _
 
 change P.tubaField A.s A.F (n+1)=_
 rw [tubaField];rfl
variable (D: Prism)
local notation "W'"=>P.aTuba D A
lemma aTuba_ruby (a b:ℝ)
 (i:(W').realWidth P 3 ≤ a)(u:(W').realWidth P 3 ≤ b):
 P.ruby 3 x (W') 0 a b= ∑ j∈D.support,
     D j • P.ruby 3 x (W (j+1)) 0 (a+δ) (b-δ):=by
 let w:=(W').u 3
 have hw:0<w:=(W').pos _
 have h:=(W').pureVat P 3 x A.s w a b rfl (le_refl _) i u
 apply h.unique
 rw [show (W').F= P.shifts 3 1 (∑ j∈D.support,D j • (W (j+1)).F) from rfl,map_sum]
 simp_rw [map_smul]
 refine Vat.sum hw _ _ _ ?_
 intro j g
 have p: (W (j+1)).u 3 + 1 ≤ w:=Nat.add_le_add (add_le_add le_rfl (le_sup (f:=fun i=>i+1) g)) le_rfl
 exact ((W (j+1)).vat P 3 x A.s w a b (n:=1) rfl (by omega) (by omega) i u).smul _
