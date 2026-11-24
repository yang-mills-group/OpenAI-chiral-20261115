import Ridgetop.Gw
import Ridgetop.Origin
import Risa.Warehouse
import Preen.Chey
-- pilot price exactly zero, all. 
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 360000
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
namespace PledgeT
open Calico
open Aria Casting Set
open scoped Pointwise
namespace MiterT
open _root_.YM.Gleam.Luster.Risa CF.BProof AnalyticBridge.VerifiedReset
open Py.Rate.LocalLimit Py Py.Dyad Papal _root_.YM.CF.Pannier.Chancel Cliplet Precision
variable (P:Spine) (s A:ℕ)(o:Bool→ Cover)(b:Bool)
local notation "T" d:max=> stackW d
local notation "f" d:max=> scaleY (hat P.par.R.L P.par.x (stackW d))
local notation "g" d:max=> ((girder P d):ℝ)
def badge(d:ℕ):ℝ:= (_root_.YM.Preen.shoreH d)⁻¹ + 4/(f d)
lemma stages_q: Tendsto (fun d=>f d) atTop atTop:= by
 apply summitG.comp -- turnover.Cal
 exact (turnover P.par).comp (tendsto_atTop_mono (show hikeV ≤ stackW from fun _=>Nat.le_add_right ..) _root_.YM.Preen.goes_town)
lemma bad_f: Tendsto (badge P) atTop (𝓝 0):= fades P
lemma artFactor{c a:ℝ}{l:ℕ}(h:1 ≤ c)(v:0≤ a)(w:a≤c^l):
 (c⁻¹ ^(2*heightH (drive l (8*l+6))))*a^8 ≤ c⁻¹:=by
 have hp:0<c:=zero_lt_one.trans_le h
 have he: a^8 ≤ c^(8*l):= (pow_le_pow_left₀ v w 8).trans_eq (by rw [← pow_mul,Nat.mul_comm])
 let k:=heightH (drive l (8*l+6)); have hb:1+8*l ≤ 2*k:=by unfold k drive heightH; omega
 rw [inv_pow,inv_mul_le_iff₀ (pow_pos hp _)] -- k; goal a^8 ≤ _*c⁻¹, divide multiply c
 apply (mul_le_mul_iff_left₀ hp).mp
 rw [show c^(2*k)*c⁻¹*c=c^(2*k) from (?_ : _)]; swap; · rw [mul_assoc,inv_mul_cancel₀ hp.ne',mul_one]
 calc _ ≤ c^(8*l)*c:=by gcongr
      _ = c^(1+8*l):=by rw [add_comm,pow_add,pow_one]
      _ ≤ _:= pow_le_pow_right₀ h hb
#print axioms stages_q
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
