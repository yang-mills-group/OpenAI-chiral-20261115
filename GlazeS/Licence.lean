import GlazeS.Overseer
import SatinFacet
import Crape.Halo
import Crape.Adjust
import Crape.Supple
import Crape.TimeLine
import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
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
set_option maxRecDepth 6000
set_option maxHeartbeats 700000
open Aria Casting Set
open scoped Pointwise
namespace MiterT
variable(P:Spine)(F:ℕ)(C D:ℕ→ℕ→ℝ)(s t:ℕ)(A:SampleDose)
local notation "K"=>P.calibration
lemma pigment: callix P F C D s∈ enclave P.calibration:= Subalgebra.smul_mem _ (color_wp P s _) _
lemma programRent:callix P F C D s∈ bay P.calibration (Calico.bands (cellar P F s) 22) true:= by
 unfold callix etui; rw [Nat.sub_self]; exact Subalgebra.smul_mem _ ((Tapestry.locates P.calibration _ _ (f:=wp P s (cellar P F s))).mpr (Calico.lining_test P.calibration (cellar P F s) (P.run.meter.a s) (payday P s))) _ -- orbitB0 def
-- placed descendants always supported. formula cover after border.Then supports around test. 
noncomputable abbrev billbook(P:Spine)(s t:ℕ)(z:Cover)(p:Finset Cover):Finset Cover:= P.border 3 (look 3) (fun i=> z i.val) (plow P.calibration 3 (z 3) (volumeAround P.par P.width (t-s) p))
lemma rights(z:Cover):
 let o:= cellar P F s
 let q:= callix P F C D s
 gibbert P s t q z∈ bay K (billbook P s t z (Calico.bands o 22)) true ∧ gibbert P s t q z∈ enclave K:=by
 intro o q; refine ⟨P.shipping 3 _ _ (P.shifts_support _ _ _ ?_), ?_⟩
 · exact (proceeds P.run P.large P.history.circuit s (t-s) (show InTest P.calibration true (Calico.bands o 22) false q.val from programRent P F C D s)).1
 have b:=P.shifts_keep 3 (z 3) (P.refine_keeps s q (pigment P F C D s) (t-s)); unfold gibbert; generalize look 3=L; induction L with
 |nil=>exact b
 |cons i L ih=> rw [P.ship_started]; exact P.shifts_keep _ _ ih
-- give footprint via P.always each. For time not always.need container.Address recursion version
variable (L:List (Trans (3:Axis)))(d:Trans (3:Axis)→ℤ)
lemma all_price(S:Finset Cover){y:Vantage}(p:y∈P.pinFoot s (P.border 3 L d S)):∃ x∈P.pinFoot s S, y 3=x 3∧∀ i:Trans (3:Axis),y i.val=x i.val+ bell (timeMesh P.par) s (massStep (3:Axis) i L d):=by
 induction L generalizing y with
 | nil=> exact ⟨_,p,rfl,fun i=>by simp [massStep,bell]⟩
 | cons i L ih=>
    have ht:=P.step_back_pin s (P.border 3 L d S) (i:Axis) (d i) p
    obtain ⟨w,v,a,t⟩:=ih ht
    refine ⟨w,v,?_,fun k=>?_⟩
    · rw [←a,Pi.sub_apply]; unfold plenumShift; -- check
      simp [Ne.symm i.property,i.property]
    specialize t k
    rw [mass_cons,bell_add]
    rw [Pi.sub_apply] at t; unfold plenumShift at t
    split_ifs with e
    · subst k; simp only [Pi.single_eq_same] at t; linarith
    have he:i.val ≠ k.val:=fun h=>e (Subtype.ext h); simp [he, Ne.symm he] at t; simpa [bell] using t

lemma totalPose(z:Cover)(v:s ≤ t)(y:Vantage)(p:y∈P.pinFoot t (billbook P s t z (Calico.bands (cellar P F s) 22)))(i:Axis):|y i-(central P F s+P.meshPose t z) i|≤ intrinsic P s:=by
 let a:=(fun i:Trans (3:Axis)=>z i.val)
 obtain ⟨x,w,e,h⟩:=all_price P t (look (3:Axis)) a _ p
 let u:=P.plenumShift t 3 (z 3); let b:=x-u
 have he:= P.pin_onward _ _ _ v (P.step_back_pin _ _ _ _ w)
 have ht:= MiterT.expense P _ s (show b∈_ from he) i
 change |central P F s i - (x i - u i)|≤ intrinsic P s at ht
 change |y i-(central P F s i +bell (timeMesh P.par) t (z i))|≤ _
 by_cases f:i=3
 · subst i; rw [e]; unfold u plenumShift at ht; rw [Pi.single_eq_same] at ht; rw [abs_le] at *; constructor<;> linarith
 specialize h (⟨i,f⟩:Trans 3); rw [mass_all] at h; change y i=x i+bell (timeMesh P.par) t (z i) at h
 unfold u plenumShift at ht; simp only [Pi.single_eq_of_ne f,sub_zero] at ht; rw [h,add_sub_add_right_eq_sub,abs_sub_comm]; exact ht
abbrev coverage(F:SampleDose)(z:ℝ):Set Vantage:= {p|∃ x∈tsupport F.val,∀ i:Axis,|p i-x i|≤ z}
lemma legalClear(v:s ≤ t): P.asked_at t (athlete P F C D s t A) (coverage A (intrinsic P s)) ∧ athlete P F C D s t A∈ enclave P.calibration:=by
 unfold athlete wageRoll; let f:=dealt A (central P F s); let S:=P.usedGrid t f; let Z:= callix P F C D s; let h(i:Cover):=gibbert P s t Z i; let G(i:Cover):= billbook P s t i (Calico.bands (cellar P F s) 22); let I:= S.biUnion G
 refine ⟨⟨I,?_ ,?_⟩,Subalgebra.sum_mem _ (fun i p => Subalgebra.smul_mem _ (rights P F C D s t i|>.2) _)⟩
 · apply Subalgebra.sum_mem; intro i p; exact tallerBay P.calibration _ true (subset_biUnion_of_mem G p) (Subalgebra.smul_mem (bay P.calibration (G i) true) (rights P F C D s t i|>.1) _)
 rintro x ⟨a,l,h'⟩; obtain ⟨i,e,u⟩:=mem_biUnion.mp (l:a∈I)
 have hr:= MiterT.pay_shift A (central P F s) ((P.usedPose t f _).mp e)
 rw [add_comm] at hr; exact ⟨_,hr,totalPose P F s t i v x ⟨a,u,h'⟩⟩
#check mass_all
#check tallerBay
#check subset_biUnion_of_mem
#print axioms legalClear
end MiterT
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
