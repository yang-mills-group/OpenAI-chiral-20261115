import Crape.Jacks
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
open Py.Dyad Keeping
variable (L0:Side) (C D:ℕ→ℕ→ℝ)(F:ℕ)
local notation "H"=>gainCost L0
local notation "Q"=>ThinGauge.boost (Xη L0)
def starts (s:ℕ):ℝ:= C s s * revenue L0 (C s) (D s) s F
-- use Nat p=s-F. define in p coordinate. avoid infinite prod.Phrase.
def ladderS:ℕ→ℝ | 0=>1|i+1=> ladderS i * starts L0 C D F (F+i)
def basket(s:ℕ):ℝ:= ladderS L0 C D F (s-F)
lemma outlay(s:ℕ)(v:F ≤ s):basket L0 C D F (s+1)=basket L0 C D F s * starts L0 C D F s:=by unfold basket; rw [show s+1-F=s-F+1 by omega, ladderS]; congr; omega
variable (p:∀ s,F ≤ s → Bills F (s+1) s L0 (C s) (D s))
include p
lemma boundsT {j s:ℕ}(t:F ≤ j)(u:j ≤ s): 3/4 ≤ revenue L0 (C s) (D s) s j ∧ revenue L0 (C s) (D s) s j ≤ 5/4:=by
 obtain ⟨a,b⟩:=abs_le.mp (fare_toll (C s) (D s) L0 u (fun i h v=>(p s (t.trans u)).2 _ (t.trans h) v)); constructor<;> linarith
lemma skein {s:ℕ}(e:F ≤ s) : |starts L0 C D F s| ≤ 2*gainCost L0 ∧ starts L0 C D F s≠0:=by
 let c:ℕ→ℝ:=C s; have ht:= (p s e|>.1 s e (Nat.lt_succ_self _)); have l:= boundsT L0 C D F p le_rfl e
 let t:= revenue L0 c (D s) s F; have q:0<t:=by unfold t; change 0< revenue _ (C s) _ _ _; linarith
 have h:|t|≤2:=by rw [abs_of_pos q]; change revenue _ (C s) _ _ _ ≤ _; linarith
 unfold starts; rw [abs_mul]; exact ⟨(mul_le_mul ht.amp h (abs_nonneg _) (gainCost_pos L0).le).trans_eq (mul_comm H 2),mul_ne_zero ht.non q.ne'⟩
lemma basket_price {s:ℕ}(e:F ≤ s):|basket L0 C D F s| ≤ (2*gainCost L0)^(s-F) ∧basket L0 C D F s≠0:=by
 rcases Nat.exists_eq_add_of_le e with ⟨d,rfl⟩; induction d with
 | zero=> simp [basket,ladderS]
 | succ d ih=>
    rw [←add_assoc, outlay _ _ _ _ _ (Nat.le_add_right ..),show F+d+1-F=(F+d-F)+1 from by omega, abs_mul,pow_succ]; obtain ⟨k,b⟩:=skein L0 C D F p (s:=F+d) (Nat.le_add_right ..); specialize ih (Nat.le_add_right ..); exact ⟨mul_le_mul ih.1 k (abs_nonneg _) (pow_nonneg (mul_nonneg (by norm_num) (gainCost_pos _).le) _),mul_ne_zero ih.2 b⟩
#print axioms basket_price
end PledgeT
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
