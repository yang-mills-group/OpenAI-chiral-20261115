import Verses.Database
import YM.SU5.Relativistic.Raspa
import YM.CF.Continuum.Extensive
/-! # pinpoint charge. On clean ORBIT. (For unrepaired dirty count by t.) -/
set_option autoImplicit false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Metric Fock Finset Lattice Lat Fir Ember Thera BPress.Spin.Blank Rush SU Scroll Tulip Dial Cube Skye Pannier Pannier.Chancel Buffered Pastry
open Crest.Sleet Pannier.Damask
open scoped Topology Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator BigOperators ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
open CF.Window Matrix Papyrus.Granat
namespace Verses
variable {I:Type}[LinearOrder I][Fintype I][Nonempty I]{C:ℝ}
variable {P V:Op I}(p:IsStarProjection P)
lemma price_saber (t:IsStarProjection V)(T:Shaft I)(u:fiber T C)(b:ℝ)(v:condor V b)(v':0≤ b)(h:0≤C)(i:LeanV I): ‖T.glow (drawT V i)‖ ≤ C*(1+b):=by
 unfold drawT; split
 · rw [seekF,prong_p,T.glow_up,←act_mul]; apply (Flare.cost_pe false _).trans ((column_action _ _ u.fst (condor_one_sub _ v) h i.2))
 rw [hideF,prong_t,T.glow_down,←act_mul]; exact ((Flare.cost_pe true _).trans (column_action _ _ u.snd v h i.2)).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) h)
lemma Saber_budget (Q:Op I)(k:ℕ)(h:0≤C)(f:∀ i:I, ‖acts (Comb Q P k) (basisKet i)‖≤C∧‖acts (star (Comb Q P k)) (basisKet i)‖≤C): fiber (Saber (B:=Q) p k) (1+C):=by
 constructor <;> intro i
 · unfold Saber; simp only [act_add,act_one]; exact (norm_add_le ..).trans (add_le_add (by simp [basisKet]) (f i).2)
 unfold Saber; simp only [star_sub, star_one, star_star,act_sub,act_one]; exact (norm_sub_le ..).trans (add_le_add (by simp [basisKet]) (f i).1)
lemma Saber_holds (B:Op I) (k:ℕ): (Saber (B:=B) p k).sell*P=P:=by
 unfold Saber; simp only [add_mul, one_mul]; rw [show star (Comb B P k)*P=0 from (?_),add_zero]; nth_rw 2 [← (show star P=P from p.isSelfAdjoint)]; rw [←star_mul,comb_px p, star_zero]

def tailor (U:UNI I): Shaft I:=⟨U.val,star U.val,(U.property.2)⟩
lemma trim_saber (U:UNI I)(A:Shaft I)(j:fiber A C)(h:0≤C)(K:ℝ)(v:condor (U:Op I) K): fiber (A.foldC (tailor U)) (C*K) :=by
 constructor; · exact column_action _ _ j.fst v h
 intro i; change ‖acts (star (star U.val*A.buy)) (basisKet i)‖≤_; rw [star_mul,star_star]; exact column_action _ _ j.snd v h i
lemma trim_condor {Q B:Op I}(T:UNI I)(C:ℝ)(p:condor T.val C): entryBudget (T.val*Q*B)≤ C*entryBudget (Q*B):=by rw [mul_assoc]; exact condor_budget _ _ p
-- equivalent appraisal: glow through unitary THEN Saber with origin-S0 and transform dg/aim by Total instead of conjugating matrix costs explicitly. Norm on bra still compare to stunt k via lawn. Wave sea transforms covariance. Use `Thera.Step`.
end Verses
end YM.CF.Papyrus.Franc
