import YM.CF.Graph.Coif
import YM.SU5.Thin.Cascade.Sea
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Rapids
open Function Filter NormedSpace Fock Thera Finset Lattice
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder Classical ContDiff
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I]
variable {A B:Op I}{u v C:ℝ}
def Filed(A:Op I)(C:ℝ):Prop:= ∀ i:I,∑ j:I,‖A j i‖≤ C
lemma parade (A:Op I): DriveL1 (star A)=DriveL1 A:=by unfold DriveL1; rw [sum_comm]; simp [Matrix.star_apply]
lemma Filed.dial (p:Filed A u)(i:I): Gall.dialZ (acts A (basisKet i))≤u:=by simpa only [Gall.dialZ,basis_act] using p i
lemma Filed.from (p:∀ i:I,Gall.dialZ (acts A (basisKet i))≤u):Filed A u:=by intro i; simpa only [Gall.dialZ,basis_act] using p i
lemma Filed.price (u':Filed A u)(p:0≤u)(w:Filed B v): Filed (A*B) (u*v):=by
 intro i; simp_rw [Matrix.mul_apply]; apply (sum_le_sum (fun _ _=> norm_sum_le ..)).trans; simp_rw [norm_mul]; rw [sum_comm]; simp_rw [←sum_mul]; apply (sum_le_sum (fun k _=> mul_le_mul_of_nonneg_right (u' k) (norm_nonneg (B k i)))).trans; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (w i) p
lemma Filed.wire (A:Op I)(B:Op I)(p:Filed A u): DriveL1 (A*B) ≤ u*DriveL1 B:=by
 unfold DriveL1; rw [sum_comm]; simp_rw [Matrix.mul_apply]; refine le_trans (sum_le_sum (g:=fun i=> u*∑ j:I,‖B j i‖) ?_) ?_
 · intro i _; apply (sum_le_sum (fun _ _=> norm_sum_le ..)).trans; simp_rw [norm_mul]; rw [sum_comm]; simp_rw [←sum_mul]; rw [mul_sum]; exact (sum_le_sum (fun k _=> mul_le_mul_of_nonneg_right (p k) (norm_nonneg (B k i))))
 rw [←mul_sum, Finset.sum_comm (f:=fun i j=> ‖B j i‖)]
lemma assists_op (b:0≤C)(p:Filed A C) (w:Filed (star B) C)(T:Op I): DriveL1 (A*T*B) ≤ C^2*DriveL1 T:=by
 nth_rw 1 [←parade (A*T*B)]; rw [star_mul]; apply (Filed.wire _ _ w).trans; rw [parade]; exact (mul_le_mul_of_nonneg_left (Filed.wire _ _ p) b).trans_eq (by ring)
lemma winter_metric (Q:UNI I)(b:Bool)(F:Op I) (c:0≤ C)(hv:Filed Q.val C): DriveL1 (Thera.jazz b (twist Q F)) ≤ C^2 * DriveL1 F :=by
 have hp : Filed (star (star Q.val)) C:=(star_star Q.val).symm ▸ hv
 rw [twist_formula]; unfold jazz; split
 · rw [show DriveL1 (-star (Q.val*F*star Q.val))=DriveL1 (star (Q.val* F *star Q.val)) from (by unfold DriveL1; simp only [Matrix.neg_apply,norm_neg]),parade]; apply assists_op c hv hp

 apply assists_op c hv hp
open Gall
lemma narrator (h:0≤v)(A:Op I): Pays v (dg A) (DriveL1 A*v^2):=by
 unfold dg DriveL1 dyad
 have ht(i:I):Pays v (put i) v:=by
    have he:=Pays.tone (n:=I) (false,i) h; simpa [Gall.pack,artW,Flare.ton,creed] using he
 have hr(i:I):Pays v (takeF i) v:=by have he:=Pays.tone (n:=I) (true,i) h; simpa [Gall.pack,artW,Flare.ton,creed] using he
 simp_rw [sum_mul]; apply Pays.sumT; intro i hi; apply Pays.sumT; intro j hj; rw [sq]; apply Pays.linear; exact (ht i).mul (hr j)
lemma gifts {A:FC I}(p:Pays v A C): Pays v (exp A) (Real.exp C):=by have H:= p.exp_sub.add Pays.uno; rw [sub_add_cancel,sub_add_cancel] at H; exact H
lemma shipsBoard {n:Side}(R:Scree.GramM n) (A:Op (Tulip.Single n))(U:Skye.Orbit n)(P: IsStarProjection A){a b w D ε:ℝ}(Z:Graph.Ledger a ε b w D R)(h:Filed A C)(hp:0≤v)(hu:0≤a)(hx:(C+1)*v≤a): Pays v (Scree.tank A (R.board U)) (Real.exp ((ε+ε+b)*(Cube.More n).val ^4)):=by
    rw [Scree.GramM.board,Graph.shape A _ _ P,add_mul,Real.exp_add]; let z(i:Pastry.LeanV (Tulip.Single n)): Pays v (Pastry.drawT A i) a:=(Graph.crag A i h.dial hp).weigh hx hp
    exact (gifts ((Graph.tierG A _ z).weigh (Graph.marks R U Z.reg Z.slip hu) hp)).mul ((Graph.tierG A _ z).weigh (Graph.toeF Z.force hu _) hp)
end YM.CF.Rapids
