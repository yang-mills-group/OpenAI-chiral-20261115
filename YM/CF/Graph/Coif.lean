import YM.CF.Graph.Sore
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
variable {n:Side}{v v' v'' h b e:ℝ}{Q:Sweep n→Prop}{p:BudgetPoint}
lemma shape {I:Type*}[Fintype I][LinearOrder I](P:Op I)(A B:ribbon I)(p:IsStarProjection P): tank P (exp A*B)=exp (tank P A)*tank P B:=by simp only [show ∀ i,tank P i=(nursery P p).cook i from fun i=>tank_eq _ _ p,map_mul,Poly.rising]
abbrev actG (R: GramM n)(X:Orbit n):= exponentL R.p R.F X.1 + exponentL R.p R.slip X.1
lemma marks(R:GramM n)(X:Orbit n)(h:IncX Q R.F R.p b v)(k:IncX Q R.slip R.p b v')(u:0≤b): tier b (actG R X).val ≤ (v+v')*(More n).val^4:=by unfold actG; rw [add_mul]; exact (tier_plus u _ _).trans (add_le_add (toeE h u X.1) (toeE k u X.1))
lemma front (R:GramM n)(h:IncX Q R.F R.p b v)(k:IncX Q R.slip R.p b v')(u:0≤b)(V: Orbit n)(A:Op (Single n))(w:0≤e)(f:∀ i:LeanV (Single n),Pays e (drawT A i) b)(t:flags R.p.threshold V.1= ∅)(p:IsStarProjection A): Pays e (tank A (R.board V)-1) (Real.exp ((v+v')*(More n).val^4)-1):=by
 rw [GramM.board, fuel_one _ _ _ t, shape _ _ _ p, tank_eq _ 1 p,map_one,mul_one]; exact ((tierG A _ f).weigh (marks R V h k u) w).exp_sub
lemma bootC {I:Type*}[Fintype I][LinearOrder I](A:FC I): ‖exp A‖ ≤ Real.exp ‖A‖:=by
 rw [congrFun (exp_eq_tsum ℝ), Real.exp_eq_exp_ℝ,congrFun (exp_eq_tsum ℝ)]; -- tune use ℂ
 refine (norm_tsum_le_tsum_norm ?_).trans ( (?_ : _))
 · exact norm_expSeries_summable' (𝕂:=ℝ) A -- tune
 exact Summable.tsum_mono (norm_expSeries_summable' (𝕂:=ℝ) A) (by apply Summable.of_norm; exact norm_expSeries_summable' (𝕂:=ℝ) ‖A‖) (fun n=> by rw [norm_smul,Real.norm_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left (norm_pow_le ..) (by positivity))
lemma rear(R:GramM n)(h:IncX Q R.F R.p b v)(k:IncX Q R.slip R.p b v')(p: Dark Q R.K R.p b v'')(u:1≤b)(V:Orbit n)(A:Op (Single n))(t:IsStarProjection A): ‖tank A (R.board V)‖ ≤ Real.exp ((v+v'+v'')*(More n).val^4):=by
 rw [GramM.board,shape _ _ _ t,add_mul,Real.exp_add]; exact (norm_mul_le ..).trans (mul_le_mul ((bootC _).trans (Real.exp_le_exp.mpr ((billP _ _ t u).trans (marks R V h k (zero_le_one.trans u))))) ((billP _ _ t u).trans (toeF p (zero_le_one.trans u) V)) (norm_nonneg _) (Real.exp_pos _).le)
end YM.CF.Graph
