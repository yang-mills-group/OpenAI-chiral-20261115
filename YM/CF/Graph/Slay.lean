import YM.CF.Graph.Dray
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Nacre Font Pec
variable {n:Side}{v h b a:ℝ}{p:BudgetPoint}
section pay
variable {n:Type*}[LinearOrder n][Fintype n]{e k u v:ℝ}{A B:FC n}{p:ℂ}
lemma rope (h:Pays k (A-1) (Real.exp u-1))(b:Pays k (B-1) (Real.exp v-1)): Pays k (A*B-1) (Real.exp (u+v)-1):=by
 rw [show A*B-1=(A-1)+(B-1)+(A-1)*(B-1) from (by noncomm_ring), Real.exp_add,show Real.exp u* _-1=(Real.exp u-1 +(Real.exp v-1))+ (Real.exp u-1)*(Real.exp v-1) by ring]; exact (h.add b).add (h.mul b)
lemma loin (h:Pays k (A-1) v)(t:‖p‖ ≤ e)(g:e≤1)(f:0≤k): Pays k (Complex.exp p • A-1) (2*e+Real.exp e*v):=by
 have he : Complex.exp p • A-1=(Complex.exp p-1) • 1+Complex.exp p • (A-1):=by rw [sub_smul,one_smul,smul_sub]; abel
 rw [he]; apply Pays.weigh ((Pays.uno.linear _).add (h.linear _)) _ f; rw [mul_one]; exact add_le_add ((Complex.norm_exp_sub_one_le (t.trans g)).trans (by linarith)) (mul_le_mul_of_nonneg_right ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr t)) h.1)
lemma cost_u (i:n):‖put i‖≤1:=by simpa [Fock.creed] using Flare.cost_pe false (basisKet i) -- tune
lemma sedge (X:Op n):‖dg X‖≤ (Fintype.card n:ℝ)^2*‖X‖:=by
 refine (norm_sum_le ..).trans ?_; refine le_trans (sum_le_sum (g:=fun i:n=> ∑ _:n,‖X‖) (fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=>?_))) ?_; · rw [norm_smul]; have hu: ‖put i*takeF j‖≤1:= (norm_mul_le ..).trans ((mul_le_mul (cost_u _) (by unfold takeF; rw [norm_star]; exact cost_u _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)); exact (mul_le_of_le_one_right (by positivity) hu).trans (norm_entry X i j)
 simp; ring_nf; exact le_rfl -- tune
end pay
variable {j:ℕ}{v η e a h x y r C vA k c:ℝ}{R: GramM n}{X:Loom n}
def baton (n:Side)(v vA C k:ℝ):ℝ:= 2*pittance n vA C+Real.exp (pittance n vA C)*(Real.exp (axle n v+doorF n vA C*lark n^2*k^2)-1)
def flagT (n:Side)(v η C:ℝ):= pittance n 2 C+ (((v+v+η)*(More n).val^4)+lark n^2*doorF n 2 C)
lemma ridge (W:Ledger h v η r C R)(t:Orbit n)(g:HelpP (X t) vA r)(e:0≤vA)(a:0≤r)(hP:0≤ h)(k':0≤k)(b:0≤C)(p:IsStarProjection (spar j R.J.M (X t)))(f:flags R.p.threshold t.1=∅)(m: pittance n vA C ≤1)(w:∀ i:LeanV (Single n), Pays k (drawT (spar j R.J.M (X t)) i) h): Pays k (mile j R X t-1) (baton n v vA C k):=by
 have hp:= front R W.reg W.slip hP t _ k' w f p; have hv:= Pays.brick k' _ (gap_b W t g e a b p); rw [Pic.units_t] at hv; apply loin (rope hp hv.exp_sub) _ m k'; rw [norm_neg]; exact aurP _ _ W.field.2 g e
lemma stout (W:Ledger h v η r C R)(t:Orbit n)(a:0≤r)(hP:1≤h)(b:0≤C)(p:IsStarProjection (spar j R.J.M (X t))): ‖mile j R X t‖ ≤Real.exp (flagT n v η C):=by
 have hp:= rear R W.reg W.slip W.force hP t _ p; let F:= actF j R X t; let E:=pittance n 2 C; let Q:=Pec.pigment R.J.I (X t); have he:‖-Q‖≤E:= by rw [norm_neg]; exact aurP _ _ W.field.2 (railT (X t) r a) (by positivity)
 have ht:‖dg F‖ ≤ lark n^2 *doorF n 2 C:=by apply (sedge F).trans; rw [Pic.units_t n]; exact mul_le_mul_of_nonneg_left (gap_b W t (railT _ _ a) (by positivity) a b p) (sq_nonneg _)
 have hu:= (bootC _).trans (Real.exp_le_exp.mpr ht); rw [flagT,Real.exp_add,Real.exp_add (x:=(v+v+η)*_),mile,norm_smul]; exact mul_le_mul ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr he)) ((norm_mul_le ..).trans (mul_le_mul hp hu (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le
end YM.CF.Graph
