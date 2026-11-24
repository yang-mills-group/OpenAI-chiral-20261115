import YM.CF.Gall.Molt
import YM.CF.Girt.Mist
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]{k v a c y:ℝ}
lemma pony(x y:Ket n):dialZ (x-y) ≤ dialZ x+dialZ y:=by unfold dialZ; rw [←sum_add_distrib]; exact sum_le_sum fun i _=> norm_sub_le ..
lemma crag (P:Op n)(i:LeanV n)(e:∀ j:n,dialZ (acts P (basisKet j)) ≤ c)(h:0≤v): Pays v (drawT P i) ((c+1)*v):=by
 unfold drawT; split
 · rw [seekF, prong_p]; let x:=acts (1-P) (basisKet i.2); refine (Pays.url x false h).weigh ?_ h; apply mul_le_mul_of_nonneg_right _ h; unfold x; rw [act_sub,act_one]; refine (pony ..).trans ((add_le_add (a:=dialZ _) (b:=1) ?_ (e _)).trans_eq (add_comm 1 c)); simp [dialZ,apply_ite (fun x:ℂ=> ‖x‖)]
 rw [hideF, prong_t]; let x:=acts P (basisKet i.2); refine (Pays.url x true h).weigh ?_ h; exact mul_le_mul_of_nonneg_right ((e _).trans (by linarith)) h
lemma paneFT (I:Type*)[Fintype I][LinearOrder I] (k:ℝ)(X:I→FC n)(h:∀ i,Pays k (X i) c)(i:Finset I):Pays k (Scree.column X i) (c^i.card):=by
 have he:= Pays.rollP X (i.sort (·≤·)) h; rw [length_sort] at he; exact he
lemma tierG (P:Op n)(S:ribbon n)(h:∀ i:LeanV n,Pays k (drawT P i) c): Pays k (tank P S) (tier c S.val):=by
 refine Pays.sumT _ _ _ fun i _=> ?_; rw [mul_comm (c^_)]; refine Pays.linear (A:=Scree.column (I:=LeanV n) (drawT P) i) ?_ _; exact paneFT (LeanV n) k (drawT P) h i
lemma vital[Nonempty n](P:Op n)(h:IsStarProjection P)(i:LeanV n):‖drawT P i‖ ≤1:=by
 have hp(A: Op n)(w:‖A‖≤1)(i:n): ‖acts A (basisKet i)‖ ≤ 1:= (Flare.opy ..).trans (by simp [basisKet,w])
 unfold drawT; split; rw [seekF,prong_p]; exact (Flare.cost_pe false _).trans (hp _ (h.one_sub.norm_le _) _); rw [hideF,prong_t]; exact (Flare.cost_pe true _).trans (hp _ (h.norm_le _) _)
lemma billP[Nonempty n] (P:Op n)(S:ribbon n)(h:IsStarProjection P)(w:1≤c): ‖tank P S‖≤tier c S.val:=by
 have ht(L:List (LeanV n)):‖(L.map (drawT P)).prod‖ ≤1:=by induction L with| nil=> simp| cons i L ih=> exact (norm_mul_le ..).trans ((mul_le_mul (vital P h i) ih (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
 refine (norm_sum_le ..).trans (sum_le_sum fun i (_:i ∈ (univ:Finset (Finset (LeanV n))))=>?_); rw [norm_smul,mul_comm (‖crumb _ _‖)]; exact mul_le_mul_of_nonneg_right ((ht _).trans (one_le_pow₀ w)) (norm_nonneg _)
variable {j:ℕ}
lemma burley(j:ℕ)(t:1≤j):∃ C a:ℝ,0<C∧0<a∧∃ v:ℕ,∀ N:Side,v≤ N.val→∀ U:Bkg (More N),Guard U a→∀ (M:Tulip.Male)(i:Single N),dialZ (acts (spar j M U) (basisKet i)) ≤ C:=by
 obtain ⟨a,r,e,h,hc,l,v,Q⟩:= funde_s _ t; refine ⟨r,e,hc,l,v,fun n g U H M i=>?_⟩
 let b:=bail n e; let x:Openc (More n) e:=⟨profile U, U,H,by simpa⟩
 obtain ⟨F,C,p,j,q⟩:= (show Solo _ _ _ _ from Q M n g).lib -- fields
 unfold dialZ; simp_rw [basis_act]; rw [show spar _ M U= _ from q x]; refine le_trans (sum_le_sum (g:=fun t=>saleM a C t i) (fun t _=>?_)) (j.cols i); rw [Matrix.sum_apply]; exact (norm_sum_le ..).trans (sum_le_sum (fun S _=> ((p S).expo _ _ |>.bounded x).trans (le_mul_of_one_le_left ((p S).nonn _ i) (rent_one h.le S))))
end YM.CF.Graph
