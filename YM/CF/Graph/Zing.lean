import YM.CF.Graph.Ault
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Nacre Font Pec
variable {n:Side}{v h b a:ℝ}{p:BudgetPoint}
section finite
lemma sealV{E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](f:Signed→E)(h:∀ i,‖f i‖ ≤ v): ‖(Fintype.card Signed:ℝ)⁻¹ • ∑ i:Signed,f i‖ ≤ v:=by rw [norm_smul,Real.norm_of_nonneg (by positivity)]; apply (mul_le_mul_of_nonneg_left ((norm_sum_le ..).trans (sum_le_sum (g:=fun _=>v) (fun i _=>h i))) (by positivity)).trans_eq; simp -- tune
end finite
variable {m:ℕ}{C:ℝ}
lemma aurP (U:Pane n)(T:Pride n)(h:Lac T a b)(g:HelpP U v a)(e:0≤v): ‖pigment T U‖ ≤ v^2*b*n.val^4:=by
 apply sealV; intro i; let V:=Yg (incX i) U; have ht(a h: Ok n)(x:Orig n): ‖inner ℝ (silt x a V) (silt x h V)‖ ≤ v^2* nick (show ℝ from ‹_›) (contour x a h):=by
    rename_i a' -- tune shadow
    apply (norm_inner_le_norm ..).trans; apply (mul_le_mul (g.fee i x a) (g.fee i x h) (norm_nonneg _) (mul_nonneg e (Real.exp_pos _).le)).trans; rw [mul_mul_mul_comm,← Real.exp_add,←mul_add,←sq]; refine mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le (by linarith [ct_pos x a h])) (by positivity)
 rw [complX]; unfold cSignX; split <;> try rw [norm_star]
 all_goals
    unfold zinger; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=>v^2*b) (fun j _=>?_)).trans_eq (by rw [sum_const,card_univ,site_card]; simp [mul_comm]))
    apply (norm_sum_le ..).trans; apply (mul_le_mul_of_nonneg_left (h.pay j) (sq_nonneg v)).trans'; simp_rw [cents,mul_sum]; refine sum_le_sum fun x _=> (norm_sum_le ..).trans (sum_le_sum fun y _=>?_); rw [norm_smul,←mul_assoc]; exact mul_le_mul_of_nonneg_right (ht x y (node j)) (norm_nonneg _)
lemma Ctil (U:Pane n)(T:Toy m n)(p:CardK n m T C a)(t: HelpP U v a)(e:0≤a)(w:0≤v)(s:Signed)(i j:Single n): let V:=Yg (incX s) U; ‖cavil T V i j‖ ≤ Fintype.card SU.Slot * (v^m *C):=by
 intro V; let f(k:Trip m n):=fun x: Fin m=> silt (terse i.1) (k x) V; let z(q:SU.Slot): Single n:=(j.1,q); let d:=v^m*C
 have ht(k q):∏ x: Fin m,‖f k x‖ ≤ v^m * nick a (notx m i (z q) k):=by
    let W(x):= t.fee s (place_x i) (k (x: Fin m)); refine (prod_le_prod (fun x _=> norm_nonneg (f k x)) (fun x _=>W x)).trans ?_; rw [prod_mul_distrib, prod_const,card_univ,Fintype.card_fin,← Real.exp_sum, ←mul_sum]; refine mul_le_mul_of_nonneg_left (le_trans (b:=Real.exp (a*notx m i (z q) k)) ?_ ?_) (pow_nonneg w _)
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (show 0≤gear _ _ by unfold gear; positivity)) e)
    exact le_mul_of_one_le_left (Real.exp_pos _).le (le_add_of_nonneg_right (notx_zero ..))
 have hh(q:SU.Slot): (∑ k:Trip m n, nick a (notx m i (z q) k)* ‖T i (z q) k‖) ≤ C:= (p.2.2 i).trans' (single_le_sum (s:=univ) (fun y _=> sum_nonneg (f:=fun j'=> nick a (notx m i y j')*‖T i y j'‖) (fun i _=> mul_nonneg (nick_pos _ (notx_zero ..)|>.le) (norm_nonneg _))) (mem_univ (z q)))
 unfold cavil; rw [Matrix.of_apply,Matrix.sum_apply]; apply (norm_sum_le ..).trans
 let F(k:Trip m n)(q:SU.Slot):=‖T i (z q) k‖*(v^m *nick a (notx m i (z q) k)); have he(k:Trip m n): ‖mold T i.1 j.1 k V i.2 j.2‖ ≤ ∑ q: SU.Slot,F k q:=by
    unfold mold; rw [Matrix.mul_apply]; refine (norm_sum_le ..).trans (sum_le_sum fun q _=> ?_); rw [norm_mul]; have hx: ‖walkB i.1 j.1 V q j.2‖ ≤ 1:= (norm_entry (walkB _ _ V) _ _).trans (le_of_eq (CStarRing.norm_of_mem_unitary (matter _).property)); apply (mul_le_of_le_one_right (norm_nonneg _) hx).trans; change ‖T i (z q) k (f k)‖ ≤ F k q; exact ((T i (z q) k).le_opNorm _).trans (mul_le_mul_of_nonneg_left (ht k q) (norm_nonneg _))
 apply (sum_le_sum (g:=fun i=>∑ q,F i q) fun i _=>he i).trans; rw [sum_comm]; refine (sum_le_sum (g:=fun _=>d) (fun i _=>?_)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul])
 refine le_trans ?_ (mul_le_mul_of_nonneg_left (hh i) (pow_nonneg w _)); rw [mul_sum]; apply sum_le_sum; intro k hk; apply le_of_eq; unfold F; ring
lemma forge (U:Pane n)(T:Toy m n)(p:CardK n m T C a)(t: HelpP U v a)(e:0≤a)(w:0≤v)(h:0≤C): ‖colorX T U‖ ≤ Fintype.card (Single n)* (45*(v^m*C)):=by
 apply sealV; intro s; let V:=cavil T (Yg (incX s⁻¹) U); have ht: ‖Nacre.foil s (cavil T) U‖ = ‖V‖:=by rw [Nacre.foil,zone_c]; unfold Thera.jazz; split <;> (try rw [norm_neg,norm_star]) <;> exact twist_norm ..
 rw [ht]; refine le_trans (Sods.cost_D V ?_ (show 0≤45*(v^m*C) by positivity)) ?_ -- check argument
 · intro i j; have he:= Ctil U T p t e w s⁻¹ i j; rw [slots] at he; exact_mod_cast he -- push
 rfl
end YM.CF.Graph
