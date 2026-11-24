import YM.CF.Floe.Folio
set_option autoImplicit false
noncomputable section
namespace YM.CF.Floe
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology Kronecker
open Filter NormedSpace Function Lattice Lat SU Fock Phase Cube Tenant Branch Drapes Metric Finset
attribute [local instance] opCStarAlgebra
variable {N:Side}{a b c d r e:ℝ}
local notation "D"=> Kelp N a
private lemma toll_b(X: Seal (Site (More N)))(p q:D): ku.eval X p q ≤ (6*X.card:ℝ)*‖p.val-q.val‖:=by
 let A:= ‖p.val-q.val‖; have he(i:Edges (More N)): ‖p.val.1 i-q.val.1 i‖ ≤ A:= (norm_le_pi_norm (p.val.1-q.val.1) i).trans (norm_fst_le (p.val-q.val)); have ht(b i): ‖p.val.2 b i-q.val.2 b i‖ ≤ A:=(norm_le_pi_norm (p.val.2 b-q.val.2 b) i).trans ((norm_le_pi_norm (p.val.2 - q.val.2) b).trans (norm_snd_le (p.val-q.val)))
 have h : (∑ i∈leaks X, ‖p.val.1 i - q.val.1 i‖) ≤ (4*X.card:ℝ)*A:=by
    refine (sum_le_sum fun i _=> he i).trans ?_; simp only [sum_const,nsmul_eq_mul]; have hv:(leaks X).card≤4*X.card:= by
       refine (card_le_card (show leaks X⊆ X×ˢ (univ:Finset Axis) from fun i p=> mem_product.mpr ⟨(mem_filter.mp p).2.1, mem_univ _⟩)).trans ?_; simp [Axis,mul_comm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hv) (norm_nonneg _)
 have g(b:Bool) : ∑ i∈news X, ‖p.val.2 b i-q.val.2 b i‖≤X.card*A:=by
    refine (sum_le_sum (s:=news X) fun i _=> ht b i).trans ?_; simp only [sum_const,nsmul_eq_mul]; refine mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ?_) (norm_nonneg _); rw [←card_image_of_injective _ Tenant.needle]; exact card_le_card (image_subset_iff.mpr fun i p=>(mem_filter.mp p).2)
 unfold ku; dsimp only; rw [Fintype.sum_bool]; exact (add_le_add h (add_le_add (g _) (g _))).trans_eq (by unfold A; ring)
lemma touchL (F: ↑D→ Op (Model N))(S T:Tag (ku (a:=a) (N:=N)))(h:RootedK S T b c F)(p:0<b)(x y: D):‖F x-F y‖≤ 6/b * c * ‖x.val-y.val‖ :=by
 obtain ⟨X,K,pK,U,V⟩:=h; let f:= fun i j=> saleM b K i j; let A:= ‖x.val-y.val‖; let r:=6/b*A; have hc := U.posP; have hp:0 ≤ r:=by unfold r A; positivity
 rw [mul_right_comm]; refine schur (fun i j=> r*f i j) _ _ (mul_nonneg hp hc) ?_ ?_ ?_
 · intro i j; change ‖F x i j-F y i j‖≤_; rw [V x,V y, Matrix.sum_apply,Matrix.sum_apply,←sum_sub_distrib]
   unfold f saleM; rw [mul_sum]; refine (norm_sum_le ..).trans (sum_le_sum fun S _=>?_); rw [←mul_assoc]; let v:=K S i j; have he := pK S; have hu:(S.card:ℝ)≤rent b S/b:= (le_div_iff₀ p).mpr (by unfold rent; linarith [Real.add_one_le_exp (b*(S.card:ℝ))]); refine ((he.expo i j).variation ..).trans ?_; change v*ku.eval S x y≤_*v; rw [mul_comm v]; refine mul_le_mul_of_nonneg_right ((toll_b S x y).trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu (by norm_num:0 ≤ (6:ℝ))) (norm_nonneg _)).trans_eq ?_)) (he.nonn _ _); unfold r A; ring
 · intro i; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (U.rows i) hp
 intro i; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (U.cols i) hp
namespace LedgerP
variable{F:pMat}{u v:Bool}(h:LedgerP F u v)
include h
lemma warm (p:a < b)(t:∀ (i: IndexK)(x:Own i.1), ‖F i (skin x.val)‖≤ a):∃ c:ℝ,0<c ∧∀ (i:IndexK) (x:BayP i.1), x∈Kelp i.1 c→‖F i x‖≤b:=by -- binder syntax
 obtain ⟨d,e,r,l,q,y,h⟩:=h; let w:=(6/d)*r; have he:0<w:= by unfold w; positivity
 let c:=min e ((b-a)/w); have hc:0<c:=lt_min q (div_pos (by linarith) he); have hz:w*c ≤ b-a:=by rw [mul_comm]; exact (le_div_iff₀ he).mp (min_le_right ..)
 refine ⟨c,hc,fun i x g=> ?_⟩; obtain ⟨z,hp⟩:= kelp_m.mp g; let Z:Kelp i.1 e:=⟨x,cut_j g (min_le_left ..)⟩; let U:=uθ z q; refine (norm_le_norm_sub_add (F i x) (F i U.val)).trans ?_; refine ((add_le_add (touchL _ _ _ (h i).lib l Z U) (t i z))).trans ?_; exact (add_le_add (mul_le_mul_of_nonneg_left hp.le he.le) le_rfl).trans (by change w*c + a ≤ b; linarith)
omit h
lemma powS {v:Bool}(F:pMat)(h:LedgerP F v v)(g:a<1)(p:0 ≤ a)(u:∀ (i: IndexK)(x: Own i.1), ‖F i (skin x.val)‖≤ a) : ∃ d b r c:ℝ,0<d∧0<b∧0<r∧0<c∧c<1∧∀ n:ℕ, certS (F^n) v v d b (r*c^n):=by -- include issue
 obtain ⟨e,hp,he⟩:=exists_between g; obtain ⟨x,k,y,A,B,V,pF⟩:=h; obtain ⟨z,K,H⟩:=warm ⟨x,k,y,A,B,V,pF⟩ hp u; let c:= min k z; let w:= slim_e pF (min_le_left k z); have ht:=ζq; obtain ⟨l,r,s⟩:= exists_between he; obtain ⟨n,hn,m,t,t',Z,v',J⟩:=grouping ht A V r (by linarith) s (show 0<(1:ℝ)/4 by norm_num)
 obtain ⟨u0,q,e,hk⟩:=drift_name hn (show 0<(1:ℝ)/2 by norm_num) (by norm_num); refine ⟨t,c,2*(Real.exp t*(u0^n)⁻¹*(Real.exp t*(max 1 (2*y))^n)),u0,t',lt_min B K,by positivity,q,e,fun j i=>?_⟩
 exact Crown.craft hn (w i) (Crown.natural _ _ _ _ _ _ _ _ _ ht A.le (by linarith) t'.le Z v' J (ku_cap ..) (w i) (fun U=> H _ _ (cut_j U.property (min_le_right k z)))) (Z.trans (half_le_self A.le)) t' q hk j
end LedgerP
end YM.CF.Floe
