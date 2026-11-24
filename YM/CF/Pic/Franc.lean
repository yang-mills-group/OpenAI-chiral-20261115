import YM.CF.Pic.Zoom
set_option autoImplicit false
noncomputable section
namespace YM.CF.Pic
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n:Type*}[LinearOrder n][Fintype n]{P Q R K:Op n}{p q f:Wave n}{k v C d b w:ℝ}{A B:FC n}
-- Observable valuation. Aut gauge equiv frame. permits arbitrary left insertions.
def Yep (k:ℝ)(p:Wave n)(q:Wave n)(d:ℝ):Prop:=∀ u:List (Reader0 n),‖inner ℂ p (acts (rollC ton u) q)‖ ≤ d*size_k _ k u
def Pays (k:ℝ)(A:FC n)(d:ℝ):Prop:= 0 ≤ d ∧ ∀ p q:Wave n,∀ w:ℝ,0 ≤ w→Yep k p q w→Yep k p (acts A q) (d*w)
lemma size_q (p:0 ≤k)(u:List (Reader0 n)): 0 ≤ size_k _ k u:=mul_nonneg (count_curve _) (pow_nonneg p _)
lemma Yep.weigh (p:Yep k f q b)(t:b≤d)(h:0≤k):Yep k f q d:=fun i=>(p i).trans (mul_le_mul_of_nonneg_right t (size_q h i))
lemma Pays.weigh (p:Pays k A b)(t:b≤d)(h:0≤k):Pays k A d:=⟨p.1.trans t,fun i j w v g=>(p.2 _ _ w v g).weigh (mul_le_mul_of_nonneg_right t v) h⟩
lemma Yep.join (h:Yep k f q d)(g:Yep k f p v): Yep k f (q+p) (d+v):=by intro i; rw [map_add,inner_add_right, add_mul]; exact (norm_add_le ..).trans (add_le_add (h _) (g _))
namespace Pays
lemma add (p:Pays k A d)(q:Pays k B v):Pays k (A+B) (d+v):=by refine ⟨add_nonneg p.1 q.1, fun i j w h u=>?_⟩; rw [act_add,add_mul]; exact (p.2 i j w h u).join (q.2 i j w h u)
lemma linear(p:Pays k A d)(c:ℂ): Pays k (c • A) (‖c‖*d):=by
 refine ⟨mul_nonneg (norm_nonneg _) p.1,fun i j w h u z=>?_⟩; rw [act_smul,map_smul,inner_smul_right, norm_mul]; exact (mul_le_mul_of_nonneg_left (p.2 i j w h u z) (norm_nonneg c)).trans_eq (by ring)
lemma mul (p:Pays k A d)(q:Pays k B v):Pays k (A*B) (d*v):=⟨mul_nonneg p.1 q.1,fun i j w e g=>by rw [act_mul,mul_assoc]; exact p.2 _ _ _ (mul_nonneg q.1 e) (q.2 _ _ _ e g)⟩
lemma uno:Pays k (1:FC n) 1:=⟨zero_le_one,fun i j w e h=>by rw [act_one,one_mul]; exact h⟩
lemma tone(u:Reader0 n)(p:0 ≤k):Pays k (ton u) (k*‖u.2‖):=by
 refine ⟨mul_nonneg p (norm_nonneg _),fun i j w t H L=>?_⟩; rw [← act_mul,show rollC ton L*ton u=rollC ton (L++[u]) by simp [rollC]]; refine (H (L++[u])).trans_eq ?_ -- tune lhs convert
 unfold size_k unitsC; simp [pow_succ]; ring
lemma power(p:Pays k A d)(i:ℕ):Pays k (A^i) (d^i):=by induction i with| zero=>rw [pow_zero,pow_zero]; exact uno| succ i ih=>rw [pow_succ,pow_succ]; exact ih.mul p
lemma nil:Pays k (0:FC n) 0:=⟨le_rfl, fun p q a e g v=>by simp⟩
lemma sumT{I:Type*}(S:Finset I)(A:I→ FC n)(k:I→ℝ)(p:∀ i∈S,Pays b (A i) (k i)):Pays b (∑ i∈S,A i) (∑ i∈S,k i):=by
 classical
 induction S using Finset.induction_on with| empty=>rw [sum_empty,sum_empty]; exact nil| @insert i S e ih=>rw [sum_insert e,sum_insert e]; exact (p i (mem_insert_self ..)).add (ih fun i x=>p i (mem_insert_of_mem x))
lemma exp_sub (p:Pays k A C):Pays k (exp A-1) (Real.exp C-1):=by
 let V(n':ℕ):=(n'.factorial:ℂ)⁻¹ • A^n'; let S(n':ℕ):=(n'.factorial:ℝ)⁻¹*C^n'
 have hv := show Summable V from (norm_expSeries_summable' (𝕂:=ℂ) A).of_norm; have h:= (norm_expSeries_summable' (𝕂:=ℝ) C).of_norm; have H : Summable S:= h
 have hp:=p.1; have ht:HasSum (fun n:ℕ=>V (n+1)) (exp A-1):=by
    rw [congrFun (exp_eq_tsum ℂ),← hv.sum_add_tsum_nat_add 1]; simpa [V,sum_range_one] using ((summable_nat_add_iff 1).mpr hv).hasSum -- tune
 have hS: HasSum (fun n:ℕ=> S (n+1)) (Real.exp C-1):=by
    rw [Real.exp_eq_exp_ℝ,congrFun (exp_eq_tsum ℝ)]; change HasSum _ ( (∑' i,S i)-1); rw [← H.sum_add_tsum_nat_add 1]; simpa [S] using ((summable_nat_add_iff 1).mpr H).hasSum
 refine ⟨sub_nonneg.mpr (Real.one_le_exp hp),fun i j w p' g u=> ?_⟩
 let W(X:FC n):=‖inner ℂ i (acts (rollC ton u) (acts X j))‖
 have hu:Continuous W:=(continuous_const.inner (ContinuousLinearMap.continuous (acts (rollC ton u))|>.comp (acts_cont.clm_apply continuous_const))).norm
 refine le_of_tendsto_of_tendsto (hu.continuousAt.tendsto.comp (ht.tendsto_sum_nat)) ((hS.tendsto_sum_nat.mul_const w).mul_const (size_k _ k u)) (Eventually.of_forall fun l:ℕ=> ((sumT _ _ (fun n=> S (n+1)) (fun i _=>?_)).2 _ _ w p' g u)) -- tune inference
 unfold S; have he:‖(((i+1).factorial:ℂ))⁻¹‖=((i+1).factorial:ℝ)⁻¹:=by simp; -- scope
 exact he ▸ ((p.power _).linear _)
lemma brick (h:0 ≤ k)(x:Op n)(e:‖x‖ ≤ C):Pays k (dg x) (C*(Fintype.card n)^2*k^2) :=by
 unfold dg dyad; have ht(i:n):Pays k (put i) k:=by
    have he:=tone (n:=n) (false,basisKet i) h; simpa [ton,creed] using he
 have hr(i:n):Pays k (takeF i) k:=by have he:=tone (n:=n) (true,basisKet i) h; simpa [ton,creed] using he
 let f (i j:n):= x i j • (put i*takeF j); have he:= sumT (n:=n) Finset.univ (fun i=> ∑ j,f i j) (fun i:n=> ∑ _:n,C*(k*k)) (fun i _=> sumT Finset.univ (f i) (fun _:n=> C*(k*k)) (fun j _=> (((ht i).mul (hr j)).linear (x i j)).weigh (mul_le_mul_of_nonneg_right ((norm_entry _ i j).trans e) (mul_nonneg h h)) h)); convert he using 1; simp; ring
end Pays
end YM.CF.Pic
