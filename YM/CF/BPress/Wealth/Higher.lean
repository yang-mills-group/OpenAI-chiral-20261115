import YM.CF.BPress.Wealth.Hess
/-! Remaining `eq:B-Hess`: spectral upper form & ranges and severe identity entries. En Route to B-jcost. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Wealth
open Function Filter MeasureTheory LocalH Lattice Wilson RG Precision Grid Push.AbsoluteSums Branch Ledger Cube Bands Tunnel Pressure Finset
open scoped Topology BigOperators Classical Matrix Matrix.Norms.Frobenius InnerProductSpace ContDiff
open SU Gauge
attribute [local instance] Gauge.frobInner
variable {s:Side}{B:BandWidth}(X:Bands s B) (M:ℕ) (R:PathData group)(d:Clip) (β y:ℝ){σ C Λ:ℝ}(H:R.Bounds d σ C Λ)(S:Finset X.Hcols)
def payUpper (M D:ℕ) (C:ℝ) := 1+ ((d.direct+ chPrice)*2*(coefH M C)^2*(counted M D))
set_option maxRecDepth 4000 in
lemma pay_upper (p: High B M) (t:0 < y)(c:β∈ Set.Icc (y/2) (2*y))(w:RaySpace X) : inner ℝ w (hessian X M R d β y H S w) ≤ payUpper d M B.D C * ‖w‖^2:=by
 let K:=(d.direct+chPrice)*2; have hk:0≤K:=by unfold K; positivity [d.quadratic_pos,chPrice_pos]
 let v:=coefH M C; have hC:= budget_nonneg H.three; have hv:0≤v:=by unfold v coefH; positivity
 let f(i:Root s):= inner ℝ w (columnP X M R d β y H i w); let P:= Θ X M S; let q(i:Root s):= ‖keepOnly X (danger X M i) w‖
 have he(i)(h:i∈P): f i ≤ (K*v^2)*q i^2 := by unfold f; rw [quadP]; apply le_trans (mul_le_mul (gate_safe d β y t c i).2 (pow_le_pow_left₀ (norm_nonneg _) (shine_price M R H i ((mem_filter.mp h).2).1 p w) _) (sq_nonneg _) hk); exact Eq.le (by unfold q v; ring)
 let N:=counted M B.D; have hit : ∑ i∈P,q i^2 ≤ (N:ℝ)*‖w‖^2:=by
   unfold q; simp_rw [tally_ray]; rw [sum_comm,ray_price, mul_sum]; refine sum_le_sum (fun i _=>?_)
   rw [← sum_filter,sum_const,nsmul_eq_mul]; gcongr; apply Nat.cast_le.mpr; apply le_trans (card_le_card ?_) (ticket_copies p i.1)
   intro j v; obtain ⟨b,f⟩:= mem_filter.mp v; exact mem_filter.mpr ⟨ mem_univ _, ((mem_filter.mp b).2).1, danger_sub j X M f⟩
 have ht: ‖keepOnly X S w‖^2 ≤ ‖w‖^2:= (show _ from (by rw [splitSoft _ S (w:=w)]; linarith only [sq_nonneg ‖keepOnly X Sᶜ w‖])) -- tune rewrite self both
 have h':∑ i∈P, f i≤ K*v^2 * ((N:ℝ)*‖w‖^2):=by apply (sum_le_sum he).trans; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left hit (mul_nonneg hk (sq_nonneg _))
 unfold hessian; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, inner_add_right, inner_sum]; apply le_trans (add_le_add h' ((mask_norm X S w).le.trans ht)); change _ ≤ (1+ K*v^2*N)*_; exact Eq.le (by ring) -- tune
-- PL since M from price and B.D constant guard gap.
lemma upper_PL (D:ℕ)(M:ℝ→ℕ)(p: PL fun i=>(M i:ℝ)) : PL fun i=> payUpper d (M i) D C:= PL.add (PL.const 1) ((PL.const ((d.direct+chPrice)*2*(coefH 0 C)^2)).mul (counted_PL D M p)) -- tune defeq

-- SEV identity subspace
lemma low_zero (w:RaySpace X)(i : Root s) (p:regular S (M:=M) (X:=X) i) : keepOnly X (danger X M i) (keepOnly X S w)=0:= by
 ext x; by_cases v:x.1.1∈danger X M i; have he:= disjoint_left.mp (Disjoint.symm p) v; simp [keepOnly, v, he]; simp [keepOnly, v]
lemma hess_sev (w:RaySpace X)(p:High B M): hessian X M R d β y H S (keepOnly X S w)=keepOnly X S w:=by
 unfold hessian; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]; rw [sum_eq_zero, zero_add]; exact id_mask ..
 intro i v; unfold columnP; simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]; obtain ⟨h,f⟩:=(mem_filter.mp v).2; simp only [← beaming M R H i h p (keepOnly X S w), low_zero X M S w i f, map_zero,smul_zero]
lemma only_mark (w : RaySpace X) (p:High B M) : keepOnly X S (hessian X M R d β y H S w)=keepOnly X S w:=by
 refine ext_inner_left ℝ fun y'=>?_ ; rw [←ray_mask,←ray_mask]; let h:= section_sym X M R d β y H S; exact (((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).1 h) (keepOnly X S y') w).symm.trans (by change inner ℝ ((hessian X M R d β y H S) (keepOnly X S y')) w=_; rw [hess_sev X M R d β y H S y' p]) -- tune adj map coerces
-- entry dependence from row index. full reach semantics.
def zSite (i:Axon X): X.Hcols:= i.1.1
def q_ray (i:Axon X):RaySpace X:= EuclideanSpace.single i 1
def rowM (P:BEnd X) : Matrix (Axon X) (Axon X) ℝ:=Matrix.of fun i j=> inner ℝ (q_ray X i) (P (q_ray X j))
def reaches (F:BEnd X) (r:ℕ):Prop:= ∀ i j : Axon X, zSite X j∉ columnBall X (zSite X i) r→ rowM X F i j=0
def houseRead (T: Finset X.Hcols → BEnd X) (r:ℕ):Prop:=∀ (S S':Finset X.Hcols), ∀ i:Axon X,(∀ p∈ columnBall X (zSite X i) r,p∈ S ↔ p∈ S')→∀ j, rowM X (T S) i j = rowM X (T S') i j
lemma reach_add {u v w:X.Hcols}{t r:ℕ}(g:u∈columnBall X v t)(f:w∈columnBall X u r): w∈columnBall X v (t+r):=by obtain ⟨a,b⟩:=column_eq.mp f; obtain ⟨c,d⟩:=column_eq.mp g; exact column_eq.mpr ⟨a.trans c,(delta_triangle _ _ _).trans (add_le_add d b)⟩
lemma q_at (S:Finset X.Hcols)(i:Axon X):keepOnly X S (q_ray X i)= if zSite X i∈ S then q_ray X i else 0 := by
 ext j; split; next h=> by_cases v:j=i; subst j; simp [keepOnly,show i.1.1∈S from h,q_ray]; simp [keepOnly,q_ray, EuclideanSpace.single_apply,v]
 next h=> by_cases v:j=i; subst j; simp [keepOnly,(show i.1.1∉ S from h), q_ray]; simp [keepOnly,q_ray,EuclideanSpace.single_apply,v]
lemma offset_entry (i:Axon X)(j:Root s)(w:RaySpace X)(h:retained X M j)(t:High B M) (p:zSite X i ∉ danger X M j) : inner ℝ (q_ray X i) ((columnP X M R d β y H j) w)=0:=by rw [act2,← beaming M R H j h t (q_ray X i), q_at,if_neg p,map_zero, inner_zero_left,mul_zero]
lemma hessian_reach (p:High B M) : reaches X (hessian X M R d β y H S) (6*M) := by
 intro i j f; unfold rowM; simp only [Matrix.of_apply,hessian,ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, inner_add_right, inner_sum]; rw [sum_eq_zero]; swap
 · intro k v; let a:= zSite X i; let b:=zSite X j; let P:= danger X M k; have e:= ((mem_filter.mp v).2).1; by_cases h:a ∉ P; exact offset_entry X M R d β y H i k _ e p h; rw [act_sym]; apply offset_entry X M R d β y H j k _ e p; intro y; apply f; rw [show 6*M=3*M+3*M by omega]; apply reach_add X (v:=a) (u:=block X M k) _ _; exact column_sym.mpr (danger_sub k X M (of_not_not h)); exact danger_sub k X M y
 rw [zero_add]; change inner ℝ _ (keepOnly X S (q_ray X j))=0; rw [q_at]; split; next h=> have ht:i≠j:=fun u=> f (u ▸ column_self ..); simp [q_ray, EuclideanSpace.inner_single_left, ht]
 next t=> simp
lemma hessian_plan (p:High B M) : houseRead X (hessian X M R d β y H) (6*M) := by
 intro S T i e j; unfold rowM; simp only [Matrix.of_apply,hessian,ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply, inner_add_right, inner_sum]; congr 1; swap
 · have h:= e _ (column_self (zSite X i) (6*M)); change inner ℝ _ (keepOnly X S _)=inner ℝ _ (keepOnly X T _); rw [← ray_mask, ←ray_mask, q_at,q_at]; split_ifs <;> tauto
 unfold Θ; rw [sum_filter,sum_filter]; refine sum_congr rfl fun k _=>?_ ; by_cases h:retained X M k; swap; · simp [h]
 simp only [h,true_and]; by_cases v: zSite X i∈rangeTh X M k; swap; · have ht:zSite X i ∉ danger X M k:=fun w=> v (danger_sub k X M w); simp only [offset_entry X M R d β y H i k _ h p ht,ite_self]
 rw [show regular (X:=X) (M:=M) S k=regular (X:=X) (M:=M) T k from propext (use_same (fun t w=> e t (by rw [show 6*M=3*M+3*M by omega]; exact reach_add X (column_sym.mpr v) w)))]
end YM.CF.BPress.Wealth
