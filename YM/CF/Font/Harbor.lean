import YM.CF.Font.Hitch
set_option autoImplicit false
noncomputable section
namespace YM.CF.Font
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L c f n:Side}{a b A B D:ℝ}{m:ℕ}
lemma bud_dec {G:Ratio c f}{K:Matrix (Single f) (Single c) ℂ}(x:BudH G K a B)(h:b≤a)(hp:B≤D): BudH G K b D:=by
 constructor
 · intro i; apply le_trans _ ((x.stem i).trans (mul_le_mul_of_nonneg_right hp (Vpos [] G.count |>.le))); refine sum_le_sum fun j _=> ?_; unfold bolt; gcongr
 intro i; apply le_trans _ ((x.hip i).trans (mul_le_mul_of_nonneg_right hp (by have:=Vpos [] G.count; positivity))); refine sum_le_sum fun j _=> ?_; unfold bolt; gcongr
abbrev Trip(m:ℕ)(n:Side):= Fin m→ PrizeX n
private lemma multx {ι:Type*}[Fintype ι](F:Fin m→ι→ℝ)(U V:ℝ)(v:0≤V)(e:∀ i,∑ j,F i j ≤ V)(p:∀ i j,0≤F i j): ∑ x:Fin m→ι, ∏ i,F i (x i) ≤ V^m:=by
 classical
 induction m with
 | zero=> simp
 | succ m ih=>
    rw [← (Fin.consEquiv (α:= fun _=> ι)).sum_comp, Fintype.sum_prod_type]
    let f(j):=∑ x: Fin m→ι,(F 0 j)*∏ i,F (Fin.succ i) (x i)
    rw [show ∑ x:ι, (∑ y:Fin m→ι,∏ i,F i _) = ∑ x:ι,f x from ?_]; swap; · refine sum_congr rfl fun i _=> sum_congr rfl fun j _=> ?_; rw [Fin.prod_univ_succ]; rfl
    unfold f; simp_rw [← mul_sum]; rw [← sum_mul, pow_succ']; exact mul_le_mul (e _) (ih _ (fun i=>e _) (fun i=>p _)) (sum_nonneg fun _ _=> prod_nonneg fun _ _=>p _ _) v
private def skinL (x:Fin m→ Ps (More n)):Trip m n:= Sum.inl ∘ x
private lemma tips(g:Trip m n)(h:∀ i,∃ a,g i=.inl a):∃ x: Fin m→ Ps (More n), g=skinL x:=by choose f p using h; exact ⟨f,funext p⟩
private lemma infi: Injective (skinL (n:=n) (m:=m)):=fun _ _ h=>funext fun i=> Sum.inl.inj (congr_fun h i)
private lemma burnt(t:Trip m n)(e:¬∃ x: Fin m→ Ps (More n),t=skinL x):∃ i :Fin m,∃ a:Axis,t i=.inr a:=by
 contrapose! e; apply tips; intro i; cases h:t i; exact ⟨_,rfl⟩; exact (e _ _ h).elim
variable {Λ:Ps (More f)→Ps (More c)→ℝ}{K:PrizeX f → PrizeX c→ℝ}
lemma rubrics1 (G:Ratio c f)(x y:Single f)(i j:Single c)(r: Fin m→ Ps (More f))(h:0<a)(k:0≤b)(hb:b≤a/2)(hA:0≤A)(Y:Rails (ratio G) A a Λ) (M:ℝ) (Q:SweepH Λ K M): let L:=spanV G
 (∑ t:Trip m c,nick b (notx m i j t)*∏ u,‖K (skinL r u) (t u)‖) ≤ cashH a m *nick b (notx m x y (skinL r))*bolt (((m:ℝ)+1)*a) G x i *bolt a G y j* (A/L^2)^m:=by
 classical
 intro L
 let S:= univ.image (@skinL c m) -- order
 let f(t:Trip m c):= nick b (notx m i j t)*∏ u,‖K (skinL r u) (t u)‖
 let P(u:Fin m)(z:Ps (More c)):= Faro a ((ratio G).parent (r u).1) z.1 * ‖Λ (r u) z‖
 let W:= cashH a m *nick b (notx m x y (skinL r))*bolt (((m:ℝ)+1)*a) G x i *bolt a G y j
 have hw :0≤W:=by
    unfold W cashH; exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (nick_pos _ (by positivity)|>.le) (Iteration.momentPrice_pos _ (half_pos h)|>.le)) (nick_pos _ (notx_zero ..)|>.le)) (Real.exp_pos _|>.le)) (Real.exp_pos _|>.le)
 change ∑ t, f t≤_
 rw [← sum_subset (subset_univ S)]; swap
 · intro t _ hx; obtain ⟨u,v,H⟩:=burnt t (fun ⟨x,hx'⟩=>hx (mem_image.mpr ⟨x,mem_univ _,hx'.symm⟩)); unfold f; rw [prod_eq_zero (mem_univ u),mul_zero]; rw [H]; simp [skinL,Q.mouth,remit]
 rw [show S=_ from rfl, sum_image infi.injOn];
 apply le_trans (b:= W*∑ t: Fin m→Ps (More c),∏ u,P u (t u)); swap; · exact mul_le_mul_of_nonneg_left (multx P 1 (A/L^2) (div_nonneg hA (by positivity)) (fun i=>Y.rate _) (fun i j=>mul_nonneg (Real.exp_pos _|>.le) (norm_nonneg _))) hw
 rw [mul_sum]; refine sum_le_sum ?_; intro t _; unfold P f; rw [prod_mul_distrib,←mul_assoc W]; simp only [skinL,Function.comp_apply,Q.mouth,remit,Sum.elim_inl]; refine mul_le_mul_of_nonneg_right (wages G x y i j r t h k hb) (prod_nonneg fun _ _=>norm_nonneg _)
theorem rubrics (A a:ℝ)(st:ℝ)(h:0<a)(v:0<A)(k:0≤st)(m:ℕ)(s:m≤2)(L:Side)(gL:4≤ L.val) (b:ℝ)(hb:0<b)(p:b≤a/2):∃ N:ℕ,∀ {f c:Side}(G:Ratio c f),G.count=L→N≤(More c).val→∀ Λ K,Rails (ratio G) A a Λ → SweepH Λ K st→∀ x y:Single f,∀ i j:Single c,∀ r:Trip m f,
 (∑ t: Trip m c,nick b (notx m i j t)*∏ u, ‖K (r u) (t u)‖) ≤ cashH a m *nick b (notx m x y r)*bolt (((m:ℝ)+1)*a) G x i *bolt a G y j* (A/(spanV G)^2)^m:=by
 have hx :0<cashH a m:=mul_pos (nick_pos _ (by positivity)) (Iteration.momentPrice_pos _ (half_pos h))
 let Y:= A/(L.val:ℝ)^2; have hv:0<Y:=by unfold Y; positivity
 let C:= cashH a m*Y^m; have hC:0<C:=mul_pos hx (pow_pos hv m)
 obtain ⟨V,W⟩:=probate gL st A 1 C b one_pos hC hb
 refine ⟨V,fun {f c} G he hp Λ K Q T x y i j r=>?_⟩
 classical
 by_cases hz:∃ u,r=skinL u
 · obtain ⟨z,H⟩:=hz; subst r; exact rubrics1 G x y i j z h hb.le p v.le Q st T
 obtain ⟨u,z,U⟩:=burnt r hz
 let g:=ratio G; let x':ℝ:=(More c).val; let sH:= 3*x'; let X:=1+|A|+|tall (More f) (More c) st|; have ht:1≤X:=by unfold X; linarith [abs_nonneg A,abs_nonneg (tall (More f) (More c) st)]
 let F(j:Fin m)(z):=‖K (r j) z‖; have hl : ∑ t:Trip m c,∏ u,F u (t u) ≤ X^2:=by
   apply (multx F 1 X (zero_le_one.trans ht) (fun i=>le_trans (totalH g T h Q k v.le (r i)) ?_) (fun _ _=> norm_nonneg _)).trans; exact pow_le_pow_right₀ ht s
   unfold X; linarith [le_abs_self A,le_abs_self (tall (More f) (More c) st)]
 have hh(t:Trip m c): notx m i j t≤ sH:=by
   have hG: (m:ℝ)≤2:=by exact_mod_cast s
   have hl1: (∑ u:Fin m,(dial (place_x i) (t u):ℝ)) ≤ m*x':=(sum_le_sum (fun u (_:u∈univ)=> (show (dial (place_x i) (t u):ℝ)≤ x' from Nat.cast_le.mpr (lowN ..)))).trans_eq (by simp)
   unfold notx; refine (add_le_add (size_q ..) hl1).trans ?_; change x'+m*x'≤ sH; have ht:0<x':=by unfold x'; positivity; -- tune
   unfold sH; nlinarith only [ht,hG]
 have hr: ((More f).val:ℝ) ≤ notx m x y r :=by
    unfold notx; refine (le_trans (b:= (dial (place_x x) (r u):ℝ)) ?_ (single_le_sum (f:=fun j=> (dial (place_x x) (r j):ℝ)) (fun j _=>Nat.cast_nonneg _) (mem_univ u))).trans (le_add_of_nonneg_left (Nat.cast_nonneg _)); rw [U]; rfl -- tune
 have hW:X^2*nick b sH≤ C*nick b (More f).val:=by simpa only [mul_one] using W g hp (show g.count=L from he)
 have hk (a:ℝ)(p:0≤a)(x z):1≤ bolt a G x z:=Real.one_le_exp (mul_nonneg p (by positivity))
 calc
    _ ≤ nick b sH *∑ t:Trip m c,∏ u,F u (t u):=by rw [mul_sum]; exact sum_le_sum fun t _=>mul_le_mul_of_nonneg_right (nick_inc hb.le (notx_zero ..) (hh t)) (prod_nonneg fun _ _=> norm_nonneg _)
    _ ≤ _:=by
       apply (mul_le_mul_of_nonneg_left hl (nick_pos _ (by unfold sH x'; positivity)|>.le)).trans; rw [mul_comm]; refine hW.trans ?_; apply (mul_le_mul_of_nonneg_left (nick_inc hb.le (Nat.cast_nonneg _) hr) hC.le).trans
       rw [show C*nick b (notx m x y r) = cashH a m* nick b (notx m x y r)*(A/spanV G^2)^m by unfold C Y spanV; rw [he]; ring]
       let V:=cashH a m*nick b (notx m x y r); have hP:0≤V:=mul_nonneg hx.le (nick_pos _ (notx_zero ..)|>.le); apply mul_le_mul_of_nonneg_right _ (by unfold spanV; positivity); change V≤V*_ * _; rw [mul_assoc]; exact le_mul_of_one_le_right hP (one_le_mul_of_one_le_of_one_le (hk _ (by positivity) _ _) (hk a h.le y j))
end YM.CF.Font
