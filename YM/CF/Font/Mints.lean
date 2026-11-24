import YM.CF.Font.Harbor
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Font
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L c f n:Side}{a b A C D B:ℝ}{m:ℕ}
-- abstract multilinear endpoints use later.
abbrev Emit(m:ℕ)(c:Side)(E:Type*) := Single c→Single c→ Trip m c→E
def balance {E:Type*}[NormedAddCommGroup E] (b:ℝ)(f:Emit m n E)(x:Single n):= ∑ y,∑ i, nick b (notx m x y i)*‖f x y i‖
def tapH {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E](U V:Matrix (Single f) (Single c) ℂ)(K:Single f→Single c→PrizeX f→ PrizeX c→ℝ)(f':Emit m f E):Emit m c E:=
 fun i j t=> ∑ x,∑ y,∑ r:Trip m f, ((star (U x i)*V y j)*(↑(∏ u, K x i (r u) (t u)):ℂ)) • f' x y r
lemma tap_cost {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E](G:Ratio c f){K:Single f→Single c→PrizeX f→ PrizeX c→ℝ}{U V:Matrix (Single f) (Single c) ℂ}(g:BudH G U (((m:ℝ)+1)*a) C)(s:BudH G V a D)(e:0<a)(h:0<A)(w:∀ x y: Single f,∀ i j:Single c,∀ r:Trip m f,
 (∑ t: Trip m c,nick b (notx m i j t)*∏ u,‖K x i (r u) (t u)‖) ≤ cashH a m *nick b (notx m x y r)*bolt (((m:ℝ)+1)*a) G x i *bolt a G y j* (A/(spanV G)^2)^m)(f':Emit m f E)(hC:0<C)(hD:0<D)(p:0≤ B)(hv:∀ x,balance b f' x≤ B) : let L:=spanV G;∀ x,balance b (tapH U V K f') x ≤ B* (C*D)*cashH a m*L*(A/L^2)^m :=by
 intro L i
 let t:= (A/L^2)^m; have hl:0<L:=span_pos; have ht:0<t:=by unfold t; positivity; -- tune
 let a':=((m:ℝ)+1)*a; let X:=cashH a m; let W(x):= bolt a' G x i*‖U x i‖; let v:= followV [] G.count; have hh:v>0:= Vpos ..
 have hX:0<X:=mul_pos (nick_pos _ (by positivity)) (Iteration.momentPrice_pos _ (half_pos e))
 let P:=tapH U V K f'; let F(j t x y r):=nick b (notx m i j t)* (‖f' x y r‖*‖U x i‖ * ‖V y j‖*∏ u,‖K x i (r u) (t u)‖)
 have he (j t): nick b (notx m i j t) *‖P i j t‖≤ ∑ x,∑ y,∑ r,F j t x y r:=by
    apply mul_le_mul_of_nonneg_left (norm_sum_le ..) (nick_pos b (notx_zero m i j t)|>.le) |>.trans; simp_rw [mul_sum]; refine sum_le_sum fun x _=> ?_; refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) (nick_pos b (notx_zero m i j t)|>.le)).trans ?_; simp_rw [mul_sum]; refine sum_le_sum fun y _=> ?_; refine (mul_le_mul_of_nonneg_left (norm_sum_le ..) (nick_pos b (notx_zero m i j t)|>.le)).trans ?_; simp_rw [mul_sum]; apply sum_le_sum; intro r _; unfold F; apply le_of_eq; rw [norm_smul,norm_mul,norm_mul,norm_star,Complex.norm_real, norm_prod]; ring
 let Q (x y r):= ∑ j,∑ t,F j t x y r
 have hx(x y r): Q x y r ≤ X* W x*t*(D*v) * (nick b (notx m x y r)* ‖f' x y r‖):=by
    let c:=X*W x*t*(nick b (notx m x y r)* ‖f' x y r‖); have hY :0≤c:=by unfold c W bolt; exact mul_nonneg (by positivity) (mul_nonneg (nick_pos b (notx_zero ..)|>.le) (norm_nonneg _))
    calc
     _ ≤ c* ∑ j,bolt a G y j*‖V y j‖:=by
       rw [mul_sum]; apply sum_le_sum; intro j _; let C:= ‖f' x y r‖ * ‖U x i‖ * ‖V y j‖
       have hx(t): F j t x y r=C* (nick b (notx m i j t)* ∏ u,‖K x i (r u) (t u)‖):=by unfold F C; ring
       simp_rw [hx,← Finset.mul_sum]; apply (mul_le_mul_of_nonneg_left (w x y i j r) (show 0≤C by unfold C; positivity)).trans_eq; unfold c t X C W L a'; ring
     _ ≤ _:= (mul_le_mul_of_nonneg_left (s.stem y) hY).trans_eq (by unfold c; ring)
 have hg(x):∑ y, ∑ r,Q x y r ≤ (X*t*(D*v)*B)*W x:=by
    let A:= X* W x*t*(D*v); have hp:0≤A:=by unfold A W bolt; positivity
    apply (sum_le_sum (fun y (_:y∈univ)=> sum_le_sum fun r (_:r∈univ)=> hx x y r)).trans; simp_rw [← Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left (hv x) hp).trans_eq (by unfold A; ring)
 apply (sum_le_sum (fun j (_:j∈univ)=>sum_le_sum fun t (_:t∈univ)=> he j t)).trans
 have hs (f:Single c→Trip m c→Single f→Single f→Trip m f→ℝ): (∑ i,∑ j,∑ x,∑ y,∑ r,f i j x y r)=∑ x,∑ y,∑ r,∑ i,∑ j,f i j x y r:=by
    have ht (I): (∑ j,∑ x,∑ y,∑ r,f I j x y r)=∑ x,∑ y,∑ r,∑ j,f I j x y r:=by rw [sum_comm]; refine sum_congr rfl fun x _ =>?_ ; rw [sum_comm]; refine sum_congr rfl fun y _=>?_ ; rw [sum_comm]
    simp_rw [ht]; rw [sum_comm]; refine sum_congr rfl fun x _=>?_; rw [sum_comm]; refine sum_congr rfl fun y _=>?_ ; rw [sum_comm]
 apply le_trans ?_ ((sum_le_sum (fun x (_:x∈univ)=> hg x)).trans ?_)
 · exact (hs F).le
 rw [←Finset.mul_sum]; apply (mul_le_mul_of_nonneg_left (g.hip i) (by positivity : 0≤ X*t*(D*v)*B)).trans_eq
 have hP: v^2=L/(L^4):=by
    unfold v followV; simp only [List.length_nil,zero_add,div_pow,Real.sq_sqrt (Nat.cast_nonneg _)]; unfold L spanV; ring
 calc
  _ = B*(C*D)*X* (L^4*v^2)*t:=by unfold L t v spanV; ring
  _ = _:=by rw [hP]; change B*_ * X*_ * t=B*_ * X*L*t; field_simp
end YM.CF.Font
