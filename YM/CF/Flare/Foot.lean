import YM.CF.Flare.Wits
set_option autoImplicit false
noncomputable section
namespace YM.CF.Flare
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N:Side}{b:Candle}{S:Slide N b}{j:ℕ}{M:Jill.Male}{k u r a v:ℝ}
lemma rod(j)(C:ℝ)(b: heave r≤C)(p:0<r):∃ c:ℝ,0<c∧∀ N:Side,Even N.val→ r *pinch N^2≤1/8→∀ d:Candle,∀ S:Slide N d,∀ M:Jill.Male,∀ s:ℝ,s∈Set.Icc (heave r) C→ let T:=risky S j M r; let Q:=portT S M j r s; let V:=mateV T (s*pinch N); ∃ U:Stag N→Op SpinIdx, (∀ i,Clad (field S j M i) Aop (Q i) (V i) (U i))∧ (∀ i,‖U i‖ ≤ c*N.val) ∧ ‖laneP (tickA N) (Dofu N Q) (Dofu N U)‖+1≤ c*N.val ∧∀ i,‖Q i‖≤c:=by
 let b':=1+C*Real.pi; let a:=(4/(heave r)+(Real.sqrt r)⁻¹)/Real.pi; have hb:=heave_p r; have hp:=Real.pi_pos; have hc:0<C:=hb.trans_le b; have hg:0<b':=by unfold b'; positivity; -- tune
 have ha:0<a:=by unfold a; positivity; -- tune
 let c:=b'*a+1+a+b'; have hv:0<c:=by unfold c; positivity; -- tune
 refine ⟨c,hv,fun N g w d S M s t=>?_⟩; intro T Q V; have ht:= N.property
 have he : 1≤(N.val:ℝ):=by exact_mod_cast ht
 have hs:0<s:=hb.trans_le t.1; have hm:0<pinch N:=pinch_pos _; obtain ⟨U,u⟩:=acre j S g M p w t.1
 have hx(i:Stag N):‖Q i‖≤ b':=by
    change ‖(1+(s*pinch N) • shake T i)‖≤_; apply (norm_add_le ..).trans; rw [norm_smul,norm_one,Real.norm_of_nonneg (by positivity)]; unfold b'; apply add_le_add_right; -- inspect
    apply le_trans (mul_le_of_le_one_right (by positivity) (show ‖shake T i‖ ≤ 1 from ?_)); exact mul_le_mul t.2 (div_le_self hp.le he) hm.le hc.le; unfold shake; split; exact warp_norm; simp
 have hK(i:Stag N):‖U i‖≤ a*N.val:=(u i).2.trans_eq (by unfold a pinch; field_simp)
 refine ⟨U,fun i=>(u i).1,fun i=>(hK i).trans (mul_le_mul_of_nonneg_right (by unfold c; linarith [mul_pos ha hg]) (by positivity)),?_,fun i=>(hx i).trans (by unfold c; nlinarith)⟩
 unfold laneP; have hp:‖Dofu N Q‖≤ b':=markQ _ hg.le hx; have h:= markQ U (by positivity) hK; have hz:‖(1-tickA N)*Dofu N Q‖ ≤ b':=(norm_mul_le ..).trans ((mul_le_mul (IsStarProjection.norm_le _ (cut_t N).one_sub) hp (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
 exact (add_le_add ((norm_mul_le ..).trans (mul_le_mul hz h (norm_nonneg _) hg.le)) he).trans (by unfold c; nlinarith [mul_pos (show 0<(N.val:ℝ) by positivity) (add_pos ha hg)])
def size_k(n:Type*)[Fintype n][LinearOrder n](d:ℝ)(q:List (Reader0 n)):= unitsC n q*d^q.length
lemma wage(Q:FC (Single N))(i:Wave (Single N))(s:ℝ)(T:Finset (Stag N))(w:ℕ)(g: T.card*4<w):inner ℂ (mateK N) (acts Q i)=∑ j∈range w,(bead w (-1) j:ℂ) * inner ℂ (mateK N) (acts (Q*quant (Dofu N (openW T ((j+1:ℝ)*s)))) i):=by
 let Y(j:ℕ):= Dofu N (openW T ((j+1:ℝ)*s)); let f(j:ℕ):ℂ:=bead w (-1) j
 let Z:=∑ j∈range w,f j • (quant (Y j)); have ht:Z=1:=redeem T w g s
 nth_rw 1 [show Q=Q*Z from (by rw [ht,mul_one])]; unfold Z; rw [Matrix.mul_sum,act_sum,inner_sum]; apply sum_congr rfl; intro l _; rw [Matrix.mul_smul,act_smul,inner_smul_right]
lemma count_curve {n:Type*}[Fintype n][LinearOrder n](q:List (Reader0 n)): 0≤unitsC n q:=by induction q with | nil=>simp [unitsC]| cons a q ih=>exact mul_nonneg (norm_nonneg a.2) ih -- simp defeq
lemma tuneup(H:1≤j)(p:0<r):∃ G C:ℝ,0<G∧0<C∧∀ N:Side,Even N.val→ r *pinch N^2≤1/8→∀ b:Candle,∀ S:Slide N b,∀ M:Jill.Male,∀ x:Wave (Single N),Sea (Dofu N (field S j M)) x→∀ y:List (Reader0 (Single N)),‖inner ℂ (mateK N) (acts (rollC ton y) x)‖≤ G*iceK j S M r * size_k _ (C*N.val) y:=by
 obtain ⟨l,h⟩:=risky_card j H r p; let w:= l*4+1; let C:ℝ:=(w+1:ℝ)*heave r; have hx:= heave_p r; have hc:heave r ≤ C:= le_mul_of_one_le_left hx.le (by simp)
 obtain ⟨c,hb,V⟩:=rod j C hc p; obtain ⟨B,u,U⟩:=octant j H p hc; obtain ⟨v,hv,Z⟩:=bead_bound w
 refine ⟨v*B,c,mul_pos hv (zero_lt_one.trans_le u),hb,fun N w' l' b s M i k y=>?_⟩; let T:=risky s j M r; let Y:=size_k _ (c*N.val) y; have hy:0≤Y:=mul_nonneg (count_curve y) (by positivity)
 let a:=iceK j s M r; have ha:0<a:=ice_p _ _ _ p
 rw [wage _ i (heave r*pinch N) T w (by unfold T w; have h:= h N w' b s M; omega)]; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun j' => |bead w (-1) j'| * (B*a*Y)) ?_).trans ?_)
 · intro i' hi; let t:=(i'+1:ℝ)*heave r; have ht:t∈ Set.Icc (heave r) C:=by refine ⟨le_mul_of_one_le_left hx.le (by simp),mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_succ (mem_range.mp hi).le) hx.le⟩
   let F:=portT s M j r t; let W:= mateV T (t*pinch N); rw [norm_mul,Complex.norm_real, Real.norm_eq_abs,show openW T (_ *(heave r*pinch N))=F from (by unfold F portT; rw [←mul_assoc])]
   obtain ⟨K,v,e,X,R⟩:=V N w' l' b s M t ht; have hv:= torn s w' j M K F W v; exact mul_le_mul_of_nonneg_left ((motto hv _ _ k (tickB N) y X).trans (mul_le_mul_of_nonneg_right (U _ w' l' b s M t ht.1 ht.2 i k) hy)) (abs_nonneg _)
 rw [←sum_mul]; exact (mul_le_mul_of_nonneg_right (Z _ (by norm_num)) (mul_nonneg (mul_nonneg (zero_le_one.trans u) ha.le) hy)).trans_eq (by unfold a Y; ring)
end YM.CF.Flare
