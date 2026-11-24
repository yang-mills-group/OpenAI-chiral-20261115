import YM.CF.Ember.Mount
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N : Side}{ι:Type*}
lemma riverB(k:Site N):river (bark k)=tmap (pm k):=by unfold river bark; rw [MeasurableEquiv.apply_symm_apply]; rfl
lemma bark_inside(k:Site N): bark k∈ boundsEarth:= fun i=> by change exileE (bark k) i∈ _; rw [bark,MeasurableEquiv.apply_symm_apply]; exact inZone (k i)
def minH(N:Side): Momentum:=river (bark (0:Site N))
lemma minimal (i): minH N i=(pinch N:ℂ):=by
 rw [minH,riverB]; change (Lat.principal 0:ℂ)=_ -- bind N
 rw [Lat.principal,tone]; simp only [ZMod.val_zero, Nat.cast_zero,mul_zero,zero_add,one_mul]; rw [if_pos]
 have h : (1:ℝ)≤N.val:=by exact_mod_cast N.property
 unfold pinch; exact div_le_self Real.pi_pos.le h
def cexpR(z:ℂ): ℂ:= Complex.exp (z*Complex.I)
def tinc (N:ι→Side):Tax ι:=⟨fun i=> pinch (N i),Real.pi,fun i=>pinch_pos _,fun i=>by unfold pinch; exact div_le_self Real.pi_pos.le (by exact_mod_cast (N i).property)⟩
private lemma yen0 (N:ι→Side)(f:ℂ→ℂ)(h:∀ x,DifferentiableAt ℂ f x)(e: f 0=0):Act (tinc N) 1 fun i _=> f (pinch (N i)):=by
 let T:=tinc N; let H:=closedBall (0:ℂ) (T.cap+1); have hk : IsCompact H:=isCompact_closedBall ..; have hg:= Differentiable.continuous h
 obtain ⟨C,hc⟩:=hk.bddAbove_image (hg.norm.continuousOn); let A:=max C 1; have hA:0<A:=lt_max_of_lt_right one_pos; have hp:0<T.cap+1:=by unfold T tinc; change 0<Real.pi+1; positivity
 refine ⟨1,A/(T.cap+1),one_pos,by positivity,fun i z hz=>⟨differentiableAt_const _,?_⟩⟩
 have he:T.r i < T.cap+1:= lt_of_le_of_lt (T.hold i) (by linarith)
 let t:ℂ:= (T.r i:ℂ); have ht:‖t‖=T.r i:=by rw [show t= (T.r i:ℂ) from rfl,Complex.norm_real,Real.norm_of_nonneg (T.pos i).le];
 have hm:t ∈ ball (0:ℂ) (T.cap+1):= mem_ball_zero_iff.mpr (ht.trans_lt he)
 have hv :Set.MapsTo f (ball (0:ℂ) (T.cap+1)) (closedBall (f 0) A):=fun x hx=>by rw [e]; exact mem_closedBall_zero_iff.mpr ((hc ⟨x,ball_subset_closedBall hx,rfl⟩).trans (le_max_left ..))
 have h := Complex.dist_le_div_mul_dist_of_mapsTo_ball (Differentiable.differentiableOn h) hv hm; rw [e,dist_zero_right,dist_zero_right,ht] at h; change ‖f t‖ ≤ A/_ * T.r i^_; rw [zpow_one]; exact h
private lemma smallP (N:ι→Side): Act (tinc N) 2 fun i _=> (1:ℂ)-cexpR (pinch (N i))+Complex.I*(pinch (N i):ℂ):=by
 let F(z:ℂ):=1-cexpR z+Complex.I*z
 let P:=dslope F 0
 have hu: Differentiable ℂ F:= by unfold F cexpR; fun_prop
 have h:Differentiable ℂ P:= differentiableOn_univ.mp ((Complex.differentiableOn_dslope univ_mem).mpr hu.differentiableOn) -- tune
 have he:P 0=0:=by
    rw [show P 0=deriv F 0 from dslope_same ..]; apply HasDerivAt.deriv
    have ht := (((Complex.hasDerivAt_exp _).comp (0:ℂ) ((hasDerivAt_id' (0:ℂ)).mul_const Complex.I)).const_sub 1).add ((hasDerivAt_id' (0:ℂ)).const_mul Complex.I); simp at ht; exact ht
 have hv:Act (tinc N) 1 fun i _=> (pinch (N i):ℂ):= yen0 N (fun z=>z) (by fun_prop) rfl
 have hx: Act (tinc N) 2 (fun i _=> (pinch (N i):ℂ)*P (pinch (N i):ℂ)):= hv.mul (yen0 N P h he); convert hx using 1; ext1 i; ext1 z; change F _= _; unfold P; let l:ℂ:= (pinch (N i):ℂ); have hl:l≠0:=by change ((pinch (N i)):ℂ)≠0; exact_mod_cast (pinch_pos _).ne'
 rw [dslope_of_ne _ hl,slope_def_module,smul_eq_mul,sub_zero,show F 0=0 by simp [F,cexpR],sub_zero, ← mul_assoc, mul_inv_cancel₀ hl,one_mul]

variable {n:Type*}[Fintype n][DecidableEq n]
def thrust (T:Op n) : Op (coneA n):=1⊗ₖ (Complex.I • T)
def flint (T:Op n) : Op (coneA n):= (Aop*zen (Lattice.step 1)) ⊗ₖ T
structure Tween (T:Op n)(j:ℕ)(M N:Side)(η C:ℝ) where
 oddV : Odd M.val
 evenV : Even N.val
 highV : 4≤N.val
 stem : TestX→Op (coneA n)
 halo : TestX→Op (coneA n)
 quote : SkinH η C stem
 other : SkinH η C halo
 -- single tiny longitudinal Ward. no Taylor in determinant until both state orientations matched.
 witness : (1-cexpR (pinch N)) • stem (spark 1 (pinch N),minH N) = cexpR (pinch N) •
  (thrust T*fuel n j M (minH N)-fuel n j M (minH N+spark 1 (2*(pinch N:ℂ)))*thrust T)
private lemma minted (N:ι→Side) : Move (tinc N) fun i _=> minH (N i):=by
 refine Move.left (fun i=> enter (bark_inside (0:Site (N i)))) one_pos fun i=>?_
 rw [one_mul,pi_norm_le_iff_of_nonneg ((tinc N).pos i|>.le)]; intro k; rw [minimal,Complex.norm_real,Real.norm_of_nonneg (pinch_pos _).le]; exact le_rfl
private lemma smoke (N:ι→Side) : Move (tinc N) fun i _=> spark 1 (pinch (N i)):=by
 let t:=tinc N
 have he i : star (spark 1 ((t.r i:ℝ):ℂ))=spark 1 (t.r i:ℂ):=by simp [spark_star]
 have hg i k : ‖(spark 1 (t.r i:ℂ)) k‖ ≤ t.r i:=by
    unfold spark; by_cases hx:k=(1:Axis) <;> simp [Lattice.step_apply,hx, Real.norm_of_nonneg,t.pos,t.pos i|>.le,abs_of_pos]
 refine Move.left (fun i=>⟨he i,fun k=>(Complex.abs_re_le_norm _).trans ((hg i k).trans (t.hold i))⟩) one_pos fun i=>?_; rw [one_mul]; exact (pi_norm_le_iff_of_nonneg (t.pos i|>.le)).mpr (hg i)
private lemma fairy (N:ι→Side)(e:∀ i,4≤(N i).val):Move (tinc N) fun i _=> minH (N i)+spark 1 (2*(pinch (N i):ℂ)):=by
 let t:=tinc N
 let F i:=minH (N i)+spark 1 (2*(t.r i:ℂ))
 have hp i : star (F i)=F i:=by unfold F minH; rw [star_add,spark_star,riv_phys]; norm_num
 have hx i k: ‖F i k‖≤ 3*t.r i:=by
   have h:=t.pos i
   simp only [F,Pi.add_apply,minimal, spark,Pi.smul_apply,smul_eq_mul,Lattice.step_apply]; change ‖(t.r i:ℂ)+_‖≤_
   split
   · rw [mul_one,show (t.r i:ℂ)+2*(t.r i:ℂ)= ((3*t.r i:ℝ):ℂ) by push_cast; ring,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
   rw [mul_zero,add_zero, Complex.norm_real,Real.norm_of_nonneg h.le]; linarith
 refine Move.left (A:=3) (fun i=>⟨hp i,fun k=>(Complex.abs_re_le_norm _).trans ((hx i k).trans ?_)⟩) (by norm_num) fun i=> (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (t.pos i|>.le))).mpr (hx i)
 have he : (3:ℝ)≤(N i).val := by exact_mod_cast show 3≤(N i).val from (by have:= e i; omega)
 exact (mul_le_mul_of_nonneg_right he (t.pos i|>.le)).trans_eq (payH.symm)
private lemma nonce(T:Op n)(p:Momentum)(z:ℂ) :thrust T* Lent n p-Lent n (p+spark 1 (2*z))*thrust T=(-Complex.I*z) • flint T:=by
 unfold Lent spark flint thrust; rw [op_kron_mul,op_kron_mul,one_mul,mul_one,one_mul,mul_one, zenP,zenS]
 let X:= ((1/2:ℂ) • (Aop*zen p)); let Y:= Aop*zen (Lattice.step 1)
 rw [show (1/2:ℂ) • (Aop*(zen p+ (2*z) • _))=X+z • Y by unfold X Y; rw [mul_add,Matrix.mul_smul]; module]
 unfold X Y; simp only [Matrix.add_kronecker,Matrix.smul_kronecker,Matrix.kronecker_smul]; module
lemma wardBud {T:Op n}{j:ℕ}(hj:1≤j){M N:ι→Side}{η C:ℝ}(h:0<η)(k:0<C)(U:∀ i:ι,Tween T j (M i) (N i) η C) :Act (tinc N) 1 fun i _=> (U i).stem 0-flint T:=by
 let X(i:ι):=minH (N i); let Y(i:ι):= spark 1 (pinch (N i)); let t:=tinc N; let Z(i:ι):= X i+spark 1 (2*(t.r i:ℂ)); let V(i:ι):=(U i).stem (Y i,X i); let P(i:ι):= cexpR (t.r i:ℂ)
 let W(i:ι):=thrust T*fuel n j (M i) (X i)-fuel n j (M i) (Z i)*thrust T
 have ht:= minted N; have hv:= fairy N fun i=>(U i).highV; have hk(i):= (U i).oddV
 have hn := Act.anchor t (thrust T); have hw:Act t 1 fun i _=>W i:= (hn.mul (ht.fossil n M hk j hj)).sub ((hv.fossil n M hk j hj).mul hn)
 let L(i:ι):= -Complex.I*(t.r i:ℂ); have hp:Act t 2 fun i _=> W i-L i • flint T:=by
   have hl:=Act.sub (p:=2) (hn.mul (ht.sap n M hk j hj)) ((hv.sap n M hk j hj).mul hn)
   apply Act.transfer hl; refine ⟨1,one_pos,fun i z _=>?_⟩; change W i-L i • _ = thrust T* (fuel n j (M i) (X i)-Lent n (X i))-(fuel n j (M i) (Z i)-Lent n (Z i))*thrust T; unfold W L; rw [← nonce T (X i)]; change (_ - _) - (_ - Lent n (Z i)*_)=_; rw [mul_sub,sub_mul]; abel
 have hg: Act t 0 (fun i _=> V i):= (smoke N).bend ht (fun i=> (U i).quote) h k
 have he : Act t 2 fun i _=> (L i) • (V i-flint T):=by
    have hy:Act t 1 fun i _=> P i-1:=yen0 N (fun z=>cexpR z-1) (by unfold cexpR; fun_prop) (by simp [cexpR]); have hl:= Act.sub (p:=2) ((hy.smul hw).add hp) ((smallP N).smul hg)
    apply Act.transfer hl; refine ⟨1,one_pos,fun i z _=>?_⟩
    have hx : (1-P i) • V i=P i • W i:= (U i).witness; change L i • _= ((P i-1) • W i+(W i-L i • flint T))-(1-P i+ Complex.I*(t.r i:ℂ)) • V i
    rw [show 1-P i+Complex.I*(t.r i:ℂ)=1-P i-L i by unfold L; ring]; rw [sub_smul _ (L i), hx, sub_smul,one_smul,smul_sub]; abel
 have hh: Act t 1 fun i _=> V i-flint T:=by
   obtain ⟨a,D,ha,hd,H⟩:=he; refine ⟨a,D,ha,hd,fun i z hz=>⟨differentiableAt_const _,?_⟩⟩; have hp:=t.pos i; have hx := (H i z hz).2; dsimp only at hx; rw [norm_smul, show ‖L i‖=t.r i from ?_,_root_.zpow_ofNat] at hx
   swap; · unfold L; rw [norm_mul,norm_neg,Complex.norm_I,Complex.norm_real, Real.norm_of_nonneg hp.le,one_mul]
   rw [_root_.zpow_one]; exact le_of_mul_le_mul_left (show t.r i* _ ≤ t.r i*(D*t.r i) from hx.trans_eq (by ring)) hp
 have hl:= (smoke N).sand ht (fun i=>(U i).quote) h k
 convert hh.sub hl using 1; ext1 i; ext1 z; unfold V X Y; abel -- tune
end YM.CF.Ember
