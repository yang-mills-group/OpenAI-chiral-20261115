import YM.CF.Vault.Scow
set_option autoImplicit false
noncomputable section
namespace YM.CF.Vault
open Function Filter Matrix NormedSpace Finset Fock Lat Lattice Rush Cube Next.Free Laurent Fir Bloch SU Drapes Peaks Dial Tulip Scroll Branch
open scoped Matrix.Norms.L2Operator Matrix Topology MatrixOrder BigOperators Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 8000
section
variable {n:Type*}[LinearOrder n][Fintype n][Nonempty n]
lemma beard_c {E:Type*}[TopologicalSpace E](P Q W:E→Op n)(C D:Op n)(p:Continuous P)(q:Continuous Q)(u:Continuous W)(k:ℕ)(h:∀i, Stay (Q i) (train (P i) (Q i) (W i) C D) k): Continuous (fun i=>beard (P i) (Q i) (W i) C D k):=by
 unfold beard rockZ; apply continuous_finsetSum; intro i t
 let X(y:ℝ)(e:E):= train (P e) (Q e) (W e) C D y; have he(y:ℝ):Continuous (X y):=by unfold X train straightC victory body throat; fun_prop
 let f:=berth k i; let V:= berth k (i+1)
 refine continuous_iff_continuousAt.mpr (fun y=> ?_); have hs:f≤V:=ber_m k i.le_succ
 let H:= h y i (mem_range.mp t);
 exact (spark_contAt (H f ⟨le_rfl,hs⟩).2.1 (H V ⟨hs,le_rfl⟩).2.2).comp (f:=fun y:E=>(Q y, X f y,X V y)) (q.prodMk ((he f).prodMk (he V))).continuousAt
end
variable {N P L:Side}{ho:Odd L.val}{j n l:ℕ}
def fineT(j:ℕ)(L:Side)(ho:Odd L.val)(b:Bool)(n l:ℕ)(G:Ratio N P)(x:Sew N P)(i:Duel):ℂ:= let y:=post x; beard (chalk j b i G y) (umber j L ho b i G y) (fade j b i G y) (dotB true G x) (dotB false G x) n
abbrev priceT(j:ℕ)(b:Bool)(l:ℕ)(G:Ratio N P)(x:Sew N P)(i:Duel) :ℂ:=beard (lobe G b) (lobe G b) (fade j b i G (post x)) (dotB true G x) (dotB false G x) l
variable (h:Tollage j L ho n l) (G:Ratio N P)(heg:G.count=L)(x:Sew N P)(u:Tollday j L ho n l x G)
include u
lemma degree_v (M:Male)(b:Bool):Continuous (fun t:TickZ=>fade j b (M,t) G (post x)):=by
 let A(t:TickZ):=dustX j (M,t) G (post x); have hv:Continuous A:=by unfold A dustX twinX; fun_prop
 have he : Continuous (fun i:TickZ=>(A i)⁻¹):= continuous_iff_continuousAt.mpr (fun t=> ContinuousAt.comp (InvC_cont (show IsUnit (A t) from (u _).2.2.1)) hv.continuousAt) -- tune
 simp_rw [duskF]; change Continuous (fun i=>fort _ (A i)); unfold fort; fun_prop
lemma price_c (b:Bool)(i:Male): Continuous (fun t:TickZ=>priceT j b l G x (i,t)):= beard_c _ _ _ _ _ continuous_const continuous_const (degree_v G x u i b) _ (fun y=> ( (u (i,y)).2.2.2 b).2.2)
lemma fine_c (b:Bool)(i:Male): Continuous (fun t:TickZ=>fineT j L ho b n l G x (i,t)):=by
 have hx(v):Safe (scrap true (coast j) (i,v) G (post x)):= (u _).1; have he(v):Safe (scrap false (urban j L ho) (i,v) G (post x)):= (u _).2.1
 have hy:Continuous (fun t:TickZ=>chalk j b (i,t) G (post x)):= by cases b; exact continuous_const.sub (pad_cont true G i x hx); exact pad_cont true G i x hx
 have ht:Continuous (fun t:TickZ=>umber j L ho b (i,t) G (post x)):= by cases b; exact continuous_const.sub (pad_cont false G i x he); exact pad_cont false G i x he
 exact beard_c _ _ _ _ _ hy ht (degree_v G x u i b) _ fun v=> ((u (i,v)).2.2.2 b).2.1
lemma price_z (b:Bool)(i:Male):priceT j b l G x (i,oneL)=star (priceT j b l G x (i,oneL)):=by
 let z:=(i,oneL); let C:=dotB true G x; let D:=dotB false G x
 have e:= ((u z).2.2.2 b).2.2; have hc(C:Bool) : sings true (dotB C G x) (lobe G b)= lobe G b:= (jetKee (dotB C G x) _).1 (debit G C b x)
 exact shade_k _ C D _ _ _ e (hc _) (hc _) (revertX G j x i b (u _).2.2.1) (spinBack D (skew_square G false x)) (spinBack C (skew_square G true x))
lemma fine_z (b:Bool)(i:Male): fineT j L ho b n l G x (i,oneL)=star (fineT j L ho b n l G x (i,oneL)):=by
 let z:=(i,oneL); let C:=dotB true G x; let D:=dotB false G x; have e:= ((u z).2.2.2 b).2.1
 have hc : sings true C (chalk j b z G (post x))=chalk j b z G (post x):=by
    have he:= pad_end true G i x (u z).1; cases b; swap; exact he
    let X:= paddle true (coast j) z G (post x); change sings true C (1-X)=1-X; rw [singT,win_l,win_i,map_sub,map_one,←singT]; rw [show sings true C X=X from he] -- tune firmF
 have ht : sings true D (umber j L ho b z G (post x))= umber j L ho b z G (post x):=by
    have he:= pad_end false G i x (u z).2.1; cases b; swap; exact he
    let X:=paddle false (urban j L ho) z G (post x); change sings true D (1-X)=1-X; rw [singT,win_l,win_i,map_sub,map_one,←singT]; rw [show sings true D X=X from he]
 exact shade_k _ C D _ _ _ e hc ht (revertX G j x i b (u _).2.2.1) (spinBack D (skew_square G false x)) (spinBack C (skew_square G true x))
include h heg
lemma toll_z (i:Duel): priceT j false l G x i=priceT j true l G x i:=by
 let X:=dotB true G x; let Y:=dotB false G x
 obtain ⟨a,l,K,T⟩:=u i; have he:=glide_k _ _ _ _ _ _ false (tooth G) (show Stay (lobe G true) (train (lobe G true) (lobe G true) (fade j true i G (post x)) X Y) _ from (T true).2.2)
 simp only [singT,windX,Bool.false_eq_true,ite_false, cSignX, bolt_one, show twist (tooth G) (fade j true i G (post x))=fade j false i G (post x) from (motionX G j i x (heg.symm ▸ ho) true K).2.2, show congrC (tooth G) X.val=X.val from bolt_spin G x true, show congrC (tooth G) Y.val=Y.val from bolt_spin G x false] at he; exact he
lemma pairedLog (M:Male): let i:=(M,noneL); fineT j L ho false n l G x i-priceT j false l G x i= star (fineT j L ho true n l G x i-priceT j true l G x i):=by
 let A(i:Duel):=fineT j L ho false n l G x i; let B(i:Duel):=fineT j L ho true n l G x i; let K:=priceT j true l G x
 let V(t:TickZ):=(2:ℂ)*(A (M,t)-K (M,t)); let W(t:TickZ):=(2:ℂ)*star (B (M,t)-K (M,t))
 have he:Continuous V:=continuous_const.mul ((fine_c G x u false M).sub (price_c G x u true M))
 have ht:Continuous W:=continuous_const.mul (((fine_c G x u true M).sub (price_c G x u true M)).star)
 have hr (t:TickZ):Complex.exp (V t)=Complex.exp (W t):=by
    let i:=(M,t); let C:=dotB true G x; let D:=dotB false G x; obtain ⟨U,T,X,q⟩:= u i; obtain ⟨⟨A,R⟩,B,Y⟩:= q false; obtain ⟨⟨C',P⟩,E,F⟩:= q true
    let Gv:= motionX G j i x (heg.symm ▸ ho) true X; have hg:lobe G false=1-lobe G true:= circ G true
    rw [hg] at R; change Stay (lobe G false) (train (lobe G false) (lobe G false) (fade j false i G (post x)) C.val D.val) l at Y
    rw [hg] at Y
    exact pillow_k C D (skew_square G true x) (skew_square G false x) (det_bill G x) C' A E B P R F Y h.p h.lpos (tooth G) ((bolt_one G true).trans hg) (bolt_spin G x true) (bolt_spin G x false) Gv.2.2
 have hp: V oneL=W oneL:=by
    let i:=(M,oneL); have hA:star (A i)=A i:= (fine_z G x u false M).symm; have hB: star (B i)=B i:= (fine_z G x u true M).symm; have hK: star (K i)=K i:= (price_z G x u true M).symm
    apply Complex.ext
    · have he:=congr_arg norm (hr oneL); rwa [Complex.norm_exp,Complex.norm_exp,Real.exp_eq_exp] at he
    have hx:star (V oneL)=V oneL:=by change star (2* (A i-K i))=_; rw [star_mul,star_sub,hA,hK, show star (2:ℂ)=2 by norm_num,mul_comm]
    have hs:star (W oneL)=W oneL:=by change star (2 * star (B i-K i))=2 * star (B i-K i); rw [star_mul,star_star,star_sub,hB,hK,show star (2:ℂ)=2 by norm_num,mul_comm]
    exact (Complex.conj_eq_iff_im.mp hx).trans (Complex.conj_eq_iff_im.mp hs).symm
 intro i
 have hv:= Phase.carry_log isPreconnected_univ he.continuousOn ht.continuousOn oneL (Set.mem_univ _) (fun i _=> hr i) hp noneL (Set.mem_univ _)
 unfold V W at hv; unfold i; rw [toll_z h G heg x u]; exact mul_left_cancel₀ two_ne_zero hv
end YM.CF.Vault
