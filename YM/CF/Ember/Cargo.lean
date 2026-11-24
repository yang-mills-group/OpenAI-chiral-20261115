import YM.CF.Ember.Shelf
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n: Type*}[Fintype n][DecidableEq n]
private def roam (x:Gaia)(a:Axis)(z:ℝ) : Gaia:= x+(2*z) • springAx a
private lemma tack(a:Axis)(z:ℝ): river (z • springAx a)=spark a z:=by ext1 i; change (↑((z • springAx a) i):ℂ)=_; by_cases h:i=a<;> simp [spark,springAx,h]
private lemma trail(x:Gaia)(a:Axis)(z:ℝ): spoon (river x) (spark a z)=river (roam x a z):=by
 have he(x y:Gaia) : river (x+y)=river x+river y:=by ext1 i; change (( (x+y) i:ℝ):ℂ)=_; simp only [PiLp.add_apply,Complex.ofReal_add]; rfl
 rw [spoon,← spark_plus,roam,he,tack]; push_cast; rfl
variable {ι:Type*}{M N:ι→Side}{T:Op n}{j:ℕ}(y:1≤j){η C:ℝ}(h:0<η)(g:0<C)(U:∀ i:ι,Tween T j (M i) (N i) η C)(k:∀ i,Site (N i))
variable {D:ℝ}(d:0<D)(H:∀ i,‖bark (k i)‖≤ D*pinch (N i))(v:∀ i,(D+2)*pinch (N i)≤1)
include U k h g H v y d
private lemma gaugeX(a:Axis)(s:ι→ℝ)(hs:∀ i, |s i|=pinch (N i)) :Act (tinc N) (-2) fun i _=> (U i).flame (river (bark (k i))) a (s i):=by
 let t:=tinc N; let F i:=bark (k i); let X i:=river (F i); let Q (i:ι):=spark a (s i); let Y(i:ι):=spoon (X i) (Q i); let Z (i:ι):=roam (F i) a (s i)
 have he i: Y i=river (Z i):=trail ..
 have hu i: ‖Z i‖≤(D+2)*t.r i:=by
   unfold Z roam; refine (norm_add_le ..).trans ((add_le_add (H i) ?_).trans_eq (add_mul ..).symm); simp [norm_smul,spring_unit,abs_mul,hs i,t,tinc]
 have hl i: pinch (N i)≤ ‖Z i‖:=by
   let b:Axis:=if a=0 then 1 else 0; have hb:b≠a:=by unfold b; split <;> grind -- tune
   have ht: Z i b=F i b:=by unfold Z roam; simp [hb,springAx]
   unfold F at ht; rw [branch] at ht -- F not
   refine (cohere (k i b)).trans ?_; rw [←ht]; change |exileE (Z i) b|≤_; exact (show |exileE (Z i) b|≤ ‖exileE (Z i)‖ by simpa using norm_le_pi_norm (exileE (Z i)) b).trans (orbit_at _)
 have hv i : Z i∈boundsEarth:= orbs ((hu i).trans (v i)); have hx i: F i∈boundsEarth:= bark_inside _
 have hp : Move t (fun i _=> X i) := Move.left (fun i=> enter (hx i)) d fun i=> (boundH _).trans (H i)
 have hq : Move t (fun i _=> Y i) :=Move.left (fun i=>he i |>.symm ▸ enter (hv i)) (show 0<D+2 by positivity) fun i=> he i |>.symm ▸ (boundH _).trans (hu i)
 have hg(c:ι→ℝ)(hc:∀ i, |c i|=pinch (N i)):Move t fun i _=>spark a (c i):=by
   have hb i : ‖c i • springAx a‖= pinch (N i):=by rw [norm_smul,spring_unit,mul_one,Real.norm_eq_abs,hc]
   simp_rw [← tack]; exact Move.left (fun i=> enter (orbs (by rw [hb]; exact le_trans (by have ht:= d; have hv:=pinch_pos (N i); nlinarith : pinch (N i)≤(D+2)*pinch (N i)) (v _)))) one_pos fun i=>(boundH _).trans_eq (by rw [hb,one_mul]; rfl)
 have hQ:= hg s hs; have hU: Move t (fun i _=> -(Q i)):=by
   convert hg (fun i=> -(s i)) (fun i=>by simpa using hs i) using 1; ext1 i; ext1 z; unfold Q spark; push_cast; rw [neg_smul]
 have hn i:= (U i).oddV
 have hb (p:ι→Momentum)(x:ι→ Gaia)(P:Move t fun i _=>p i)(e:∀ i,p i=river (x i))(w:∀ i,x i∈boundsEarth)(r:∀ i,t.r i ≤ ‖x i‖):Act t (-2) fun i _=> edgeH n j (M i) (p i):=by
    let A:Tax ι:=⟨fun i=>‖x i‖,2*Real.pi,fun i=>(t.pos i).trans_le (r i),fun i=>mem_closedBall_zero_iff.mp (earth_bounded _ (w i))⟩
    have he:=principal_in A x (fun _=>rfl) w
    obtain ⟨C,hc,H⟩:= Move.chill_mag (p:=fun i _=>river (x i)) M hn j y x (fun i=>rfl) (fun i=>(show A.r i=_ from rfl)) w
    apply Act.smul (p:=-2) (q:=0) (s:=fun i _=> (shell j (M i) (p i))⁻¹) ?_ (Act.anchor t (bins n)) -- tune
    apply Act.inv (P.glass M hn j y); refine ⟨C,hc,fun i=>(le_trans ?_ (e i |>.symm ▸ H i))⟩ -- tune
    exact mul_le_mul_of_nonneg_left (zpow_le_zpow_left₀ (by decide) (t.pos i|>.le) (r i)) hc.le
 have hc : Act t 1 fun i _=> (U i).rail (X i) (Q i):=by
    have ht: Act t 0 fun i (_:ℂ)=> star ((U i).stem (-Q i,Y i)):= (hU.bend hq (fun i=>(U i).quote) h g).sun
    apply Act.transfer (Act.add (p:=1) ((hQ.bend hp (fun i=>(U i).quote) h g).mul (hp.fossil n M hn j y).sun) ((hq.fossil n M hn j y).mul ht))
    refine ⟨1,one_pos,fun i z _=>?_⟩; unfold Tween.rail Q X; rw [spark_star,riv_phys,show star ((s i:ℝ):ℂ)=s i from Complex.conj_ofReal _] -- tune
 have hi:= hb X F hp (fun _=>rfl) hx (fun i=>torch _)
 have hk:Act t (-2) fun i _=> (U i).wheels (X i) (Q i):=by
   have ht:= hb Y Z hq he hv hl
   have h': Act t (-2) fun i (_:ℂ)=> edgeH n j (M i) (Y i)*(U i).rail (X i) (Q i)*edgeH n j (M i) (X i)*star ((U i).rail (X i) (Q i)) := ((ht.mul hc).mul hi).mul hc.sun
   apply Act.transfer (coal h'); refine ⟨1,one_pos,fun i z _=>?_⟩; unfold Tween.wheels X Q; rw [spark_star,riv_phys,show star ((s i:ℝ):ℂ)=s i from Complex.conj_ofReal _]
 have hh: Act t (-2) fun i _=> (U i).sear (X i) (Q i):= coal (hi.mul (hQ.bend hp (fun i=>(U i).other) h g)) -- tune
 exact hk.sub hh
lemma campU:∃ B:ℝ,0<B∧ ∀ i,‖(U i).valley (k i)‖ ≤B/pinch (N i)^4:=by
 let t:=tinc N
 let S(i:ι):= (U i).slab (bark (k i)); let T(i:ι):ℂ:= pinch (N i); let F(i:ι):= S i (T i)+S i (-T i)
 have hx:Act t (-2) fun i _=>F i:=by
   have ht(a:Axis):= gaugeX y h g U k d H v a (fun i=>pinch (N i)) (fun i=>abs_of_pos (pinch_pos _)); have hy(a:Axis): Act t (-2) fun i _=> (U i).flame (river (bark (k i))) a (-T i):=by simpa only [t,T, Complex.ofReal_neg] using gaugeX y h g U k d H v a (fun i=> -pinch (N i)) (fun i=> by rw [abs_neg]; exact abs_of_pos (pinch_pos _))
   exact ((ht 0).sub (ht 1)).add ((hy 0).sub (hy 1))
 obtain ⟨a,C,ha,hc,K⟩:= hx; refine ⟨C/64,by positivity,fun i=>?_⟩; let z:=pinch (N i); have hp:t.r i=z:=rfl; have hz:0<z:=pinch_pos _
 change ‖(F i).re/(64*z^2)‖≤C/64/z^4; rw [norm_div,Real.norm_eq_abs,Real.norm_of_nonneg (by positivity : 0≤64*z^2)]; apply (div_le_div_of_nonneg_right ((Complex.abs_re_le_norm (F i)).trans (K i 0 (by simpa)).2) (by positivity : 0≤64*z^2)).trans_eq; rw [hp,_root_.zpow_neg,_root_.zpow_ofNat]; field_simp
end YM.CF.Ember
