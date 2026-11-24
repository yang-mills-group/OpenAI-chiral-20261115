import YM.CF.Ember.Light
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary MeasureTheory
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {n: Type*}[Fintype n][DecidableEq n]
namespace Tween
variable {T:Op n}{η C:ℝ}{j:ℕ}{M N:Side}
def flame (U: Tween T j M N η C)(p:Momentum)(a:Axis)(z:ℂ):= U.wheels p (spark a z)-U.sear p (spark a z)
def slab (U: Tween T j M N η C)(x:Gaia)(z:ℂ):ℂ:= U.flame (river x) 0 z-U.flame (river x) 1 z
def valley (U:Tween T j M N η C)(k:Site N):ℝ:= (slab U (bark k) (pinch N)+slab U (bark k) (- (pinch N:ℂ))).re/(64*(pinch N)^2)
def wax(U:Tween T j M N η C)(p: Momentum)(a:Axis)(z:ℂ):= U.flame p a z-oval T p (spark a z)+U.sear p 0
end Tween
variable {ι:Type*}{M N:ι→Side}{T:Op n}(eT:star T=T){j:ℕ}(y:1≤j){η C:ℝ}(h:0<η)(g:0<C)(U:∀ i:ι,Tween T j (M i) (N i) η C)(k:∀ i,Site (N i))
include k
private def windF :Tax ι:=⟨fun i=>‖bark (k i)‖,2*Real.pi,fun i=>(pinch_pos _).trans_le (torch _),fun i=>mem_closedBall_zero_iff.mp (earth_bounded _ (bark_inside _))⟩
include U h g y eT
lemma pyrite :∃ A E :ℝ,1≤A∧0<E∧∀ i,∀ j':A*pinch (N i)≤‖bark (k i)‖,‖(U i).valley (k i)-latticeFieldEstimates T (bark (k i))‖ ≤ E*((‖bark (k i)‖^3)⁻¹+pinch (N i)/‖bark (k i)‖^5) :=by
 let t:=windF k; let X(i:ι):=bark (k i); have hp(i):=bark_inside (k i); have hk(i):=torch (k i)
 let f(a:Axis)(i:ι)(z:ℂ):=(U i).wax (river (X i)) a (raf t i z)
 have he(a:Axis): Act t (-1) (f a):=by
   have hl:=stormL y h g U (t:=t) hk X hp (fun _=>rfl) a
   have hx:= hl.sub (quake y h g U X hp (e:=fun i=>(show t.r i=_ from rfl)) a)
   apply hx.transfer; refine ⟨1,one_pos,fun i z _=>?_⟩; unfold f Tween.wax Tween.flame; abel
 let v(i:ι)(z:ℂ):= f 0 i z-f 1 i z
 have ho(i:ι):v i 0=0:=by simp [v,f,Tween.wax,Tween.flame,raf]
 obtain ⟨a,D,ha,hD,H⟩:= Act.levy (f:=v) ((he 0).sub (he 1))
 obtain ⟨E,hE,K⟩:= aureole T eT; let A:=max 16 (2/a); refine ⟨A,max E (D/64),le_trans (by norm_num : (1:ℝ)≤16) (le_max_left ..),hE.trans_le (le_max_left ..),fun i w=>?_⟩
 let z:=pinch (N i); have hx:= pinch_pos (N i); have ht:=t.pos i; let x:=X i; let s:= z/t.r i
 change A*z≤t.r i at w; change 0<z at hx
 have hv:0<s:=by unfold s; positivity
 have hs:s ≤1/16:= (div_le_iff₀ ht).2 (by nlinarith [mul_le_mul_of_nonneg_right (show 16≤A from le_max_left ..) hx.le]); have hu : (2/a)*z ≤ t.r i := (mul_le_mul_of_nonneg_right (show 2/a≤A from le_max_right ..) hx.le).trans w
 have hm:s<a:= (div_lt_iff₀ ht).2 (by rw [div_mul_eq_mul_div,div_le_iff₀ ha] at hu; nlinarith)
 have hz:‖(s:ℂ)‖=s:=by rw [Complex.norm_real,Real.norm_of_nonneg hv.le]
 have h':=H i (s:ℂ) (by rw [mem_ball_zero_iff,hz]; exact hm); rw [ho,zero_add,sub_zero,hz] at h'
 have hl := K x z ht hx hs
 let V:= (v i s+v i (- (s:ℂ))).re/(64*z^2); let Q:= ((harris T 0 x z+harris T 0 x (-z))-(harris T 1 x z+harris T 1 x (-z)))/(64*z^2)
 have hf:(U i).valley (k i)=V+Q:=by
   have he : ((raf t i (s:ℂ)))=z:= by unfold raf s; push_cast; field_simp [show (t.r i:ℂ)≠0 by exact_mod_cast ht.ne']
   have hb : raf t i (- (s:ℂ))=-(z:ℂ):=by rw [←he]; unfold raf; ring
   unfold V v f Tween.wax Tween.flame; rw [he,hb]; unfold Tween.valley Q Tween.slab harris Tween.flame; push_cast; unfold x X z; simp only [Complex.add_re,Complex.sub_re]; ring
 have hG : ‖V‖≤D/64*(‖x‖^3)⁻¹:=by
   rw [show ‖V‖=_ from norm_div ..,Real.norm_eq_abs,Real.norm_of_nonneg (by positivity : 0≤64*z^2)]
   apply (div_le_div_of_nonneg_right ((Complex.abs_re_le_norm _).trans h') (by positivity : 0≤64*z^2)).trans_eq
   unfold s; change D*‖x‖^(-1:ℤ)*(z/‖x‖)^2/(64*z^2)= _; change 0<‖x‖ at ht; rw [zpow_neg_one]; field_simp
 rw [hf,add_sub_assoc]; apply le_trans (norm_add_le ..)
 let C':=max E (D/64); change _≤C'*(_+z/‖x‖^5); rw [mul_add]; apply add_le_add (hG.trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))) (hl.trans ?_); rw [← mul_div_assoc]; gcongr; exact le_max_left .. -- tune
end YM.CF.Ember
