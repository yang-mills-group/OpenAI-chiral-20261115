import YM.CF.Onyx.Gold
set_option autoImplicit false
noncomputable section
namespace YM.CF.Onyx
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Ember Jill Flare
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {ι:Type*}{A:Tax ι}{j:ℕ}
lemma eden{z:ℂ}(p:z.re≤0):‖1- Complex.exp z‖≤2*‖z‖:=by
 rw [norm_sub_rev]; rcases le_total ‖z‖ 1 with h|h
 · have hx:= (norm_le_norm_sub_add (Complex.exp z-1) z).trans (add_le_add_left (Complex.norm_exp_sub_one_sub_id_le h) _); nlinarith [norm_nonneg z]
 have he:‖Complex.exp z‖≤1:=by rw [Complex.norm_exp]; simpa using Real.exp_le_exp.mpr p
 exact (norm_sub_le ..).trans (by rw [norm_one]; linarith)
def damp(y:ℝ)(x:ℂ):ℂ:= (y:ℂ)⁻¹ * (1-Complex.exp (-(y:ℂ)*x))
lemma ion(y:ℝ)(hp:0<y)(x:ℂ)(h:0≤x.re): ‖damp y x‖≤2*‖x‖:=by
 unfold damp; rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hp.le]; apply le_trans (mul_le_mul_of_nonneg_left (eden ?_) (inv_nonneg.mpr hp.le)); rw [norm_mul,norm_neg,Complex.norm_real,Real.norm_of_nonneg hp.le]; apply le_of_eq; field_simp
 simp only [Complex.mul_re, Complex.neg_re,Complex.neg_im,Complex.ofReal_im,Complex.ofReal_re]; nlinarith [mul_nonneg hp.le h]
lemma thin (F:ι→ℂ→ℂ)(h:Act A 2 F)(u:∃ c:ℝ,0<c∧∀ i,c*A.r i^2 ≤(F i 0).re)(s:ι→ℝ)(p:∀ i,0<s i):Act A 2 fun i z=>damp (s i) (F i z):=by
 obtain ⟨c,e,H⟩:=u; obtain ⟨a,b,g,j,K⟩:=h.dam; obtain ⟨r,C,w,hc,R⟩:=h
 refine ⟨min r (min a (c/b)),2*C,lt_min w (lt_min g (by positivity)),by positivity,fun i z u=>?_⟩; obtain ⟨u,l⟩:=lt_min_iff.mp u; obtain ⟨t,v⟩:=lt_min_iff.mp l; have hz:= R i z u
 have ht:0≤(F i z).re:=by
   have he: (F i 0).re-(F i z).re≤ b*A.r i^2 *‖z‖:=by rw [← Complex.sub_re]; exact (Complex.re_le_norm _).trans (by rw [norm_sub_rev]; simpa only [zpow_ofNat] using (K i z (mem_ball_zero_iff.mpr t))) -- tune
   have hh: b*A.r i^2 *‖z‖≤ c*A.r i^2:=by rw [mul_right_comm]; exact mul_le_mul_of_nonneg_right (by have hv:= (lt_div_iff₀ j).mp v; linarith) (sq_nonneg _)
   linarith [H i]
 refine ⟨?_,(ion _ (p i) _ ht).trans ((mul_le_mul_of_nonneg_left hz.2 (by norm_num : (0:ℝ)≤2)).trans_eq (by ring))⟩
 unfold damp; apply DifferentiableAt.const_mul; apply differentiableAt_const _ |>.sub; exact (hz.1.const_mul _).cexp -- tune
abbrev WarmRay:=RayH × {r:ℝ//0<r}
def Heat:Tax WarmRay:=⟨fun i=>crop.r i.1, Real.pi,fun i=>i.1.width,fun i=>i.1.cap⟩
variable (j)
def aura(w:WarmRay)(a:Axis)(z:ℂ):=tmap w.1.x + spark a (raf crop w.1 z)
def tail (y:ℝ)(M:Male)(p:Momentum):= damp y (shell j M.val p) • dip j M p
lemma limbo(a:Axis)(H:1≤j):Act Heat 1 fun i z=> tail j i.2.val i.1.M (aura i a z):=by
 let T(i:WarmRay)(z:ℂ):= aura i a z; let K(i:WarmRay):=i.1.M; let X(i:WarmRay):=i.1.x
 have e(i): Heat.r i= ‖X i‖:=rfl; have w(i):Bound Real.pi (X i):= i.1.cap; have hp i:T i 0=tmap (X i):=by simp [T,aura,raf,spark,X]
 obtain ⟨c,h,V⟩:=cane e w K H; exact (thin (A:=Heat) (fun i z=> shell j (K i).val (T i z)) ((turn_s e w K a).glass _ (fun i=>(K i).property) j H) ⟨c,h,fun i=>hp i |>.symm ▸ V i⟩ _ (fun i=>i.2.property)).smul (drill e w K H a) -- tune
lemma soul (H:1≤j):∃ b B:ℝ,0<b∧0<B∧∀ M:Male,∀ p:Bin,Bound Real.pi p→∀ r:ℝ,0<r→ ‖tail j r M (tmap p)‖≤ b*‖p‖∧ ‖dip j M (tmap p)‖≤ B/‖p‖:=by
 obtain ⟨a,b,ha,h,F⟩:=limbo j 0 H; obtain ⟨u,B,g,v,K⟩:=drill (A:=crop) (x:=RayH.x) (fun _=>rfl) RayH.cap RayH.M H 0
 refine ⟨b,B,h,v,fun M p w r t=>?_⟩; by_cases e:p=0
 · subst p; rw [show tmap (0:Bin)=0 from rfl]; simp [tail,dip] -- inspect
 let Q:RayH:=⟨M,p,w,norm_pos_iff.mpr e⟩; have hh:= (F (Q,⟨r,t⟩) 0 (by simpa)).2; simp only [aura,raf,mul_zero,spark,zero_smul,add_zero,zpow_one] at hh
 have he:= (K Q 0 (by simpa)).2; simp only [raf,mul_zero,spark,zero_smul,add_zero,zpow_neg,zpow_one] at he
 rw [div_eq_mul_inv]; exact ⟨hh,he⟩
end YM.CF.Onyx
