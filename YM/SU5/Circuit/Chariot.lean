import YM.SU5.Circuit.Anthem
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior Matrix RG Work.F06 MeasureTheory
open YM.Stationary (Gaia cartWeight) -- parser
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix
variable {N:Side}{M: Bed}{q:Clip}{σ η C w R:ℝ}
-- adaptation, weight two instead of one
lemma ameno (Q:Clip) (η:ℝ)(a b:TypeFace 2)(u:0<σ)(v:0<C)(t:0<w)(s:Axis):∃ P:ℝ,0 < P ∧∀ {N:Side}{M:Bed}, Floor M Q N η C→ M.covered σ C→ Even N.val →∀ R:ℝ,0<R→ R*pinch N≤1→∀ d:ℤ,|extent N d| ≤ w/R→∀ z:Cover, 1≤ ‖drum (extent N d*z s)‖→ ∀ H:ℝ,0<H→ ‖songOf (rear M a b H (N:=N)) z‖≤ P/R^2*(R*pinch N)^(-4:ℤ):=by
 obtain ⟨c,S,h,hS,F⟩:=pivotSky Q η w u v t a b s; obtain ⟨z,wz,G⟩:=pivotNear Q η S w u v t hS a b s; obtain ⟨u',h',Z⟩:=sixen -- tune Unicode
 let B:=max z c; have he:0<B:=lt_max_of_lt_right h; refine ⟨B*u',by positivity,fun {N} {M} φ p k R r hp d ht x hm H e=>?_⟩
 let A:=rear M a b H (N:=N); let T:=fadeOf A s d; apply le_trans (le_mul_of_one_le_left (b:=‖songOf A x‖) (norm_nonneg _) hm); rw [←norm_mul,←fade_song]; apply (norm_sum_le (s:=univ) (f:=fun i=> charK (rubyOff N) i x*T i)).trans; refine (sum_le_sum (g:=fun i=>B/R^2*(1/(1+R*‖ruby i‖)^6)) ?_).trans ?_
 · intro i _; have hx: ‖charK (rubyOff N) i x‖=1:=mode_real (rubyM i) _ (ruby_pigment i); rw [norm_mul,hx,one_mul]; rcases le_total S (R*‖ruby i‖) with l|l
   · exact (F i φ p k _ r l _ H ht e).trans (by gcongr; exact le_max_right ..)
   exact (G i φ p k _ r l _ H ht e).trans (by gcongr; exact le_max_left ..)
 rw [← Finset.mul_sum]; exact (mul_le_mul_of_nonneg_left (Z N (rubyOff N) R r hp) (by positivity : 0≤ B/R^2)).trans_eq (by simp only [_root_.zpow_neg,zpow_ofNat]; ring)
def magnify (M:Bed)(R:ℝ)(a b:TypeFace 2)(z:Cover)(n:Side):ℂ:=((R:ℂ)^4) * rimble n M (wrap n z,a) (0,b)
def mist (M:Bed)(R D:ℝ)(a b:TypeFace 2)(i:Site N):ℂ:=Complex.exp (- (soft R D:ℂ)*divisor 1 (rubyM i))*Cov M (rubyM i) a b
abbrev chant (M:Bed)(R D:ℝ)(a b:TypeFace 2)(z:Cover)(n:Side):ℂ:= ((R:ℂ)^4)*(stageVolume n)⁻¹ * songOf (mist M R D a b (N:=n)) z
lemma joyful (r:0<R)(x:Cover)(D:ℝ)(p:0<D)(M:Bed)(a b:TypeFace 2)(N:Side): magnify M R a b x N-chant M R D a b x N= ((R:ℂ)^4)*(stageVolume N)⁻¹ * (soft R D :ℂ)* songOf (rear M a b (soft R D) (N:=N)) x:=by
 let y:=soft R D; have hv:0<y:= by unfold y soft; positivity
 let t:ℂ:= y; have hh:t≠0:=by unfold t; exact_mod_cast hv.ne'
 unfold magnify chant; rw [rimflare N M (wrap N x) 0 x (by rw [sub_zero]),←mul_assoc,←mul_sub_left_distrib,mul_assoc _ (soft R D :ℂ)]; congr 1; rw [songOf,songOf,Finset.mul_sum,←sum_sub_distrib]; refine sum_congr rfl fun i _=>?_ ; rw [rear,cusp,damp, Matrix.smul_apply, smul_eq_mul,mist, mul_left_comm (soft R D:ℂ) (charK (rubyOff N) i x), ←mul_sub]; congr 1
 change _= t * (t⁻¹ *_ *_); field_simp -- tune
lemma unpublished (S:ℕ→Side)(R:ℕ→ℝ)(z:ℕ→Cover)(h:Yard S R) {X:Gaia}(t:Tendsto (fun i=>riseX (R i) (z i)) atTop (𝓝 X))(p:X ≠ 0)(u:0<σ)(v:0<C)(η:ℝ)(Q:Clip)(a b:TypeFace 2): ∃ P:ℝ,0<P∧ ∀ᶠ i in atTop,∀ d:ℝ,0<d→∀ M:Bed,M.covered σ C→ Floor M Q (S i) η C→ ‖magnify M (R i) a b (z i) (S i)- chant M (R i) d a b (z i) (S i)‖ ≤ P/d^2:=by
 obtain ⟨s,Y,T,hT,F⟩:=h.loom X z t p; obtain ⟨G,hg,H⟩:=ameno Q η a b u v (zero_lt_one.trans_le hT) s; have hP:=Real.pi_pos; refine ⟨G/Real.pi^4,by positivity,?_⟩; filter_upwards [F] with i e; intro d hd M L V; have ht:= h.pos i; let y:= soft (R i) d; have hy:0<y:=by unfold y soft; positivity; -- tune
 have hk:= H V L (h.even _) _ ht e.2.2.2 _ e.1 _ e.2.1 y hy
 rw [joyful ht _ _ hd]; apply le_trans (norm_mul_le ..); refine (mul_le_mul_of_nonneg_left hk (norm_nonneg _)).trans_eq ?_; unfold stageVolume soft pinch; simp only [norm_mul,norm_pow,norm_inv, Complex.norm_real,Complex.norm_natCast,_root_.zpow_neg,zpow_ofNat]; have hx:= side_pos (S i); rw [Real.norm_of_nonneg (by positivity : 0≤R i), show ‖R i / d‖= R i/d from Real.norm_of_nonneg (by positivity)]; field_simp
end YM.Regis.Circuit
#print axioms YM.Regis.Circuit.unpublished
