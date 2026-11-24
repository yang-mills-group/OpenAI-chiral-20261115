import YM.SU5.Circuit.Anthem
set_option autoImplicit false
set_option maxHeartbeats 440000
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit.SpringDay
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior RG Work.F06
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix

-- general resonance: integrate z exp phases along a period to show nonzero, simpler than combin
variable {N:Side}
def speed (x:ℝ):ℂ:=Complex.exp (Complex.I*(x:ℂ))
abbrev debtM (n j:ℕ):ℂ := (bead n (-1) j:ℂ)
def chants (s:Offset N)(T:Site N→ℂ)(z:Cover):ℂ := ∑ i:Site N,charK s i z*T i
def brink (n:ℕ)(T:Site N→ℂ)(x:Axis)(v:ℤ)(k:Site N):ℂ:= T (k+march N x (-v))-∑ i∈ range n,debtM n i *T (k+march N x (i*v))
def auras (n:ℕ)(d:ℝ):ℂ:= speed d-∑ i∈range n,debtM n i*speed (-(i:ℝ)*d)
lemma marchQu (a:Axis)(d:ℤ)(z:Cover)(k:Site N)(s:Offset N):charK s k z= speed (-(extent N d * (z a))) * charK s (k+march N a d) z:=forth ..
lemma adagio (s:Offset N)(n:ℕ)(T:Site N→ℂ)(z:Cover)(a:Axis)(v:ℤ): chants s (brink n T a v) z=auras n (extent N v*z a)* chants s T z:=by
 have he(x:ℤ):(∑ i:Site N,charK s i z*T (i+march N a x))= speed (-(extent N x*z a))*chants s T z:=by
    rw [chants,Finset.mul_sum,←Equiv.sum_comp (Equiv.addRight (march N a x)) (fun i=> speed (-(extent N x*z a))*(charK s i z * T i))]; apply sum_congr rfl; intro i _; rw [show Equiv.addRight (march N a x) i=i+march N a x from rfl]; rw [←mul_assoc, ←marchQu]
 rw [chants]; unfold brink; simp_rw [mul_sub,Finset.mul_sum,sum_sub_distrib]; rw [he]; unfold auras; rw [sub_mul,Finset.sum_mul]
 congr 1
 · rw [show -(extent N (-v)*_)=extent N v*(z a) from (by unfold extent; push_cast; ring)]
 rw [sum_comm]; apply sum_congr rfl; intro i _; simp_rw [mul_left_comm (charK s _ z) (debtM n i),← Finset.mul_sum, he,march_t]; push_cast; ring_nf -- tune
-- analytic resonance using integral one dim
lemma brightChord (n:ℕ): ∃ x:ℝ, auras n x≠0:=by
 by_contra! p
 let J(i:ℕ):ℂ:= -((↑(i+1):ℂ)*Complex.I)
 let f(i:ℕ)(x:ℝ):= debtM n i*Complex.exp (J i *(x:ℂ))
 have hp:(fun x:ℝ=>∑ i∈range n,f i x)=fun _ => (1:ℂ):=funext fun x=>by
    have h:=p x; unfold auras at h; let s:=speed x; apply mul_left_cancel₀ (Complex.exp_ne_zero (Complex.I* (x:ℂ))); -- tune
    change s * _=s*1; simp only [mul_sum]; rw [mul_one]; refine Eq.trans ?_ (sub_eq_zero.mp h).symm; refine sum_congr rfl fun i _=>?_; unfold f s speed J; rw [mul_left_comm, ←Complex.exp_add]; congr 2; push_cast; ring -- tune neg
 let y:=2*Real.pi
 have hh(i:ℕ): (∫ x:ℝ in 0..y,f i x)=0:=by
    unfold f; rw [intervalIntegral.integral_const_mul,integral_exp_mul_complex]; push_cast
    · unfold y; rw [show J i * (↑(2*Real.pi):ℂ)=-((i+1:ℕ)*(2*(Real.pi:ℂ)*Complex.I)) from (by unfold J; push_cast; ring),Complex.exp_neg,Complex.exp_nat_mul_two_pi_mul_I]; simp
    unfold J; exact neg_ne_zero.mpr (mul_ne_zero (by exact_mod_cast i.succ_ne_zero) Complex.I_ne_zero)
 have he := (show (∫ x:ℝ in 0..y,∑ i∈ range n,f i x)=0 by rw [intervalIntegral.integral_finsetSum, sum_eq_zero (fun i _=>hh i)]; exact fun i _=> (show Continuous (f i) by unfold f; fun_prop).intervalIntegrable ..)
 rw [hp,intervalIntegral.integral_const] at he
 exact (smul_ne_zero (by rw [sub_zero]; positivity : (2*Real.pi:ℝ)-0 ≠ 0) one_ne_zero) he

/-- Lattice radial sup norm x. -/
abbrev shaftX (x:Cover):Bin:= fun i=> (x i : ℝ)
abbrev rally (x:Cover) := ‖shaftX x‖
lemma planePeak{z:Cover}(h:z≠0):0<rally z:= norm_pos_iff.mpr (fun a=> h (funext fun i=> (by exact_mod_cast (show (z i:ℝ)=0 from congr_fun a i))))
lemma melody (k:ℕ): ∃ θ w:ℝ,0<θ∧0<w∧∀ (z:Cover),z≠0 → ∃ a:Axis, ∀ (N:ℕ→Side), Tendsto (fun n=>(N n).val) atTop atTop → ∀ᶠ i:ℕ in atTop, ∃ v:ℤ, θ ≤ ‖auras k (extent (N i) v*(z a))‖ ∧ |extent (N i) v| ≤ w/rally z ∧ rally z * pinch (N i)≤1 :=by
 obtain ⟨x,hx⟩:= brightChord k
 let θ:= ‖auras k x‖/2; let w:= |x|+1; have hv:= norm_pos_iff.mpr hx; have ht:0<θ:= half_pos hv
 refine ⟨θ,w,ht,by unfold w; positivity,fun z h=> ?_⟩
 obtain ⟨a,e,f⟩:= exists_max_image univ (fun i=> |(z i:ℝ)|) univ_nonempty
 let R:=rally z; let A:ℝ:= z a
 have he: R=|A|:= le_antisymm ((pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr (fun i=> f i (mem_univ _))) (b_abs (shaftX z) a)
 have hR:0<R:=planePeak h; have hA:A≠0:=abs_pos.mp (he▸hR); let W:= x/A
 refine ⟨a,fun N p=> ?_⟩
 have hp:Tendsto (fun i=>pinch (N i)) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp p) -- tune `val` comp
 choose D F using (fun i:ℕ=> fragment (pinch (N i)) (pinch_pos _) W)
 let G(i:ℕ):= extent (N i) (D i)
 have hz: Tendsto G atTop (𝓝 W) :=by
    rw [tendsto_iff_norm_sub_tendsto_zero]; exact squeeze_zero (fun i=> norm_nonneg _) (fun i=> by rw [norm_sub_rev]; exact F i) hp
 have hh: Tendsto (fun i=> G i*A) atTop (𝓝 x):= (div_mul_cancel₀ x hA) ▸ hz.mul_const A -- tune
 have hP:Tendsto (fun i:ℕ=> ‖auras k (G i*A)‖) atTop (𝓝 ‖auras k x‖):=(((show Continuous (auras k) by unfold auras speed; fun_prop).continuousAt.tendsto).comp hh).norm
 have hs: Tendsto (fun i=> R*pinch (N i)) atTop (𝓝 0):=by simpa using hp.const_mul R
 have hW: |W| < w / rally z:=by
    unfold W w; change _< _/R; rw [he,abs_div]; gcongr; linarith -- tune
 filter_upwards [hz.abs.eventually (gt_mem_nhds hW),hP.eventually (lt_mem_nhds (half_lt_self hv)),hs.eventually (gt_mem_nhds one_pos)] with i a h w; exact ⟨D i,h.le,a.le,w.le⟩ -- var h proof collision

lemma apogee (D H R f u:ℝ)(e:0<D)(p:0<R)(k:0<u)(hn:1 ≤ R*u)(v:0≤H)(g:|f| ≤ H/R)(j:ℕ): D*u^j*(|f|/u)^(j+6) ≤ D*H^(j+6)*2^6/R^j*(1/(1+R*u)^6):=by
 rw [one_div,← div_eq_mul_inv,le_div_iff₀ (by positivity : 0<(1+R*u)^6)]
 refine (mul_le_mul (show D*u^j*(|f|/u)^(j+6)≤D*u^j*(H/R/u)^(j+6) by gcongr) (show (1+R*u)^6≤ (2*R*u)^6 by gcongr; linarith) (by positivity) (by positivity)).trans_eq ?_
 rw [pow_add, pow_add H, div_pow,div_pow]; field_simp -- tune

/-- Symbol budget: when shifting along axis at *proportional-to-|p|* step, need pay general order chord. Record even shifts crossing seam at their true torus momenta. -/
structure Aria (N:Side)(s:Offset N)(T:Site N→ℂ)(m:ℕ)(b C:ℝ):Prop where
 even: Even N.val
 cap(i): ‖T i‖≤ C*‖glen s i‖^m
 fade(a:Axis)(v:ℤ)(i:Site N)(h:|extent N v| < b*‖glen s i‖): ‖brink (m+6) T a v i‖ ≤ C*‖glen s i‖^m * (|extent N v|/‖glen s i‖)^(m+6)
variable {s:Offset N}{T:Site N→ℂ}{m:ℕ}{b C:ℝ}(u:Aria N s T m b C)(hb:0<b)(hc:0<C)
lemma glaze (b C:ℝ)(m:ℕ)(_p:0<b)(f:0<C)(w S:ℝ)(hw:0<w)(hS:0<S) :∃ U:ℝ,0<U ∧∀ {N:Side}{s:Offset N}{T:Site N→ℂ}(R:ℝ)(i:Site N), 0<R→ R*‖glen s i‖≤S→ Aria N s T m b C→∀(v:ℤ)(a:Axis),|extent N v| ≤ w/R→ ‖brink (m+6) T a v i‖ ≤ U/R^m * (1/(1+R*‖glen s i‖)^6):=by
 let k:=m+6
 obtain ⟨x,h,P⟩:=bead_bound k; let V:= C*(S+k*w)^m; let K:=(1+x)*V; have hV:0<V:=by unfold V; positivity; -- tune
 have hK:0<K:=by unfold K; positivity
 refine ⟨K*(1+S)^6,by positivity,fun {N} {s} {T} R i p' y χ v a hv=>?_⟩
 have hz(j:ℤ)(e:|(j:ℝ)|≤(k:ℝ)): ‖T (i+march N a (j*v))‖ ≤ V/R^m:=by
    apply (χ.cap _).trans; have hp: |extent N (j*v)|≤ (k:ℝ)* (w/R):= by rw [march_t,abs_mul]; gcongr
    obtain ⟨he,_⟩:=abs_le.mp (within_d (s:=s) χ.even i a (j*v) _ hp)
    have hh:‖glen s (i+march N a (j*v))‖ ≤ (S+(k:ℝ)*w)/R:=by
       rw [add_div, mul_div_assoc]; have ht:= (le_div_iff₀ p').mpr (show ‖glen s i‖*R≤S from (mul_comm _ _).trans_le y); linarith only [ht,he]
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hh _) f.le).trans_eq ?_; rw [div_pow]; unfold V; ring
 let y':=V/R^m; have hy:0 ≤ y':=by unfold y'; positivity
 calc _≤ y'+x*y':=by
        unfold brink; apply le_trans (norm_sub_le ..); refine add_le_add ?_ ((norm_sum_le ..).trans ((sum_le_sum (g:=fun i=>|bead k (-1) i| *y') ?_).trans ?_))
        · simpa [y'] using hz (-1) (by simp only [Int.cast_neg,Int.cast_one,abs_neg,abs_one]; exact_mod_cast show 1≤ k from (by unfold k; omega))
        · intro i l; rw [norm_mul]; unfold debtM; rw [Complex.norm_real,Real.norm_eq_abs]; refine mul_le_mul_of_nonneg_left (hz i ?_) (abs_nonneg _); simp only [Int.cast_natCast,abs_of_nonneg (by positivity : 0 ≤ (i:ℝ))]; exact_mod_cast (mem_range.mp l).le
        rw [← sum_mul]; gcongr; exact P (-1) (by norm_num)
      _≤_:=by
        rw [one_div,← div_eq_mul_inv,le_div_iff₀ (by positivity :0<(1+R*‖glen s i‖)^6)]; apply le_trans (b:=(y'+x*y')*(1+S)^6) ?_ (le_of_eq ?_)
        · gcongr
        unfold y' K; ring
#print axioms brightChord
def skyPrice(s:Offset N)(T:Site N→ℂ)(z:Cover):ℂ:=((N.val:ℂ)^4)⁻¹ * chants s T z
/-- Standing symbol-to-power price at true stencil offsets. Holder on even-kick. -/
theorem radiant (m:ℕ)(hb:0<b)(hc:0<C) :∃ K:ℝ,0<K ∧ ∀ (z:Cover), z≠0 → ∀ (N:ℕ→Side), Tendsto (fun i=>(N i).val) atTop atTop → ∀ᶠ i:ℕ in atTop, ∀ (s:Offset (N i))(T:Site (N i)→ℂ),Aria (N i) s T m b C→ ‖skyPrice s T z‖ ≤ K/(rally z)^(4+m):=by
 obtain ⟨θ,w,t,hW,F⟩:= melody (m+6)
 let A:= 1+w/b
 have hz:0<A:=by unfold A; positivity
 obtain ⟨V,hV,g⟩:= glaze b C m hb hc w A hW hz
 let u:= C*w^(m+6)*2^6; let Y:= max u V; have hu:0<Y:=lt_max_of_lt_right hV
 obtain ⟨p,h,hp⟩:=sixen
 have hx:=Real.pi_pos
 refine ⟨Y*p/θ/Real.pi^4,by positivity,fun z e N s=>?_⟩
 let R:=rally z; have hR:0<R:=planePeak e
 obtain ⟨a,f⟩:=F z e; filter_upwards [f N s] with i v; obtain ⟨d,e',hv,hf⟩:=v
 let L:=N i; intro σ P U; let ℱ:= brink (m+6) P a d; let t':= extent L d
 have hℱ(k:Site L):‖ℱ k‖ ≤ Y/R^m*(1/(1+R*‖glen σ k‖)^6):=by
    let K:= ‖glen σ k‖; rcases le_or_gt (R*K) A with y|y
    · exact (g _ k hR y U d a hv).trans (by gcongr; exact le_max_right ..)
    have ht:1 < R*K:=lt_trans (by unfold A; linarith [div_pos hW hb] : 1<A) y
    have hk:0<K:=by nlinarith; -- honest
    have hw: |t'|< b*K:= lt_of_le_of_lt hv ((div_lt_iff₀ hR).mpr (by
       have he:w/b<R*K:= by unfold A at y; linarith; -- tune
       have hg:= (div_lt_iff₀ hb).mp he; linarith))
    exact ((U.fade a d k hw).trans (apogee C w R t' K hc hR hk ht.le hW.le hv m)).trans (by unfold Y u; gcongr; exact le_max_left ..)
 have he:θ*‖chants σ P z‖ ≤ Y/R^m * (p/(R*pinch L)^4):=calc
   _≤ ‖chants σ ℱ z‖:=by rw [show chants σ ℱ z=_ from (adagio ..),norm_mul]; gcongr
   _≤ ∑ k:Site L,‖ℱ k‖:=by refine (norm_sum_le ..).trans_eq (sum_congr rfl fun i _=>?_); rw [norm_mul, show ‖charK σ i z‖=1 from mode_real _ _ (tmap_physical _),one_mul]
   _≤_:= by apply (sum_le_sum (s:=univ) (fun i _=>hℱ i)).trans; rw [←Finset.mul_sum]; refine mul_le_mul_of_nonneg_left (hp L σ R hR hf) (by positivity)
 have hv: ‖chants σ P z‖ ≤ (Y/R^m * (p/(R*pinch L)^4))/θ:= (le_div_iff₀ t).mpr (by rwa [mul_comm])
 rw [skyPrice,norm_mul]; apply (mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans_eq; change ‖((L.val:ℂ)^4)⁻¹‖ *_= _/R^_; rw [norm_inv,norm_pow, Complex.norm_natCast]; unfold pinch; have hx:=side_pos L; field_simp; ring
#print axioms radiant
end YM.Regis.Circuit.SpringDay
