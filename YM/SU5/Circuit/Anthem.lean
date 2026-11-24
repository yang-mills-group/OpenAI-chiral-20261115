import YM.SU5.Circuit.Dynamo
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Regis.Circuit
open Function Filter Metric Lattice Laurent Next.Free Bloch Finset CF CF.Lat CF.Jill CF.Ember CF.Flare CF.Onyx CF.Fir
open Precision Exterior Matrix RG Work.F06
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix
-- six estimate adapted from Onyx/Pay
lemma sixen : ∃ C:ℝ,0<C∧∀ (N:Side)(x:Offset N)(R:ℝ),0<R→R*pinch N≤1→∑ k:Site N,1/(1+R*‖glen x k‖)^6 ≤ C/(R*pinch N)^4:=by
 obtain ⟨C,g,H⟩:=moor_q; let F(i:ℕ):ℝ:=1/(1+(i:ℝ))^2
 have ht: Summable F:=by
   have he:=(summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow (p:=2) |>.mpr (by norm_num)); simpa [F,add_comm] using he
 let d:=1+∑' i,F i; have hp(i:ℕ):0≤F i:=by unfold F; positivity
 have hv:0<d:=by unfold d; linarith [show 0≤ ∑' i,F i from tsum_nonneg hp]
 refine ⟨d*C,by positivity,fun N x R hr p=>?_⟩
 let V:=C/(R*pinch N)^4; have hm:=pinch_pos N
 let w(k:Site N):= ⌊R*‖glen x k‖⌋₊; let I:= univ.image w; let A(k:Site N):= 1/(1+R*‖glen x k‖)^6
 have hg i:(∑ k∈ univ.filter (fun k=>w k=i),A k) ≤ F i * V:=by
   let M:=univ.filter (fun k=>w k=i); let y:ℝ:=1+(i:ℝ); have hY:0<y:=by unfold y; positivity
   have he := H N M x (y/R) (by rw [le_div_iff₀ hr]; unfold y; have ht:0≤(i:ℝ):=Nat.cast_nonneg _; linarith) (fun k hk=> by
     have he:w k=i:=(mem_filter.mp hk).2; rw [le_div_iff₀ hr]; unfold y; rw [←he,add_comm,mul_comm]; exact (Nat.lt_floor_add_one _).le)
   have hh: ∑ k∈M,A k ≤ ∑ k∈M,1/y^6:=by
      refine sum_le_sum fun k hk=>?_ ; -- tune
      have hh:w k=i:= (mem_filter.mp hk).2; unfold A; unfold y; rw [←hh]; gcongr; exact Nat.floor_le (by positivity)
   refine hh.trans ((show ∑ k∈M,1/y^6 = (#M:ℝ) *(1/y^6) by simp).trans_le ?_); exact (mul_le_mul_of_nonneg_right he (by positivity)).trans_eq (by unfold y V F; rw [add_comm 1 (i:ℝ)]; have hz: 0<(i:ℝ)+1:=(by positivity); field_simp)
 have he:Set.MapsTo w (↑(univ:Finset (Site N))) I:=fun i _=>mem_image_of_mem w (mem_univ _)
 change (∑ k,A k) ≤ _; rw [← sum_fiberwise_of_maps_to he] -- tune
 exact (sum_le_sum (g:=fun i=>F i * V) (fun i _=>hg i)).trans (by rw [← sum_mul]; refine (mul_le_mul_of_nonneg_right ((ht.sum_le_tsum I fun i _=> hp i).trans (by unfold d; linarith : _≤d)) (show 0≤V by unfold V; positivity)).trans_eq ?_; unfold V; ring)
variable {N: Side}{M: Bed}{q:Clip}{σ η C:ℝ}
def fadeOf (T: Site N→ℂ)(a:Axis)(d:ℤ)(k:Site N):= T (k+march N a (-d))-∑ i∈range 8,debt i * T (k+march N a (i*d))
def songOf (T:Site N→ℂ)(z:Cover):ℂ:=∑ k:Site N,charK (rubyOff N) k z*T k
lemma fade_song (T:Site N→ℂ)(z:Cover)(a:Axis)(d:ℤ): songOf (fadeOf T a d) z=drum (extent N d*z a)* songOf T z:=by
 -- reuse opacity via casting Peb matrices and entry evaluation. arbitrary.
 let F(k):Peb:= T k • 1
 let U(v:Peb):=v (0:CF.SpinIdx) 0
 have he : ∀ k:Site N, odds F a d k= (fadeOf T a d k) • (1:Peb):=by intro k; simp only [odds, F, fadeOf,sub_smul, Finset.sum_smul,smul_smul]
 have hv: ∀ D: Site N→ℂ,liv (fun i=>D i •1) (rubyOff N) z= songOf D z • (1:Peb):=by intro I; simp only [liv,songOf,Finset.sum_smul,smul_smul]
 have hz:= setK F a (rubyOff N) d z
 rw [show odds F a d= _ from funext he,hv, show liv F _ _=_ from hv T, smul_smul] at hz
 exact (by simpa [U] using congrArg U hz) -- tune syntax hz ?
lemma travelFree (M: Bed) (v:ℝ) {x y: Bin}(h:peers x y): cusp M v (tmap x)=cusp M v (tmap y):=by
 obtain ⟨w,rfl⟩:=h; rw [map_stem]; unfold cusp Cov cliffMap signal mirage
 simp only [signal, tripQ_stays,Row.periods]; rw [show divisor 1 (_+reciprocal w)=_ from chipSq_stable _ w]; simp only [neg_add,←reciprocal_negate,tripQ_stays]
private lemma localKey (t:Topaz q σ η C)(a:Axis)(x:ℝ)(u:ℝ): t.hop a ((x:ℂ)*(u:ℂ))=tmap (t.path+beam a (x*(‖t.path‖*u))):=by
 funext i; by_cases h:i=a <;> simp [Topaz.hop,rubyM,spark,tmap,beam,Lattice.step,raf,h] <;> first | rfl | ring
lemma apex_zero(M:Bed):Cov M 0=0:=by simp [Cov,signal,tripQ,chip,wedge]
lemma routine {n:Side}{k:Site n}(e: ruby k=0):rubyM k=0:= by unfold rubyM; rw [e]; rfl
lemma pinnacle (h:0<σ)(v:0<C)(Q:Clip)(η:ℝ) (a b:TypeFace 2):∃ w:ℝ,0<w ∧ ∀ {N:Side}{M:Bed},Floor M Q N η C → M.covered σ C→Even N.val → ∀ i:Site N,∀ u:ℝ,0<u→ ‖cusp M u (rubyM i) a b‖ ≤ w * ‖ruby i‖^2:=by
 obtain ⟨r,w,hr,hW,W⟩:= pivotal (Q:=Q) (η:=η) h v 0 a b; refine ⟨w,hW,fun {N} {M} L p x i u e=> ?_⟩; by_cases a':ruby i=0; · rw [cusp, routine a',apex_zero]; simp [a']
 let t:Topaz Q σ η C:=⟨N,M,L,p,x,i,norm_pos_iff.mpr a',u,e⟩; let X:=‖ruby i‖; have ht:= (W t 0 (by simpa)).2; simp only [Topaz.hop,raf,mul_zero,spark,zero_smul,add_zero,zpow_ofNat] at ht; exact ht
-- symbol shift with width exactly d
private lemma costU (D R H f v:ℝ)(e:0<D)(p:0<R)(k:0<v)(hn:1≤R*v)(u:0≤H)(g:|f| ≤ H/R): D*v^2*(|f|/v)^8 ≤ D*H^8*2^6/R^2*(1/(1+R*v)^6):=by
 rw [one_div,←div_eq_mul_inv,le_div_iff₀ (by positivity : 0<(1+R*v)^6)]; refine (mul_le_mul (show D*v^2*(|f|/v)^8≤D*v^2*(H/R/v)^8 by gcongr) (show (1+R*v)^6≤ (2*R*v)^6 by gcongr; linarith) (by positivity) (by positivity)).trans_eq ?_; field_simp
abbrev rear (M:Bed)(a b:TypeFace 2)(u:ℝ)(i:Site N):=cusp M u (rubyM i) a b
lemma pivotNear (Q:Clip) (η S T :ℝ) (u:0<σ)(v:0<C)(t:0<T)(g:0<S)(a b:TypeFace 2)(w:Axis):∃ c:ℝ,0<c ∧ ∀ {N:Side}{M:Bed} (i:Site N), Floor M Q N η C → M.covered σ C→Even N.val →∀ (R:ℝ),0<R→ R*‖ruby i‖≤ S→∀ (d:ℤ)(x:ℝ),|extent N d| ≤ T/R→0<x→ ‖fadeOf (rear M a b x) w d i‖ ≤ (c/R^2)*(1/(1+R*‖ruby i‖)^6):=by
 obtain ⟨c,l,H⟩:=pinnacle u v Q η a b; obtain ⟨A,wA,uA⟩:=debt_bound
 let Z:= c*(S+8*T)^2; let P:=(1+A)*Z; have hZ:0<Z:=by unfold Z; positivity
 have hP:0<P:=by unfold P; positivity
 refine ⟨P*(1+S)^6,by positivity,fun {N} {M} i L p j R s y d x ht hx=>?_⟩
 have hz(z:ℤ)(e:|(z:ℝ)|≤8): ‖rear M a b x (i+march N w (z*d))‖ ≤ Z/R^2:=by
   apply (H L p j _ _ hx).trans; let k:=i+march N w (z*d); let m:=‖ruby i‖; have hm:m≤ S/R:=by rw [le_div_iff₀ s]; linarith
   obtain ⟨hR,_⟩:=abs_le.mp (within_d (s:=rubyOff N) j i w (z*d) _ (rod_j z e _ _ ht)); change _≤ m-‖ruby k‖ at hR; have hu:‖ruby k‖≤ (S+8*T)/R:=by rw [add_div,mul_div_assoc]; linarith only [hm,hR]
   refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hu _) l.le).trans_eq ?_; unfold Z; ring
 let f:= Z/R^2; have hg:0 ≤ f:=by unfold f; positivity
 calc _≤ f+A*f:=by
        unfold fadeOf; apply le_trans (norm_sub_le ..); refine add_le_add ?_ ((norm_sum_le ..).trans ((sum_le_sum (g:=fun i=>‖debt i‖*f) ?_).trans ?_))
        · simpa [f] using hz (-1) (by norm_num)
        · intro i p; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hz i (below8 p)) (norm_nonneg _)
        rw [← sum_mul]; gcongr
      _≤_:=by
        rw [one_div,← div_eq_mul_inv,le_div_iff₀ (by positivity :0<(1+R*‖ruby i‖)^6)]; apply le_trans (b:=(f+A*f)*(1+S)^6) ?_ (le_of_eq ?_)
        · gcongr
        unfold f P; ring
lemma pivotSky (Q:Clip)(η T :ℝ)(u:0<σ)(v:0<C)(t:0<T)(a b:TypeFace 2)(w:Axis):∃ c W:ℝ,0<c ∧ 0<W ∧ ∀ {N:Side}{M:Bed} (i:Site N), Floor M Q N η C → M.covered σ C→Even N.val →∀ (R:ℝ),0<R→ W ≤ R*‖ruby i‖→∀ (d:ℤ)(x:ℝ), |extent N d| ≤ T/R→0<x→ ‖fadeOf (rear M a b x) w d i‖ ≤ (c/R^2)*(1/(1+R*‖ruby i‖)^6):=by
 obtain ⟨F,c,h,e,H⟩:=Jill.plunge (pivotal (Q:=Q) (η:=η) u v w a b) 8 (by decide)
 let W:= 1+T/F; refine ⟨c*T^8*2^6,W,by positivity,by unfold W; positivity,fun {N} {M} i L p j R s hm d x ht hx=>?_⟩
 let A:=‖ruby i‖; let f:=extent N d; let y:=f/A
 have h':0<T/F:=by positivity
 have he:1≤ R*A:=by change 1+_≤ R*A at hm; linarith; -- tune
 have ha:0<A:=by nlinarith
 have hp:‖(y:ℂ)‖= |f|/A:=by simp [y,abs_of_pos ha]; --
 let i':Topaz Q σ η C:= ⟨N,M,L,p,j,i,ha,x,hx⟩; let Y(z):= cusp M x (i'.hop w z) a b
 have hy: ‖(y:ℂ)‖<F:=by
   rw [hp,div_lt_iff₀ ha]; refine lt_of_le_of_lt ht ((div_lt_iff₀ s).mpr ?_); have he:T/F<R*A:=by unfold W at hm; linarith
   rw [div_lt_iff₀ h] at he; linarith
 have hz:= H i' (-1) (by norm_num) (y:ℂ) hy; rw [zpow_ofNat, hp] at hz
 have hg(k:ℤ): Y ((k:ℂ)*(y:ℂ))=rear M a b x (i+march N w (k*d)):=by
   unfold Y; rw [←Complex.ofReal_intCast, localKey]; let X:=i+march N w (k*d)
   have he: (k:ℝ)*(A*y)=extent N (k*d):=by rw [march_t]; unfold y; change (k:ℝ)*(A*(f/A))=(k:ℝ)*f; field_simp
   change cusp M x (tmap (ruby i+beam w ((k:ℝ)*(A*y)))) a b= cusp M x _ a b; rw [he, travelFree M x (march_a (k*d) (rubyOff N) i w)]; rfl
 change ‖Y (_*(y:ℂ)) - ∑ k∈ range 8,debt k*Y ((k:ℂ)*(y:ℂ))‖≤ c*A^2*(|f|/A)^8 at hz
 rw [show (↑(-1:ℝ):ℂ)=((-1:ℤ):ℂ) by norm_num, hg (-1),neg_one_mul,sum_congr (g:=fun k=> debt k * rear M a b x (i+march N w (k*d))) rfl (fun k _=>by rw [← Int.cast_natCast (R:=ℂ) k,hg k])] at hz
 exact hz.trans (costU c R T f A e s ha he t.le ht)
end YM.Regis.Circuit
#print axioms YM.Regis.Circuit.pivotNear
#print axioms YM.Regis.Circuit.pivotSky
