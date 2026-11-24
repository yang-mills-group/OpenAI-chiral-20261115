import YM.SU5.Reconstruction.Sleet.Swale
/-! # The spatio-temperature bound on spectral support. Costs as PAD increases. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm.Snowball
open Function Set Filter MeasureTheory Measure Complex Metric Topology YM.Paley
open scoped Topology NNReal ENNReal Real
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
variable (μ : Measure X) [IsFiniteMeasure μ]
variable (H P:X→ℝ)(x:Continuous H)(y:Continuous P)(p:∀ i,0≤ H i)

def metre(r b:ℝ):= ∫ i,(Real.exp (-r* H i):ℂ)*Complex.exp (↑(P i*b)*I) ∂μ
lemma reversed(r t:ℝ): metre μ H (fun i=> -P i) r t= metre μ H P r (-t):=by unfold metre; simp [mul_neg]

def troublemeter(r k b:ℝ):= ∫ i, Real.exp (-r* H i) * shrink (P i-b) k ∂μ
include p in
private lemma expo_s {r:ℝ}(v:0≤r)(i:X): Real.exp (-r * H i) ≤1:=by rw [Real.exp_le_one_iff]; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr v) (p i) -- include later
include x y p in
private lemma y_service {r k:ℝ} (v:0≤r) (w:0<k) (b:ℝ) : Integrable (fun i=> Real.exp (-r* H i) * shrink (P i-b) k) μ:= by
 apply (integrable_const (μ:=μ) (1:ℝ)).mono' (Continuous.aestronglyMeasurable (by unfold shrink;fun_prop))
 apply ae_of_all; intro i
 unfold shrink; rw [Real.norm_of_nonneg (by positivity)]; apply mul_le_one₀ (expo_s H p v i) (by positivity); rw [Real.exp_le_one_iff]; exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity) -- -q^2 precedence
include x y p
private lemma gets {r:ℝ}(v:0≤r) (b k:ℝ)(w:0<k):
    (∫ t:ℝ, metre μ H P r t * probe b k t) = ((seed k:ℝ):ℂ) * (troublemeter μ H P r k b:ℝ):=by
 let f(t:ℝ)(i:X):= Complex.exp (↑(P i*t)*I) * probe b k t
 unfold metre
 simp_rw [← integral_mul_const,mul_assoc]
 rw [integral_integral_swap]
 swap
 · have hz: Continuous (uncurry fun (t:ℝ)(i:X)=> (Real.exp (-r*H i):ℂ)*f t i):= by unfold uncurry f probe;fun_prop
   apply ((integrable_exp_neg_mul_sq w).comp_fst (ν:=μ)).mono hz.aestronglyMeasurable
   apply ae_of_all; intro t; obtain ⟨t,i⟩:=t; change ‖_ * f t i‖≤ ‖Real.exp (-k*t^2)‖; unfold f; rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le]; apply le_trans (mul_le_mul_of_nonneg_right (expo_s H p v _) (by positivity)); rw [show ‖Complex.exp ((↑(P i * t):ℂ)*I)‖=(1:ℝ) from by simp [Complex.norm_exp], ← gap_zero (t:=t),probed]; simp
 unfold troublemeter; simp_rw [integral_const_mul,Paley.basis _ b k w, ofReal_mul,←mul_assoc] -- desired
 rw [← integral_complex_ofReal, ← integral_const_mul]; refine integral_congr_ae (ae_of_all _ fun t=>?_); simp only [ofReal_mul]; ring

private lemma speed_service {F:ℂ→ℂ}{C σ r:ℝ}(v:0≤r)(Q:Swale C (σ*r) F)
    (o:∀ b:ℝ,F b=metre μ H P r b)(b k:ℝ)(s:0<k): troublemeter μ H P r k b ≤ C * Real.exp (b*(σ*r)+k*(σ*r)^2):=by
 have ht:= givenBound Q (σ*r) b k Q.pos le_rfl s
 simp_rw [o] at ht; rw [gets μ H P x y p v b k s,norm_mul] at ht
 have hg:0<seed k:=by unfold seed;positivity
 have hZ:0≤ troublemeter μ H P r k b:= integral_nonneg (fun i=> mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
 rw [norm_real,Real.norm_of_nonneg hg.le, norm_real,Real.norm_of_nonneg hZ] at ht
 rw [mul_left_comm C] at ht; exact (mul_le_mul_iff_right₀ hg).1 ht -- check

def Snoops (μ:Measure X) (H P:X→ℝ):Prop:= ∀ σ∈Set.Ioo 0 (1:ℝ),∃ C:ℝ,∃ᶠ r:ℝ in atTop, ∃ F:ℂ→ℂ, Swale C (σ*r) F∧∀ b:ℝ,F b=metre μ H P r b

lemma trailblazer (Q:Snoops μ H P) (w:X)(W:w∈ μ.support): -P w≤ H w:=by
 let b:= P w
 by_contra! h; change H w< -b at h; have hp:0< -b:= (p w).trans_lt h
 obtain ⟨σ,u,v⟩:= exists_between (show H w /(-b)<1 from (div_lt_one hp).mpr h)
 have e:0<σ:=lt_of_le_of_lt (by exact div_nonneg (p _) hp.le) u
 obtain ⟨c,hc,hu⟩:= exists_between ((div_lt_iff₀ hp).1 u)
 obtain ⟨δ,hδ,hv⟩:= exists_between (show 0< (-(b*σ+c))/σ^2 from div_pos (by linarith) (by positivity))
 let S:= {i| H i + (P i-b)^2/(4*δ) < c}; have hx : IsOpen S:= isOpen_lt (by fun_prop) continuous_const; have hy : 0<μ S:= (Measure.mem_support_iff_forall w).1 W S (hx.mem_nhds (by simpa [S,b] using hc)) -- shape implicit S?
 let A:= μ.real S; have hA:0<A:= ENNReal.toReal_pos hy.ne' (measure_ne_top _ _)
 obtain ⟨C,E⟩:= Q σ ⟨e,v⟩
 let a:= b*σ+δ*σ^2+c; have ha: a<0:=by unfold a; linarith [(lt_div_iff₀ (show 0<σ^2 by positivity)).1 hv]
 let K(r:ℝ) := C*Real.exp (a*r); have ht: Tendsto K atTop (𝓝 0):=by simpa [K, comp_def] using (Real.tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg ha).mpr (show Tendsto (fun x:ℝ=> x) atTop atTop from tendsto_id))).const_mul C
 obtain ⟨r,⟨F,f,y'⟩,w,v⟩:= (E.and_eventually ((eventually_gt_atTop (0:ℝ)).and (ht.eventually (gt_mem_nhds hA)))).exists
 -- shadow w avoid
 let k:=δ/r; let ε:= Real.exp (-r*c); let m(i:X):= Real.exp (-r* H i) * shrink (P i-b) k
 have hK:0<k:= div_pos hδ w
 have hm:Integrable m μ:= y_service μ H P x y p w.le hK _
 have h₁: A*ε ≤ troublemeter μ H P r k b:= calc
   _ = ∫ _ in S, ε ∂μ:= by simp [A]
   _ ≤ ∫ t in S,m t ∂μ := setIntegral_mono_on (integrable_const _) hm.integrableOn hx.measurableSet (fun i t=> by unfold m shrink ε; rw [← Real.exp_add,Real.exp_le_exp]; have hg:H i+(P i-b)^2/(4*δ)< c:=t; apply le_trans (show -r*c ≤ -r*(H i+(P i-b)^2/(4*δ)) from mul_le_mul_of_nonpos_left hg.le (neg_nonpos.mpr w.le)) (le_of_eq ?_); unfold k; field_simp;ring)
   _ ≤ _ := setIntegral_le_integral hm (ae_of_all _ fun _ => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
 have h₂ : troublemeter μ H P r k b≤ K r*ε:= le_trans (speed_service μ H P x y p w.le f y' _ k hK) (le_of_eq (by unfold ε K; rw [mul_assoc, ←Real.exp_add]; congr 2; unfold k a; field_simp;ring))
 exact (show K r < A from v).not_ge ((mul_le_mul_iff_left₀ (Real.exp_pos _ : 0<ε)).mp (h₁.trans h₂)) -- tune
end YM.ConePrice.Storm.Snowball
