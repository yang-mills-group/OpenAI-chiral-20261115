import YM.CF.Ember.Plant
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ember
open Function Filter Metric Matrix
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator
namespace Act
variable {ι E B: Type*} {t:Tax ι}{f g:ι→ℂ→ℂ}{p q:ℤ}
lemma stay (h:Act t p f){D:ℝ}(he:0<D)(hv:∀ i,D*(t.r i)^p ≤ ‖f i 0‖) : ∃ a:ℝ,0<a∧∀ i,∀ z∈ball (0:ℂ) a,(D/2)*(t.r i)^p ≤‖f i z‖:=by
 obtain ⟨a,C,ha,hc,H⟩:= h.dam
 let x:=min a (D/(2*C)); refine ⟨x,lt_min ha (by positivity),fun i z hz=>?_⟩
 have hz':=mem_ball_zero_iff.mp hz
 have ho:= t.pos i
 have hx:=H i z (mem_ball_zero_iff.mpr (hz'.trans_le (min_le_left ..))); have hg := mul_le_mul_of_nonneg_left (le_of_lt (hz'.trans_le (min_le_right ..))) (show 0≤ C*(t.r i)^p by positivity)
 have hp:=norm_sub_norm_le (f i 0) (f i z); rw [norm_sub_rev] at hp
 rw [show C*(t.r i)^p * (D/(2*C))=D/2*(t.r i)^p by field_simp] at hg
 linarith [hv i]
lemma inv (h: Act t p f) (he:∃ D:ℝ,0<D∧ ∀ i,D*(t.r i)^p ≤ ‖f i 0‖):Act t (-p) fun i z=> (f i z)⁻¹:=by
 obtain ⟨D,hd,V⟩:=he; obtain ⟨x,hx,B⟩:= h.stay hd V; obtain ⟨a,C,ha,hc,H⟩:=h
 refine ⟨min x a,(D/2)⁻¹,lt_min hx ha,by positivity,fun i z hz=>?_⟩
 have hp:=B i z (mem_ball_zero_iff.mpr (hz.trans_le (min_le_left ..))); have hr:= t.pos i; have ht:0<D/2*(t.r i)^p:=by positivity
 refine ⟨(H i z (hz.trans_le (min_le_right ..))).1.inv (norm_pos_iff.mp (ht.trans_le hp)),?_⟩
 rw [norm_inv,_root_.zpow_neg]; exact (inv_anti₀ ht hp).trans_eq (by rw [mul_inv])
lemma inv_gap (h: Act t p f)(k: Act t p g)(u:Act t q fun i z=> f i z-g i z)
    {D D':ℝ}(he:0<D)(he':0<D')(hl:∀ i,D*(t.r i)^p≤‖f i 0‖)(hm:∀ i,D'*(t.r i)^p≤‖g i 0‖) :Act t (q-p-p) fun i z => (f i z)⁻¹-(g i z)⁻¹:=by
 have hg := u.neg.mul (h.inv ⟨D,he,hl⟩) |>.mul (k.inv ⟨D',he',hm⟩)
 rw [show q-p-p=q + -p + -p by ring]; apply hg.transfer; obtain ⟨x,hx,B⟩:= h.stay he hl; obtain ⟨a,ha,K⟩:= k.stay he' hm; refine ⟨min a x,lt_min ha hx,fun i z hz=>?_⟩
 have hv:= t.pos i; have hb:=B i z (ball_subset_ball (min_le_right ..) hz); have hh:= K i z (ball_subset_ball (min_le_left ..) hz)
 have h':=norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hb); have k':= norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hh); field_simp; ring

variable [NormedRing B][NormedAlgebra ℂ B][NormedAddCommGroup E][NormedSpace ℂ E]
lemma diffM {f g y w:ι→ℂ→B}{a:ℤ}(h:Act t p y)(k:Act t q g)(hl:Act t (p+a) fun i z=> f i z-y i z)(hm:Act t (q+a) fun i z=> g i z-w i z) :Act t (p+q+a) fun i z=> f i z*g i z-y i z*w i z:=by
 have he:=hl.mul k; rw [show p+a+q=p+q+a by ring] at he; have hx:=h.mul hm; rw [← add_assoc] at hx
 convert he.add hx using 1
 ext1 i; ext1 z; rw [sub_mul,mul_sub]; abel
lemma delta {s g:ι→ℂ→ℂ}{y w:ι→ℂ→E}{a:ℤ}(h:Act t p s)(k:Act t q w)(hl:Act t (p+a) fun i z=> s i z-g i z)(hm:Act t (q+a) fun i z=> y i z-w i z) :Act t (p+q+a) fun i z=> s i z•y i z-g i z•w i z:=by
 have he:=h.smul hm; rw [←add_assoc] at he; have hx:=hl.smul k; rw [show p+a+q=p+q+a by ring] at hx
 convert he.add hx using 1; ext1 i; ext1 z; rw [smul_sub,sub_smul]; abel
lemma lit (h:Act t p (fun i z=>f i z))(G:ℂ):Act t p fun i z=> G*f i z:=by simpa only [zero_add] using (Act.anchor t G).mul h
end Act
end YM.CF.Ember
