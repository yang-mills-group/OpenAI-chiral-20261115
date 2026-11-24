import GaugeFieldConstruction.Echin
set_option autoImplicit false
set_option maxHeartbeats 120000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One
open Lattice CF.XGarden.MastTin.ArtCart.Violets CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators Classical
open HopeC
-- Uniform selector summary.Across ALL paths.
variable (H G:HopeC E4) (X:E4)
abbrev NX (d:E4):=closedBall d (‖d‖/2)
lemma NXp (h:X≠0): 0∉ NX X:= by
 simp only [NX,mem_closedBall,dist_zero_left]; have v:=norm_pos_iff.mpr h; linarith
variable (d:ℕ→E4)(t:ℕ→ℝ)(w:Tendsto t atTop (𝓝 0))(g:Tendsto d atTop (𝓝 X))(h:X≠0)
include w g h
lemma ripe: ∀ᶠ i:ℕ in atTop, PathsZ H G (NX X) (d i) (t i):=by
 obtain ⟨r,p⟩:=isBounded_iff_subset_ball (0:E4) |>.1 H.k.isBounded; obtain ⟨s,h'⟩:=isBounded_iff_subset_ball (0:E4)|>.1 G.k.isBounded
 let C:= max 1 (s+r); have hx:1≤C:=le_max_left ..; have Hc:0<‖X‖/4:=by have he:=norm_pos_iff.mpr h; positivity
 filter_upwards [(w.mul_const C).eventually (gt_mem_nhds (show 0*C < ‖X‖/4 from (zero_mul _).trans_lt Hc)),g.eventually (ball_mem_nhds X Hc)] with j e a
 intro u v l h w k; have he: ‖l-u‖≤ C:= (norm_sub_le ..).trans ((add_le_add (by simpa using le_of_lt (mem_ball.mp (h' h))) (by simpa using le_of_lt (mem_ball.mp (p v)))).trans (le_max_right ..))
 change t j*C< ‖X‖/4 at e; rw [mem_closedBall]; apply (dist_triangle _ (d j) _).trans
 rw [dist_eq_norm_sub (d j+_), add_sub_cancel_left, norm_smul,Real.norm_of_nonneg k.1]
 have hv: w* ‖l-u‖≤t j*C:= mul_le_mul k.2 he (norm_nonneg _) (k.1.trans k.2); have ht:=mem_ball.mp a; linarith
omit w g h
-- βFee.App.$ Bound U $
structure Rally (b c:ℝ)(x y:ℂ) :Prop where
 go: ‖x‖≤ b
 pay: ‖y‖≤ b
 error: ‖x-y‖≤ b*c
namespace Rally
lemma twice {b d c:ℝ}{x y i j:ℂ}(p:Rally b c x y)(h:Rally d c i j): Rally (b+d) c (x+i) (y+j):=by
 refine ⟨(norm_add_le ..).trans (add_le_add p.go h.go),(norm_add_le ..).trans (add_le_add p.pay h.pay),?_⟩; rw [show x+i-(y+j)=(x-y)+(i-j) from by abel,add_mul]; exact (norm_add_le ..).trans (add_le_add p.error h.error)
lemma threes {b d c:ℝ}{x y i j:ℂ}(p:Rally b c x y)(h:Rally d c i j): Rally (2*b*d) c (x*i) (y*j):=by
 have H:0≤b:=(norm_nonneg _).trans p.go; have he:0≤d:=(norm_nonneg _).trans h.go
 refine ⟨(norm_mul ..).le.trans ((mul_le_mul p.go h.go (norm_nonneg _) H).trans ?_),(norm_mul ..).le.trans ((mul_le_mul p.pay h.pay (norm_nonneg _) H).trans ?_),?_⟩ <;> try nlinarith
 rw [show x*i-y*j=y*(i-j)+(x-y)*i from by ring]
 have hv:‖y*(i-j)‖≤ b*(d*c):= (norm_mul ..).le.trans (mul_le_mul p.pay h.error (norm_nonneg _) H)
 have hx:‖(x-y)*i‖≤ b*c*d:= (norm_mul ..).le.trans (mul_le_mul p.error h.go (norm_nonneg _) ((norm_nonneg _).trans p.error))
 exact (norm_add_le ..).trans ((add_le_add hv hx).trans (le_of_eq (by ring)))
lemma sore {b c:ℝ}{x y:ℂ}(p:Rally b c x y): Rally b c (-x) (-y):=by
 refine ⟨by rw [norm_neg]; exact p.go,by rw [norm_neg]; exact p.pay,?_⟩; rw [show -x- -y= -(x-y) from by abel,norm_neg]; exact p.error
lemma mono {b c d:ℝ}{x y:ℂ}(p:Rally b c x y)(h:b≤d)(v:0≤c): Rally d c x y:= ⟨p.go.trans h,p.pay.trans h,p.error.trans (mul_le_mul_of_nonneg_right h v)⟩
lemma zero (b c:ℝ)(u:0≤ b)(s:0≤c):Rally b c 0 0:= ⟨by simpa,by simpa,by simp [mul_nonneg u s]⟩
end Rally
variable {α β:Type*}(D: Axis→ Module.End ℂ (J α)){L: Axis→ Module.End ℂ (J β)}(p:Bil α β)(a:J α)(b:J β)
lemma viz_C (n m:ℕ)(h:X≠0)(w:Tendsto t atTop (𝓝 0))(g:Tendsto d atTop (𝓝 X)) : ∃ C>0,∀ᶠ i:ℕ in atTop,‖port p (d i) (Wane D a H m (t i)) (Wane L b G n (t i))‖≤ C:=by
 let f(i:ℕ):= port p (d i) (Wane D a H m (t i)) (Wane L b G n (t i)); let P:= port p X (Wane D a H m 0) (Wane L b G n 0)
 have V:Tendsto f atTop (𝓝 P):=by
    unfold f P Wane; simp only [map_sum,map_smul, LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul,Finset.mul_sum]; refine tendsto_finsetSum _ fun j _=>tendsto_finsetSum _ fun u _=>?_ ; -- tune
    have he(q):Tendsto (fun i=>(tariff (t i) q:ℂ)) atTop (𝓝 (tariff 0 q:ℂ)):= continuous_ofReal.continuousAt.tendsto.comp ((w.pow q).mul_const _)
    exact (he _).mul ((he _).mul ((healthy (p _ _) h).continuousAt.tendsto.comp g))
 refine ⟨‖P‖+1,by positivity,(V.norm.eventually (gt_mem_nhds (a:=‖P‖+1) (b:=‖P‖) (by linarith))).mono fun _ p=>le_of_lt p⟩ -- tune
include h g w
lemma tilted (Hh:Lefty p D)(hT:Rorky p L)(m:ℕ)(v:∀ᶠ i:ℕ in atTop, 0<t i): ∃ C>0,∀ᶠ i:ℕ in atTop, PathsZ H G (NX X) (d i) (t i) ∧ Rally C ((t i)^(m+1)) (∫ z:E4×E4,port p (d i + t i • (z.2-z.1)) a b ∂(pairs H G).μ) (port p (d i) (Wane D a H m (t i)) (Wane L b G m (t i))):=by
 obtain ⟨C,cK,T⟩:=rebate D p a b H G m (isCompact_closedBall X _) (NXp X h) Hh hT; obtain ⟨B,Hb,hb⟩:= viz_C H G X d t D (L:=L) p a b m m h w g -- tune order
 refine ⟨C+B,by positivity,?_⟩; filter_upwards [v,ripe H G X d t w g h,w.eventually (gt_mem_nhds (show (0:ℝ)<1 by norm_num)),hb] with i e l Ht f
 change t i<1 at Ht; have hp:= T (t i) (d i) ⟨e.le,Ht.le⟩ l; have hv: 0≤ t i^(m+1):= pow_nonneg e.le _; have ht:t i^(m+1) ≤ 1 := pow_le_one₀ e.le Ht.le
 refine ⟨l, ⟨?_, f.trans (le_add_of_nonneg_left cK.le), hp.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right Hb.le) hv)⟩⟩
 exact (norm_le_norm_sub_add _ _).trans ((add_le_add hp f).trans (add_le_add_left (mul_le_of_le_one_right cK.le ht) B))
end YM.GaugeFieldConstruction.Wick.Yacht
end
