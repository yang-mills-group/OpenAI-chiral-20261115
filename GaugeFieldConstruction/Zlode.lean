import GaugeFieldConstruction.Zigzag
set_option autoImplicit false
noncomputable section
namespace YM.StressFHeat
open Function Filter Metric MeasureTheory Real BigOperators
open GaussianFourier Maxwell Analysis
open scoped RealInnerProductSpace Topology ContDiff
local notation "I"=> Complex.I
-- points and compact domains
abbrev holdW (f: ℝ→ E4 → ℝ):Prop:= ∀ K:Set E4, IsCompact K → 0∉K → ∃ V:ℝ→ℝ,Tendsto V atTop (𝓝 0) ∧ ∀ᶠ z in atTop,∀ x∈K, |f z x| ≤ V z
lemma hold_add {f g : ℝ→ E4→ℝ}(h:holdW f) (p:holdW g): holdW (fun z x=> f z x+g z x):=by
 intro K q u; obtain ⟨c,p,h⟩:= p K q u; obtain ⟨d,m,l⟩:=‹holdW f› K q u; refine ⟨fun i=> d i+c i, (show 0+0=(0:ℝ) from add_zero _) ▸ (m.add p),?_⟩; exact (l.and h).mono fun i v x u=> (abs_add_le ..).trans (add_le_add (v.1 x u) (v.2 x u))
lemma seqN (z:ℝ)(v:0<z)(k:ℕ): Tendsto (fun t:ℝ=> t^k*Real.exp (-z*t)) atTop (𝓝 0):=by simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (↑k) z v)
def winn (z:ℝ)(x:E4):ℝ:=Real.exp (z*(-‖x‖^2/4))
lemma w_lag (k:ℕ)(f:E4→ℝ)(h: ContinuousOn f {x|x≠0}): holdW (fun z x=> z^k*f x*winn z x):=by
 intro K p u
 by_cases v: K.Nonempty; swap; · exact ⟨fun _=>0,tendsto_const_nhds,Eventually.of_forall fun x y t=>(v ⟨y,t⟩).elim⟩
 obtain ⟨a,hA,c⟩:=p.exists_isMinOn v (f:=fun x:E4=>‖x‖) continuous_norm.continuousOn; have ha: a≠0:=fun t=>u (t▸ hA)
 obtain ⟨b,hb,e⟩:= p.exists_isMaxOn v ((h.mono fun x v => (fun t:(x=0)=> u (t ▸ v)): ContinuousOn f K).abs) -- annotation tune
 let z:= ‖a‖^2/4; have hz:0<z:=by unfold z; have hp:=norm_pos_iff.mpr ha; positivity
 refine ⟨fun i=> |f b| * (i^k*Real.exp (-z*i)),by simpa only [mul_zero] using ((seqN z hz k).const_mul |f b|),?_⟩
 filter_upwards [eventually_gt_atTop (0:ℝ)] with i v x h; have ht: abs (winn i x) ≤ Real.exp (-z*i):=by
    unfold winn; rw [abs_of_pos (Real.exp_pos _)]; apply Real.exp_le_exp.mpr; apply le_trans (b:=i*(-z)) _ (le_of_eq (by ring)); unfold z; have hw:=pow_le_pow_left₀ (norm_nonneg a) (c h) 2; nlinarith only [mul_le_mul_of_nonneg_left hw v.le]
 rw [abs_mul,abs_mul,abs_of_pos (pow_pos v k)]; apply (mul_le_mul (mul_le_mul_of_nonneg_left (e h) (pow_nonneg v.le _)) ht (abs_nonneg _) (mul_nonneg (pow_nonneg v.le _) (abs_nonneg _))).trans_eq; ring
abbrev growB (z:ℝ)(k:ℕ)(f:E4→ℝ)(x:E4):= z^k*f x*winn z x
-- induction on grad list, using splitting non-coincident gang.
lemma bendζ (a:Axis)(w:List Axis)(f g h:E4→ℝ)(x:E4)(e:∀ x:E4,x≠0 → g x=f x+h x)(u:x≠0)(m:∀ x:E4,x≠0 → ContDiffAt ℝ ∞ f x)(n:∀ x:E4,x≠0 → ContDiffAt ℝ ∞ h x): regD w g x=regD w f x+regD w h x:=by
 induction w generalizing x with
 | nil=> exact e x u
 | cons b w P=>
    change grad _ _ _=_+_
    change D (basis b) (regD w g) x=_; rw [GermD (g:=regD w f + regD w h) _ ((eventually_ne_nhds u).mono fun i p=>P i p)]
    change fderiv ℝ _ _ _=D (basis b) _ _+D (basis b) _ _; rw [fderiv_add ((quietC w _ x (m x u)).differentiableAt (by decide)) ((quietC w _ x (n x u)).differentiableAt (by decide))]; rfl
lemma angleζ (z:ℝ)(x:E4)(k:ℕ): ContDiffAt ℝ ∞ (winn z) x:=by exact ((contDiff_const.mul ((contDiff_norm_sq (E:=E4) ℝ).neg.div_const (4:ℝ))).exp).contDiffAt
lemma frothy (x:E4) (a:Axis)(z:ℝ): grad a (winn z) x=z*(grad a (fun y:E4=> -‖y‖^2/4) x) * winn z x:=by
 let F(y:E4):ℝ:= -‖y‖^2/4; have h:DifferentiableAt ℝ F x:=by unfold F; first| exact (contDiff_norm_sq (E:=E4) ℝ).neg.div_const (4:ℝ)| exact ((contDiff_norm_sq (n:=1) (E:=E4) ℝ).neg.div_const (4:ℝ)|>.differentiable (by decide)).differentiableAt
 change fderiv ℝ _ _ _=z* (fderiv ℝ F _ _ )* winn z x; have he:= ((h.hasFDerivAt.const_mul z).exp).fderiv; change fderiv ℝ (winn z) x=_ at he; rw [he]; simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]; unfold F at *; unfold winn; ring
lemma winterP (w:List Axis)(f:E4→ℝ)(h:∀ x:E4,x≠0 → ContDiffAt ℝ ∞ f x)(k:ℕ):holdW (fun z=>regD w (growB z k f)):=by
 induction w using List.reverseRecOn generalizing f k with
 | nil=> exact w_lag k f (fun x v=>(h _ v).continuousAt.continuousWithinAt)
 | append_singleton w a P=>
    let F(y:E4):ℝ:= -‖y‖^2/4; let Y(x:E4):ℝ:= f x*grad a F x
    have hx:ContDiff ℝ ∞ F:=by unfold F; first| exact (contDiff_norm_sq (E:=E4) ℝ).neg.div_const (4:ℝ)| exact ((contDiff_norm_sq (n:=1) (E:=E4) ℝ).neg.div_const (4:ℝ)|>.differentiable (by decide)).differentiableAt
    have hf(x:E4)(e:x≠0):ContDiffAt ℝ ∞ (grad a f) x:=quietC [a] _ _ (h _ e)
    have hZ :ContDiff ℝ ∞ (grad a F):= by refine contDiff_iff_contDiffAt.mpr fun i=> quietC [a] _ _ hx.contDiffAt
    have hu(x:E4)(e:x≠0):ContDiffAt ℝ ∞ Y x:=(h _ e).mul hZ.contDiffAt
    have hl(z:ℝ)(x:E4)(e:x≠0): regD (w++[a]) (growB z k f) x= regD w (growB z k (grad a f)) x+regD w (growB z (k+1) Y) x:=by
       rw [show regD (w++[a]) (growB z k f)= regD w (grad a (growB z k f)) from (by unfold regD; rw [List.foldr_append]; rfl)]
       apply bendζ a _ _ _ _ _ ?_ e (fun i p=>(contDiffAt_const.mul (hf i p)).mul (angleζ z _ k)) (fun i p=>(contDiffAt_const.mul (hu i p)).mul (angleζ z _ k))
       intro i p; have hh z:=angleζ z i k; let L:=(((h i p).differentiableAt (by decide)).hasFDerivAt.const_mul (z^k)).mul ((hh z).differentiableAt (by decide)).hasFDerivAt
       have ht:fderiv ℝ (growB z k f) i=_:=L.fderiv
       change fderiv ℝ _ _ _= _; rw [ht]; simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]; rw [show fderiv ℝ (winn z) i (basis a)= _ from frothy i a z]; change _=z^k*fderiv ℝ f i (basis a)*winn z i + z^(k+1)*(f i*grad a F i)*winn z i; unfold F; ring
    intro K g u
    obtain ⟨W,H,Q⟩:= hold_add (P (grad a f) hf k) (P Y hu (k+1)) K g u
    refine ⟨W,H,Q.mono fun i h t p=>?_⟩; dsimp only; rw [hl i t (fun o=>u (o▸p))]; exact h t p
lemma autumnP (w:List Axis):holdW (fun z x=> regD w (fun x=>Woof x z⁻¹) x-regD w Green x):=by
 have he(z:ℝ)(x:E4)(v:x≠0): regD w (fun x=>Woof x z⁻¹) x-regD w Green x=regD w (growB z 0 (-Green)) x:=by
    rw [bendζ 0 _ Green (fun x=>Woof x z⁻¹) (growB z 0 (-Green)) x ?_ v (fun x u=> freeSmooth u) (fun x u=> (contDiffAt_const.mul (freeSmooth u).neg).mul (angleζ z _ 0)),add_sub_cancel_left]
    intro x _; unfold growB Woof winn; simp only [pow_zero,one_mul,Pi.neg_apply]; ring_nf; rw [inv_inv] -- ∀ z incl 0 by field inverse algebra
 intro K u v; obtain ⟨W,h,m⟩:= winterP w (-Green) (fun x p=> (freeSmooth p).neg) 0 K u v; exact ⟨W,h,m.mono fun i u' x t=> (show abs (_-_) ≤ _ from by rw [he i x (fun l=> v (l ▸ t))]; exact u' x t)⟩
end YM.StressFHeat
end
