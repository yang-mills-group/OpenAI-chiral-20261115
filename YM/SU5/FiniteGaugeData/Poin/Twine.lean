import YM.SU5.FiniteGaugeData.Poin.Regal
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Function Filter Metric Complex MeasureTheory Set OS OS.Semigroup
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder
variable {n:ℕ}{H:Hilbert}{a:Axis}(S:OS.Semigroup H a)(x y:H)
open Boundary Probe Fin
abbrev Shelf₀ (r:ℝ):Set ℂ:= {x| |x.im|<r}
structure Shelf (S:OS.Semigroup H a) (b:Cross a) where
 cup : ℝ≥0 → ℂ → H.Op
 hol (u:ℝ≥0) (_: 0<u) : AnalyticOnNhd ℂ (cup u) (Shelf₀ u)
 norm (u:ℝ≥0) (z:ℂ)(p:z∈Shelf₀ ↑u): ‖cup u z‖≤4
 realC (u:ℝ≥0) (_:0<u)(t:ℝ): cup u t= S.U (t • b)*S.E u
lemma lyc {X:Type*}[NormedAddCommGroup X][NormedSpace ℂ X](p:Set ℂ){f g:ℂ→X}
 (z:0∈p)(h:IsPreconnected p)(F:AnalyticOnNhd ℂ f p)(G:AnalyticOnNhd ℂ g p)
 (r:∀ᶠ x:ℝ in 𝓝[>] (0:ℝ), f x=g x): Set.EqOn f g p:=by
 refine F.eqOn_of_preconnected_of_frequently_eq G h z ?_; intro h; have hp:Tendsto ((↑):ℝ→ℂ) (𝓝[>] (0:ℝ)) (𝓝[≠] 0):= by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact continuous_ofReal.continuousAt.continuousWithinAt
    filter_upwards [self_mem_nhdsWithin] with i u; exact fun e=> (Set.mem_Ioi.mp u).ne' (by exact_mod_cast (show (i:ℂ)=0 from e))
 obtain ⟨x,p,z⟩:= (r.and (hp.eventually h)).exists; exact z p
lemma polyp {L:ℝ} (p:0<L){f g:ℂ→ H.Op}(F:AnalyticOnNhd ℂ f (Shelf₀ L))(G:AnalyticOnNhd ℂ g (Shelf₀ L))(t:∀ x:ℝ,f x=g x): Set.EqOn f g (Shelf₀ L):= by
 apply lyc _ (by simp [Shelf₀,p]) _ F G (Eventually.of_forall t); apply Convex.isPreconnected; rw [show Shelf₀ L={x:ℂ|-L<x.im}∩{x:ℂ|x.im<L} from by ext; simp [Shelf₀,abs_lt]]; exact Convex.inter (convex_halfSpace_gt Complex.imCLM.toLinearMap.isLinear _) (convex_halfSpace_lt Complex.imCLM.toLinearMap.isLinear _)
variable (b: OS.Cross a) (A: Shelf S b)(z w:ℂ) (u p:ℝ≥0)(m:ℕ)(t:ℝ)
local notation "F"=>parabola S
local notation "ρ"=> A.cup
local notation "d"=> OS.Semigroup.duration
abbrev albe (α:ℝ):H.Op:= S.U (α • b)
local notation "G"=> albe S b
lemma sub_in (r:(u:ℝ)<z.re) : z-d u∈inside:= sub_pos.mpr r
lemma joinRun (r:0<u) (k:(u:ℝ)<z.re): F m (z-d u) * S.E u = F m z:= by
 ext1 x; apply cache_I S m; exact DFunLike.congr_fun (show Cache S m*(F m (z-d u) * S.E u)=Cache S m*F m z from (by
    let Z:=z-d u; have he:(S.F Z)*(S.E u)=S.F z:=by rw [← S.roots_heat r, ← show S.F (Z+d u)=(S.F Z)*(S.F (d u)) from S.pairs (sub_in z u k) (dur.mpr r),show Z+d u=z from sub_add_cancel z (d u)]
    rw [←mul_assoc,recover S m _ (sub_in z u k),recover S m _ (show z∈inside from (show (0:ℝ)≤u from by positivity).trans_lt k)]; exact he)) x
abbrev pendulum (u:ℝ≥0) (w:ℂ): H.Op:= F m (z-d u)*ρ u w
local notation "P" => pendulum S b A z m
lemma pending (r:0<u) (k:(u:ℝ)<z.re): pendulum S b A z m u (t:ℂ)= F m z * G t:=by unfold pendulum; rw [A.realC u r, (show S.U (t • b)*S.E u=S.E u*S.U (t • b) from (S.independent u (t • b)).symm), ←mul_assoc, joinRun S z u m r k]
lemma linkJoin (r:u≤p)(h:(p:ℝ)<z.re)(s:w∈Shelf₀ u): P u w=P p w:=by
 have hk:0<u:= (show (0:ℝ)<u from (abs_nonneg _).trans_lt (show |w.im|< (u:ℝ) from s)); have he(x:ℝ): P u x=P p x:= (pending S b A z u m x hk (lt_of_le_of_lt (by exact_mod_cast r) h)).trans (pending S b A z p m x (hk.trans_le r) h).symm
 apply polyp (show (0:ℝ)<u from hk) (fun x t=> analyticAt_const.mul (A.hol u hk x t)) (fun x t=> analyticAt_const.mul (A.hol p (hk.trans_le r) x (show x∈ Shelf₀ ↑p from (lt_of_lt_of_le (show |x.im|<(u:ℝ) from t) (by exact_mod_cast r))))) he s
abbrev Wheel(z w:ℂ):= w∈ Shelf₀ z.re
def wageX (z w:ℂ):ℝ≥0:= ((z.re+|w.im|)/2).toNNReal
def foil (m:ℕ) (z w:ℂ):H.Op:= pendulum S b A z m (wageX z w) w
local notation "L"=> foil S b A
lemma cups_own (k: Wheel z w) : ((wageX z w):ℝ)<z.re ∧ w∈Shelf₀ ↑(wageX z w):=by
 let t:=(z.re+|w.im|)/2; change _<z.re ∧ |w.im|<((t.toNNReal:ℝ≥0):ℝ); change |w.im|<z.re at k; have he:t<z.re∧ |w.im|<t:=⟨by unfold t; linarith,by unfold t; linarith⟩; change ((t.toNNReal:ℝ≥0):ℝ)<_∧ _; simpa only [Real.coe_toNNReal t ((abs_nonneg _).trans he.2.le)] using he
lemma Lfoil (k:(u:ℝ)<z.re)(p:w∈ Shelf₀ u): foil S b A m z w= pendulum S b A z m u w:=by
 have he: Wheel z w:= lt_trans (show |w.im|<(u:ℝ) from p) k; let t:=wageX z w; obtain ⟨u',v⟩:= cups_own z w he; rcases le_total u t with c|c; exact (linkJoin S b A z w _ _ m c u' p).symm; exact linkJoin S b A z w _ _ m c k v
lemma realF (u:0<z.re): foil S b A m z t=F m z*G t:=by obtain ⟨v,r⟩:=cups_own z t (by simp [Shelf₀,Wheel,u]); exact pending S b A z _ m t (show 0< _ from (by exact_mod_cast (show (0:ℝ)<wageX z t from (lt_of_le_of_lt (abs_nonneg _) (show |(t:ℂ).im|<_ from r))))) v
lemma hol_whole {Z: Type*}[NormedAddCommGroup Z][NormedSpace ℂ Z](x:Z)(f g:Z→ℂ)(p:AnalyticAt ℂ f x)(q:AnalyticAt ℂ g x)(z: Wheel (f x) (g x)): AnalyticAt ℂ (fun x=> L m (f x) (g x)) x:=by
 let u:= wageX (f x) (g x); obtain ⟨v,r⟩:= cups_own _ _ z
 let P':=(fun x:Z=> F m (f x-d u)); have he:P' = _ := (rfl : P'= parabola S m ∘ (fun x=>f x-d u))
 have w:0<u:=(show (0:ℝ) < (u:ℝ) from (abs_nonneg _).trans_lt (show |(g x).im|<_ from r))
 let T(x):=f x-d u; have zq:AnalyticAt ℂ (F m) (T x):= Bokeh S m _ (sub_in (f x) u v); refine ((zq.comp (show AnalyticAt ℂ T x from p.sub analyticAt_const)).mul ( (A.hol u w _ r).comp q)).congr ?_ -- EventuallyEq orientation
 filter_upwards [(continuous_re.continuousAt.tendsto.comp p.continuousAt).eventually (lt_mem_nhds v),((continuous_im.abs).continuousAt.tendsto.comp q.continuousAt).eventually (gt_mem_nhds (show |(g x).im|<(u:ℝ) from r))] with i z t; exact (Lfoil S b A _ _ u m z t).symm
#print axioms hol_whole
-- bank of identities on any strict wheel
variable (p': Wheel z w)(J:H.Op)
lemma wheel_pos(p':Wheel z w): 0<z.re:=(abs_nonneg _).trans_lt (show |w.im|< z.re from p')
lemma funcplus {r:ℂ}(h:r∈inside) (p:Wheel z w): Wheel (z+r) w:= lt_trans (show |w.im|<z.re from p) (lt_add_of_pos_right _ (show 0<r.re from h))
-- shifted along positive
include p'
lemma brassup (v:0<u) : L m (z+d u) w= L m z w*S.E u:=by
 let f(t:ℂ):= L m (z+d u) t; have he(t:ℝ): f t=(L m z t)*S.E u:=by
    let Z':= z+d u; have hp:(u:ℝ)<Z'.re:= lt_add_of_pos_left _ (wheel_pos _ _ p'); have hc:S.U (t • b)*S.E u=S.E u*S.U (t • b):=(S.independent ..).symm
    unfold f; rw [realF S b A _ m t ((show (0:ℝ)≤u from by positivity).trans_lt hp),realF S b A z m t (wheel_pos _ _ p')]; change F m Z'* G t=F m z * S.U (t • b)*S.E u; rw [mul_assoc, hc,← mul_assoc,← show Z'-d u=z from add_sub_cancel_right ..,joinRun S _ _ m v hp]
 exact polyp (wheel_pos _ _ p') (fun i p=> hol_whole S b A m i (fun _=>z+d u) id analyticAt_const analyticAt_id (funcplus z i (dur.mpr v) p)) (fun i p=> (hol_whole S b A m i (fun _=>z) id analyticAt_const analyticAt_id p).mul analyticAt_const) he p'
lemma skirt (c:Commute J (F m z))(r:∀ t:ℝ,Commute J (albe S b t)) : Commute J (foil S b A m z w) :=by
 let f(t:ℂ):=J*L m z t; let g(t:ℂ):= L m z t *J; have h(t:ℝ): f t=g t:=by unfold f g; rw [realF S b A z m t (wheel_pos _ _ p')]; exact c.mul_right (r t)
 have hz(t:ℂ)(p:t∈Shelf₀ z.re) := hol_whole S b A m t (fun _=>z) id analyticAt_const analyticAt_id p
 exact polyp (wheel_pos _ _ p') (show AnalyticOnNhd ℂ f _ from fun i p=>analyticAt_const.mul (hz i p)) (show AnalyticOnNhd ℂ g _ from fun i p=>(hz i p).mul analyticAt_const) h p'
lemma holds(x:E4): Commute (M S x) (L m z w):= by
 let J:=M S x; apply skirt S b A z w m p' J ( (mslot S x z (show z∈inside from wheel_pos _ _ p') m).symm ); intro t; rw [albe,← laneslot S]; exact (tgo S x _).trans ((congrArg (M S) (add_comm ..)).trans (tgo S _ x).symm)
lemma holdsR : Commute (saucer S) (L m z w):=skirt S b A z w m p' _ (gear S _ (show z∈inside from wheel_pos _ _ p') m) (fun t=> cupU S (t • b))
lemma rolling : L m (z+sideways t) w=L m z w*S.edge t:=by
 let g(u:ℂ):= L m z u *S.edge t; have f(u:ℝ): L m (z+sideways t) u=g u:=by
    have hz:= wheel_pos _ _ p'; have hk:0<(z+sideways t).re:=by simp [hz]
    unfold g; rw [realF S b A _ m u hk, realF S b A z m u hz, ←FRight S t m z (show z∈inside from hz)]; rw [mul_assoc,mul_assoc, show S.edge t* G u= G u *S.edge t from S.both t (u • b)]
 have hr (r:ℂ)(p:r∈Shelf₀ z.re):Wheel (z+sideways t) r := by show |r.im|< (z+sideways t).re; simpa using (show |r.im|< z.re from p)
 exact polyp (wheel_pos _ _ p') (fun i p=>hol_whole S b A m i (fun _=>z+sideways t) id analyticAt_const analyticAt_id (hr i p)) (show AnalyticOnNhd ℂ g _ from fun i p=> (hol_whole S b A m i (fun _=>z) id analyticAt_const analyticAt_id p).mul analyticAt_const) f p'
lemma hillside : L m z (w+(t:ℂ))=L m z w*G t:=by
 let f(u:ℂ):=L m z (u+(t:ℂ)); let g(u:ℂ):=L m z u* G t
 have he(r:ℝ): f r=g r:=by unfold f g; rw [← ofReal_add,realF S b A z m (r+t) (wheel_pos _ _ p'),realF S b A z m r (wheel_pos _ _ p'),mul_assoc]; unfold albe; rw [add_smul,S.space]; rfl
 have hp(y:ℂ)(p:Wheel z y): Wheel z (y+(t:ℂ)):=by show |(y+(t:ℂ)).im|< z.re; simpa using (show |y.im|< z.re from p)
 have h:AnalyticOnNhd ℂ f (Shelf₀ z.re):= fun i p=> hol_whole S b A m i (fun _=>z) (fun i=> i+(t:ℂ)) analyticAt_const (analyticAt_id.add analyticAt_const) (hp i p)
 exact polyp (wheel_pos _ _ p') h (show AnalyticOnNhd ℂ g _ from fun i p=> (hol_whole S b A m i (fun _=>z) id analyticAt_const analyticAt_id p).mul analyticAt_const) he p'
lemma aerial : L m z w * Cache S m=L 0 z w:=by
 have he(y:ℝ):L m z y * Cache S m=L 0 z y:=by
    simp_rw [realF S b A z _ y (wheel_pos _ _ p'),mul_assoc,(show Commute (G y) (Cache S m) from ((cupU S _).symm.pow_right m)).eq,←mul_assoc,change_m S _ _ (show z∈inside from wheel_pos _ _ p')]; rfl
 apply polyp (wheel_pos _ _ p') (fun i p=> (hol_whole S b A m i (fun _=>z) id analyticAt_const analyticAt_id p).mul analyticAt_const) (fun i p=> (hol_whole S b A 0 i (fun _=>z) id analyticAt_const analyticAt_id p)) he p' -- p within
#print axioms rolling
#print axioms brassup
#print axioms aerial
lemma fol_norm: ‖L 0 z w‖≤4:=by
 obtain ⟨h,k⟩:=cups_own z w p'; unfold foil pendulum; exact (norm_mul_le ..).trans ( (mul_le_mul (S.norm_row (sub_in _ _ h)) (A.norm _ _ k) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
omit p'
lemma fol_fix : L 0 (OS.Semigroup.duration 1) 0=S.E 1:=by rw [← ofReal_zero,realF S b A _ 0 0 (show 0< _ from dur.mpr zero_lt_one), albe, zero_smul, S.uZero]; change S.F (d 1)*(1:H.Op)=_; rw [mul_one,S.roots_heat zero_lt_one]
variable (α β:ℕ→ℂ)(e:∀ i,Wheel (α i) (β i))(v:Tendsto α atTop (𝓝 0))(k:Tendsto β atTop (𝓝 0))
include e v k
local notation "Θ" i:max=> L 0 (α i) (β i)
lemma aboard (x:H): Tendsto (fun i=> (Θ i) (S.E 1 x)) atTop (𝓝 (S.E 1 x)):=by
 let Z:ℂ:=d 1; have HZ: Wheel Z 0:=show |(0:ℂ).im|< Z.re from (by simp [Z,OS.Semigroup.duration]); let f(y:Prod ℂ ℂ):=L 0 y.1 y.2; have hf : AnalyticAt ℂ f (Z,0):= hol_whole S b A 0 (Z,0) _ _ analyticAt_fst analyticAt_snd HZ; have h₀: f (Z,0)=_:=fol_fix S b A
 have hp: Tendsto (fun i=> α i+Z) atTop (𝓝 Z):= by simpa only [zero_add] using v.add_const Z
 have hw:Tendsto (fun i=>Θ i*S.E 1) atTop (𝓝 (S.E 1)):=by
    nth_rw 2 [← fol_fix S b A] -- changes both left wrong.H
    exact  (hf.continuousAt.tendsto.comp (hp.prodMk_nhds k)).congr (fun i=>(brassup S b A _ _ _ 0 (e i) zero_lt_one))
 exact ( (ContinuousLinearMap.apply ℂ H.space x).continuous.tendsto (S.E 1)).comp hw
lemma secure : Gesture (fun i:ℕ=> foil S b A 0 (α i) (β i)):=by
 have he(i):= fol_norm S b A _ _ (e i); refine ⟨4,he,fun Vh=>?_⟩
 apply Metric.tendsto_nhds.mpr; intro ε hε; obtain ⟨_,⟨g,rfl⟩,h⟩:= Metric.mem_closure_iff.mp (S.whole 1 Vh) (ε/12) (by positivity)
 let u:=S.E 1 g; have hv(i:ℕ): dist ((Θ i) Vh) ((Θ i) u)≤4* dist Vh u:=by
    rw [dist_eq_norm, dist_eq_norm,←map_sub]; exact ((Θ i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (he i) (norm_nonneg _))
 filter_upwards [Metric.tendsto_nhds.mp (aboard S b A α β e v k g) (ε/2) (by positivity)] with i h'; 
 have hh := dist_triangle ((Θ i) Vh) ((Θ i) u) Vh; have hp:= dist_triangle ((Θ i) u) u Vh; rw [dist_comm u Vh] at hp; change dist Vh u< _ at h; change dist _ _ < _ at h'; linarith [hv i]
#print axioms secure
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
