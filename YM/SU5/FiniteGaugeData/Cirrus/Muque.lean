import YM.SU5.FiniteGaugeData.Cirrus.Floraison
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Maison
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Mink.Lorentz
open scoped Topology NNReal InnerProductSpace Classical
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E] (F G: H.space→L[ℂ]E)(x y:H)
private def quoteE(z:ℂ):= F (S.edge (-z.im) (S.E z.re.toNNReal x))
local notation "F'" => quoteE S F x
local notation "G'" => quoteE S G y
private lemma spanC : Continuous (quoteE S F x):=by unfold quoteE; exact F.continuous.comp (S.cont_edge (fun z:ℂ=> S.E z.re.toNNReal x) (fun z:ℂ=>-z.im) ((S.continuousE x).comp (continuous_real_toNNReal.comp continuous_re)) continuous_im.neg)
private lemma orbitE_0(z:ℂ)(p:z.re=0) : quoteE S F x z= F (S.edge (-z.im) x):=by unfold quoteE; rw [p, Real.toNNReal_zero,S.eZero]; rfl
private lemma routeH(z:ℂ)(h:z∈inside): AnalyticAt ℂ (quoteE S F x) z:=by
 apply (AnalyticAt.comp ((F.comp (ContinuousLinearMap.apply ℂ H.space x)).analyticAt _) (S.localHeat z h)).congr
 filter_upwards [OS.Semigroup.open_inside.mem_nhds h] with z q; have hp:0< z.re.toNNReal:=Real.toNNReal_pos.mpr q; have he: duration z.re.toNNReal + sideways (-z.im)= z:= Complex.ext (by simp [duration, Real.coe_toNNReal _ (show 0< z.re from q).le]) (by simp [duration,sideways])
 apply Eq.symm; unfold quoteE; rw [← S.roots_heat hp]; exact congrArg F ((DFunLike.congr_fun (S.along (dur.mpr hp) (-z.im)) x).trans (congrArg (fun z=>S.F z x) he))
private lemma routeNorm(z:ℂ): ‖quoteE S F x z‖ ≤ ‖F‖*‖x‖:=by
 unfold quoteE; apply le_trans (F.le_opNorm _) _; rw [S.life]; exact mul_le_mul_of_nonneg_left (((S.E _).le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (S.shrinks _))) (norm_nonneg _)
set_option quotPrecheck false
local notation "P"=> setOf (fun z:ℂ=>0≤ z.re)
local notation "J"=> inside
lemma pontiac (p:∀ t:ℝ,F (S.edge t x)=G (S.edge (-t) y)) : ∀ s:ℝ,F (S.edge s x)=F x:=by
 let f:= piecewise P (F') (fun z=> G' (-z)); have hL(z:ℂ)(h:0≤z.re):f z=F' z:= piecewise_eq_of_mem _ _ _ (h:z∈P); have hf(z:ℂ)(h:z.re=0): F' z= G' (-z):=by rw [orbitE_0 _ _ _ _ h, orbitE_0 S _ _ _ (by simp [h]),p, neg_im]; -- ends
 have hR(z:ℂ)(h:z.re<0):f z=G' (-z):= piecewise_eq_of_notMem _ _ _ ((not_le.mpr h):z∉ P)
 have ht:Continuous f:= by
    apply continuous_piecewise ?_ (spanC S F x).continuousOn ((spanC S G y).comp continuous_neg).continuousOn
    intro z p; have he:=frontier_subset_iff_isClosed.mpr (show IsClosed P from isClosed_le continuous_const continuous_re) p; refine hf z (le_antisymm ?_ (show 0≤ z.re from he)); exact le_of_not_gt fun e=> p.2 ( interior_maximal (show J⊆P from fun i v=> show 0 ≤ i.re from le_of_lt v) open_inside e)
 have hv:Differentiable ℂ f:= by
    apply differentiableOn_univ.mp (shear univ f ht.continuousOn ?_ isOpen_univ); intro z _ h; rcases lt_or_gt_of_ne h with h|h
    · apply ((routeH S G y (-z) (show 0<(-z).re from neg_pos.mpr h)).differentiableAt.comp (f:=fun z:ℂ=>-z) z (by fun_prop)).congr_of_eventuallyEq; filter_upwards [(isOpen_lt continuous_re (continuous_const (y:=(0:ℝ)))).mem_nhds h] with z h; exact hR z h
    apply (routeH S F x z h).differentiableAt.congr_of_eventuallyEq; filter_upwards [open_inside.mem_nhds (show z∈ inside from h)] with z h; exact hL z (show 0< z.re from h).le
 let c:=max (‖F‖*‖x‖) (‖G‖*‖y‖); have hj(z:ℂ):‖f z‖≤ c:=by
    rcases lt_or_ge z.re 0 with e|e; · rw [hR z e]; exact le_max_of_le_right (routeNorm ..);
    rw [hL z e]; exact le_max_of_le_left (routeNorm ..)
 have hP:=hv.apply_eq_apply_of_bounded (?_); swap; · apply (show Bornology.IsBounded (Metric.closedBall (0:E) c) from Metric.isBounded_closedBall).subset; rintro _ ⟨x,rfl⟩; rw [Metric.mem_closedBall, dist_zero_right]; exact hj x
 let Z(t:ℝ):ℂ:=⟨0,-t⟩; have H(t:ℝ): f (Z t)= F (S.edge t x):=by
    rw [hL (Z t) (le_refl 0),orbitE_0 S F x (Z t) rfl]; unfold Z; simp
 intro s; rw [← H]; apply (hP (Z s) (Z 0)).trans ((H 0).trans (congrArg F ?_)); rw [S.birth]; rfl
open Mink Mink.Poincare
local notation "K"=>basis timeAxis
local notation "V"=> M S
variable (W:Boundary.Action H)(v:∀ x:E4,W.orbit.translation x=M S x)
include v
lemma palindrome (p:∀ x':E4,F (M S x' x)=G (M S (-x') y)) : ∀ t:E4,F (M S t x)=F x:=by
 have hU(z:E4)(L:Lorentz)(t:ℝ): F (V (z+t • L.act K) x)=F (V z x):=by
    let Pn:= motion L; let A:= W.V Pn; let w(r:ℝ):=r • L.act (K);  have he (U:E4)(V': H.space →L[ℂ] E)(s:ℝ)(x:H.space): V' (V (U+w s) x)=(V'.comp (V U*A)) (S.edge s (W.V Pn⁻¹ x)):=by rw [← tgo,raised S W v]; rfl
    let P':=(F.comp (V z*A)); let Q:=(G.comp (V (-z)*A)); have h(r:ℝ): P' (S.edge r (W.V Pn⁻¹ x))= Q (S.edge (-r) (W.V Pn⁻¹ y)):=by unfold P' Q; rw [←he,←he,p]; congr 2; unfold w; simp [add_comm]
    let u:= W.V Pn⁻¹ x; let g:=pontiac S P' Q u _ h; change F (V (z+w t) x)= _; rw [he]; refine (g t).trans ((g 0).symm.trans ((he z F 0 x).symm.trans (?_)))
    simp [w]
 intro t; obtain ⟨a,b,e,r⟩:= alongSplit t; rw [r,hU]; have hv:=hU 0 (1:Lorentz) a; simpa [tini] using hv
#print axioms palindrome
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Maison
