import YM.SatinExist.Sylphid
/-!
 # Inflationary budgets on D∞, recovered norms.
-/
set_option autoImplicit false
set_option maxRecDepth 2400
set_option maxHeartbeats 215000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j:Axis} (S : OS.Semigroup H j) (n:ℕ)
local notation "Λ" => 𝓝[>] (0:ℝ)
local notation "E" => elast S
local notation "D" => Bench S
local notation "K" =>Cache S
variable (A:ℝ → H.Op) (C:H.Op)
-- if exists bound of two different orders, unique operator fields.
lemma mint_unique (B:H.Op)(p:RealMint S n A B)(q:RealMint S n A C): B=C:=by
 let F:= S.E 1
 have h:F*B*F=F*C*F:= ((realMint_eq _ _ _ _).mp p 1 zero_lt_one).symm.trans ((realMint_eq ..).mp q 1 zero_lt_one)
 ext1 x; have he: F* B=F * C := DFunLike.coe_injective ((S.whole 1).equalizer (F*B).continuous (F*C).continuous (funext fun z=> DFunLike.congr_fun h z)) -- API tune
 apply sub_eq_zero.mp; apply S.heat_faithful 1; rw [map_sub,sub_eq_zero]; exact DFunLike.congr_fun he x
lemma price_same (m:ℕ)(f:Test4): ℑ S C f n= ℑ S (K m*C*K m) f (m+n):=by
 ext1 x; apply Subtype.ext; apply cache_I S (m+n); let U:=K m; have hp:S.unit.P=S.unit.P:=rfl
 change K (m+n) _ = _; rw [native,cacheA]; change U (K n (ℑ S C f n x).val)= _; let z:=hall S (m+n) x
 rw [native,overlap_R,overlap]; change _=U (valise S C f (K m _)); rw [add_comm m n, downstairs] -- binder add. name tactic
 all_goals intro p; exact ((tread S p).pow_left m).symm
-- SOT critical
lemma valise_rises (F:ℕ→ H.Op)(p:∀ y:H,Tendsto (fun i=> F i y) atTop (𝓝 (C y))) (b:ℝ)(q:∀ᶠ i:ℕ in atTop,‖F i‖ ≤ b)(f:Test4)(x:H): Tendsto (fun i=>valise S (F i) f x) atTop (𝓝 (valise S C f x)):=by
 let ζ(i:ℕ)(z:E4):= f z • optx S (F i) z x; let Z(z:E4):= f z • optx S C z x; let d(z:E4):= ‖f z‖*(b*‖x‖); have hu(z:E4): Tendsto (fun i=>ζ i z) atTop (𝓝 (Z z)):= (((M S z).continuous.continuousAt.tendsto).comp (p (M S (-z) x))).const_smul (f z) -- continuous
 apply (show Tendsto _ atTop _ from (show Tendsto (fun i:ℕ=> ∫ u,ζ i u) atTop (𝓝 (∫ z,Z z)) from tendsto_integral_filter_of_dominated_convergence d (Eventually.of_forall (fun i=> emberI S x (F i) f |>.aestronglyMeasurable)) ?_ (f.integrable.norm.mul_const _) (Eventually.of_forall hu)))
 exact q.mono (fun v hp=> Eventually.of_forall (fun i=> (spice S x (F v) f i).trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) (norm_nonneg _))))
variable (F:ℕ→ H.Op)(p:∀ y:H,Tendsto (fun i=> F i y) atTop (𝓝 (C y))) (b:ℝ)(q:∀ᶠ i:ℕ in atTop,‖F i‖ ≤ b)(f:Test4)(x:Bench S)(u:ℕ→Bench S)(w:pays_to S atTop u x)
include p q
lemma brochure_go (x:H):Tendsto (fun i=> brochure S (F i) n f x) atTop (𝓝 (brochure S C n f x)):=by
 induction n generalizing f x with
 | zero=>exact valise_rises S C F p b q f x
 | succ n ih=> exact (ih f x).add (ih _ ((saucer S) x))
omit p q in
private lemma cdk (u:ℕ) (f:Test4):0 ≤ dollycoin j u f:=by
 induction u generalizing f with | zero=> exact norm_nonneg _ | succ n ih=> exact add_nonneg (ih f) (ih _)
include w
lemma purchase (m:ℕ): pays_to S atTop (fun i=> ℑ S (F i) f m (u i)) (ℑ S C f m x):=by
 intro n; simp_rw [graphN]; let B(i:ℕ):= brochure S (F i) (m+n) f; let Y(i:ℕ):= hall S (m+(m+n)) (u i); let y:=hall S (m+(m+n)) x; let r:=dollycoin j (m+n) f*b
 have e:Tendsto (fun i=>B i (Y i-y)) atTop (𝓝 0):= tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero' (Eventually.of_forall fun _=>norm_nonneg _) (q.mono (fun i hu=> ((B i).le_opNorm _).trans (mul_le_mul_of_nonneg_right ((dollyP S (F i) f (m+n)).trans (mul_le_mul_of_nonneg_left hu (?_ : 0 ≤ dollycoin j (m+n) f))) (norm_nonneg _)))) (show Tendsto (fun i=>r* ‖Y i-y‖) atTop _ from by simpa only [sub_self, norm_zero,mul_zero,y] using ((w (m+(m+n))).sub_const y).norm.const_mul r))
 · have h:= e.add (brochure_go S (m+n) C F p b q f y); rw [zero_add] at h; refine h.congr ?_; intro a; change B a (Y a-y)+ B a y=B a (Y a); rw [map_sub,sub_add_cancel]
 exact cdk (m+n) f -- include pp. arguments
omit w p q
-- Warm/physical smear limit in test. Each product fixed heights after birth H TRUE, genuine spectral norm graph in unpadding.
lemma heatigher (f:Test4) (U:RealMint S n A C)(t:ℝ≥0)(z:0<t) (x:D): ℑ₀ S (A t) f x= stove S t (ℑ S C f n (stove S t x)):=by
 apply Subtype.ext; apply cache_I S n
 let G:= S.E t; have h:G* K n = K n* G := ((cupE S t).pow_left n).eq.symm; have ht:= (realMint_eq ..).mp U t z
 change K n (valise S (A t) f x.val)=K n (G (ℑ S C f n (stove S t x)).val);
 let p:=hall S n x
 have b: hall S n (stove S t x)= G p:= park_κ S n _ _ _ _ h
 rw [show ∀ z:H,K n (G z) = G (K n z) from fun z=>DFunLike.congr_fun h.symm z,native,b,← show K n p=x.val from releases S n x]
 refine Eq.trans (DFunLike.congr_fun (?_ : K n* valise S (A t) f* K n=G*valise S C f*G) p) rfl
 have v(y:E4):Commute (M S y) G := (S.overE _ y).symm -- check order
 have q(y:E4):Commute (M S y) (K n) := ((tread S y).pow_left n).symm
 have e:=congrArg (fun z=> valise S z f) ht; rw [overlap_R _ _ _ _ q,overlap _ _ _ _ q, overlap_R _ _ _ _ v, overlap _ _ _ _ v] at e; exact e
lemma δLimit {U:Type*}(ℱ:Filter U)(g:U→ℝ≥0)(h:Tendsto g ℱ (𝓝[>] (0:ℝ≥0))) (c:U→D)(p:pays_to S ℱ c x)(q:RealMint S n A C): pays_to S ℱ (fun i=> ℑ₀ S (A (g i)) f (c i)) (ℑ S C f n x) := by
 have e:= stoveLim S 0 x ℱ c g (h.mono_right nhdsWithin_le_nhds) p -- order check
 have he:pays_to S ℱ (fun i=> stove S (g i) (c i)) x:=by rwa [stove_zero] at e
 let d:= fun i=> ℑ S C f n (stove S (g i) (c i)); have a:pays_to S ℱ d _:= ℑLim₁ S C f _ n ℱ _ _ tendsto_const_nhds he
 let v:= ℑ S C f n x; have t:pays_to S ℱ (fun i=> stove S (g i) (d i)) (stove S 0 v):= stoveLim S 0 v ℱ d g (h.mono_right nhdsWithin_le_nhds) a
 rw [stove_zero] at t
 intro m; apply (t m).congr'; filter_upwards [h.eventually self_mem_nhdsWithin] with i hi; exact congrArg _ (heatigher S n A C f q (g i) hi _).symm
end YM.SatinJets
