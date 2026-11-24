import YM.CF.Jet.Subsidy
import YM.Planned.ATOM_REGULAR_ESTIMATE.Parametric
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Orin
/-! Differentiating only on positive law supports; no volume loss for localized queries. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric MeasureTheory Phase Phase.Sample Planned.AtomRegular
open scoped Topology BigOperators ContDiff
variable {I T E Y:Type}[Fintype I][DecidableEq I][TopologicalSpace T][CompactSpace T][T2Space T][SecondCountableTopology T][MeasurableSpace T][BorelSpace T][Nonempty T]{μ:Measure T}[IsProbabilityMeasure μ]
variable [NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E][NormedAddCommGroup Y][NormedSpace ℝ Y][CompleteSpace Y]
variable {S:Set E}{n:ℕ}{C K a:ℝ}{p: E→Plan I μ}
lemma under {T':Type}[MeasurableSpace T']{μ':Measure T'}{f:T'→E→Y}(l:IsOpen S)(h:∀ t:T',∀ y∈S,ContDiffAt ℝ (↑n:WithTop ℕ∞) (f t) y)(k:∀ x∈S,StronglyMeasurable (fun t=>f t x)){b:T'→ℝ}(hex:Integrable b μ')(hp:∀ t:T',∀ x∈S, Allows n (f t) x (b t)) :Under μ' f n S b:=⟨Eventually.of_forall h,fun i t y hx=>(ConnectedActivityE6.Blaze.Meristem.legs l h k t hx).aestronglyMeasurable,hex,Eventually.of_forall fun t x hx=> (hp t x hx).norm_le⟩
def priceP(a K C:ℝ)(n m:ℕ):= (n.factorial:ℝ)*((1+n*K*a)^m*(C+n*C*a))*a⁻¹^n
def mercury (S:ℕ)(n:ℕ)(K C:ℝ):= (n.factorial:ℝ)*Real.exp (n*K)*(C+n*C)*(1+S)^n
lemma tariff (hK:0≤K)(hC:0≤C)(n S:ℕ): priceP (1/(1+S:ℝ)) K C n S ≤ mercury S n K C:=by
 unfold priceP mercury; set a:=1/(1+S:ℝ); have ht:0<a:=by unfold a; positivity
 have hp:a≤1:=by unfold a; field_simp; linarith [Nat.cast_nonneg (α:=ℝ) S]
 let v:=n*K*a; have hv:0≤v:=by unfold v; positivity
 have h: (1+v)^S ≤ Real.exp (n*K):=by
    calc
     _ ≤ (Real.exp v)^S:= by gcongr; linarith [Real.add_one_le_exp v]
     _ = Real.exp (S*v):= by rw [Real.exp_nat_mul]
     _ ≤ _:= Real.exp_le_exp.mpr (by unfold v a; field_simp; nlinarith [Nat.cast_nonneg (α:=ℝ) S, Nat.cast_nonneg (α:=ℝ) n])
 rw [← mul_assoc (n.factorial:ℝ),show a⁻¹=(1+S:ℝ) by unfold a; simp]; apply mul_le_mul_of_nonneg_right _ (by positivity); exact mul_le_mul (mul_le_mul_of_nonneg_left h (by positivity)) (add_le_add_right (mul_le_of_le_one_right (by positivity) hp) C) (by positivity) (by positivity)
variable (P:FireK S p K n)
include P
lemma waitA (q:E→(I→T)→Y)(r:Finset I)(A:∀ t:I→T,∀ x∈ S, sails (p x) r t≠0→ Allows n (fun x=> q x t) x C)(hc:0≤C)
    (M:∀ x∈S,StronglyMeasurable (fun t:I→T=>sails (p x) r t • q x t))(x:E)(g:x∈ S)(h:0<a)(ha:a≤1) : Allows n (fun y:E=>∫ t:I→T,sails (p y) r t • q y t ∂fares I μ) x (priceP a K C n r.card):=by
 let v:=n*K*a; have hk:=P.pos; have hv:0≤v:=by unfold v; positivity
 let f(t:I→T)(x:E):=sails (p x) r t • q x t
 have hm (x) (y:x∈S) (t): Allows n (f t) x (meter a K C n r (p x) t):= stokes_support P t r _ hc h ha y (A t)
 have he (y:E)(s:y∈S)(t:I→T): meter a K C n r (p y) t≤ (n.factorial:ℝ)*((K+v)^r.card*(C+n*C*a))*a⁻¹^n:=by
    unfold meter; gcongr; unfold subsidize
    calc
     _ ≤ ∏ _ ∈ r,(K+v) := Finset.prod_le_prod (fun i _=> add_nonneg ((p y).rightF ..) hv) (fun i _=> add_le_add_left (by simpa [Real.norm_of_nonneg ((p y).rightF ..)] using (P.budget _ s i t).value) _)
     _ = _ :=by simp
 have H:=under P.support (f:=f) (fun t x hx=> (hm x hx t).smooth) M (integrable_const (μ:=fares I μ) _) (fun t y hy=>(hm y hy t).mono (he y hy t))
 refine ⟨H.germ P.support g,fun i e=> ?_⟩
 rw [show (fun y:E=> ∫ t:I→T,sails _ r t • q y t ∂fares I μ)=average (fares I μ) f from rfl,(H.less e).differentiate P.support g]
 have hg:Continuous (meter a K C n r (p x)):= Continuous.mul (Continuous.mul continuous_const ((sub_c _ _ r).mul continuous_const)) continuous_const
 calc
   _ ≤ _ := norm_integral_le_integral_norm _
   _ ≤ ∫ t, meter a K C n r (p x) t ∂fares I μ:=integral_mono (H.integrate g e).norm (net_compact hg) (fun t=> hm x g t|>.norm_le i e)
   _ = _:=by unfold meter priceP; rw [integral_mul_const,integral_const_mul, integral_mul_const,sub_norm _ v hv r]

lemma waitB (q:E→(I→T)→Y)(r:Finset I)(hR:∀ x∈S,Bank (p x) r)(A:∀ t:I→T,∀ x∈ S, fall (p x) t≠0→ Allows n (fun x=> q x t) x C)(hc:0≤C)
    (B:∀ x∈S,∀ t u, fall (p x) t≠0→fall (p x) u≠0→AgreeF r t u→ q x t=q x u)
    (M:∀ x∈S,Continuous (fun t:I→T=>fall (p x) t • q x t))(x:E)(g:x∈ S) : Allows n (fun y:E=>∫ t:I→T,fall (p y) t • q y t ∂fares I μ) x (mercury r.card n K C):=by
  classical
  let G (x:E)(t:I→T):=aerate r μ (bet (p x) (q x)) t
  let F(x:E)(t:I→T):=(sails (p x) r t)⁻¹ • G x t
  have he (x:E)(h:x∈S)(t u:I→T)(l:fall (p x) u≠0)(p':AgreeF r t u): F x t=q x u :=by
    let T:=p x; have hv:sails T r u≠0:=by rw [fuel T (hR _ h) (x:=u) (y:=u) (fun _ _=>rfl)] at l; exact left_ne_zero_of_mul l
    unfold F G; rw [banked (p x) (hR _ h) p',aerate_agree (μ:=μ) _ p', aer_side _ _ (hR _ h),smul_smul,inv_mul_cancel₀ hv,one_smul]; exact fun b c d=> B x h b u d l c
  have ht (x:E)(h:x∈S) (t:I→T): sails (p x) r t • F x t=G x t:=by
    unfold F; by_cases v:sails (p x) r t=0; rw [show G x t=0 from aer_miss _ _ (hR _ h) _ v]; simp
    rw [smul_smul,mul_inv_cancel₀ v,one_smul]
  have hP (t:I→T)(z:E)(l:z∈S)(w:sails (p z) r t≠0): Allows n (fun y=> F y t) z C:=by
    obtain ⟨u,h,hK⟩:= widens (p z) (hR z l) t w
    refine (A u z l hK).germ ?_
    filter_upwards [P.support.mem_nhds l, (show ContinuousAt (fun y=>fall (p y) u) z from (fire_num P l _ _).continuousAt).eventually_ne hK] with y hy g using (he y hy t u g (AgreeF.flip h)).symm
  have hM(z:E)(l:z∈S):Continuous (fun t:I→T=> sails (p z) r t • F z t):=by simp_rw [ht z l]; exact aerate_cont r μ (M z l)
  have hR':= tariff P.pos hc n r.card
  apply ((waitA P F r (fun t x h=> hP t x h) hc (fun z t=>(hM z t).stronglyMeasurable) x g (a:=1/(1+r.card:ℝ)) (by positivity) (by field_simp; linarith [Nat.cast_nonneg (α:=ℝ) r.card])).mono hR').germ
  filter_upwards [P.support.mem_nhds g] with x hx
  simp_rw [ht x hx]; exact split_air (μ:=μ) r (M x hx)
end YM.CF.Jet
