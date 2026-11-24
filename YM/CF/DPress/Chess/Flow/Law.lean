import YM.Push.GRID_APPROXIMATION.KernelLocal
import YM.CF.DPress.FD.Law.Dream
/-! Actual phase generator. Re-use a local block expectation lemma (parts_back...) from
 project, arising by marginalizing the `shared` frame tags and `per link` terms. Write it in
 probability form so it can be used for the union of requests in each directional half. The
 proof doesn't factorize the conditional distribution of all coarse links given the fine field. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess.Transit
open Function Set Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal
variable {n m:Side}{G:Gauge}{S:StepData n m}
variable {Y:Type*}[NormedAddCommGroup Y][NormedSpace ℝ Y]
local notation "Z"=> Config G n
variable {β:ℝ}(p:S.patch.Branches S.kernel G)
def Ξ (G:Gauge)(S:StepData n m)(β:ℝ)(x:Config G m): Measure (Config G n):= (prior G n).withDensity fun z=> ENNReal.ofReal (S.density β x z)
variable (x:Config G m)
local notation "ν" => Ξ G S β x
include p
lemma paid : IsProbabilityMeasure (Ξ G S β x):=by
 let h:=S.isKernel p β; have ht:0≤ᵐ[(prior G n)] S.density β x:= Eventually.of_forall (h.positive x); refine ⟨?_⟩; rw [Ξ,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ, ←ofReal_integral_eq_lintegral_ofReal (h.integrable x) ht, h.total]; exact ENNReal.ofReal_one
lemma card (f:Z→Y) : (∫ z,f z∂ν)=∫ z, S.density β x z • f z ∂prior G n:=by
 let k:=fun z:Z=> ENNReal.ofReal (S.density β x z); unfold Ξ; rw [integral_withDensity_eq_integral_toReal_smul (f:=k) _ _];
 · simp only [k, ENNReal.toReal_ofReal (S.density_positive β x _)]
 · exact ((S.isKernel p β).meas.comp measurable_prodMk_left).ennreal_ofReal
 exact Eventually.of_forall fun _=> ENNReal.ofReal_lt_top
lemma mass (t:Set (Config G n))(h:MeasurableSet t): back S β (t.indicator (fun _=>(1:ℂ))) x = ((Ξ G S β x).real t:ℂ):=by
 letI:IsProbabilityMeasure ν:= paid p x; rw [show back _ _ _ _=∫ z, t.indicator _ z∂ν from ?_, integral_indicator h,setIntegral_const]; exact (Complex.real_smul ..).trans (mul_one _); rw [card p x]; exact integral_congr_ae (Eventually.of_forall fun z=>(Complex.real_smul ..).symm)
omit p
-- setoid of field restrictions. share.
def Ties (G:Gauge)(S:Support n):Setoid (Config G n) where
 r:= Agrees S
 iseqv:=⟨fun _ i x z=>rfl,fun p i x z=> (p i x z).symm,fun p q i x z=>(p i x z).trans (q i x z) ⟩
def orig{X:Type*}{V:Gauge}{n:Side}(S:Support n)(f:Config V n→X):Prop:=LocalOn S f
abbrev ink {V:Type*}(S:Set V) := S.indicator (fun _=>(1:ℂ))
private lemma inkE {V:Type*}[MeasurableSpace V] {S:Set V}(p:MeasurableSet S): Envelope (ink S):=⟨measurable_const.indicator p,1,fun x=> by by_cases h:x∈S <;> simp [ink,h]⟩
private lemma ink_t(S:Support n)(F:Set Z)(p:FD.Uses (·∈F) (Ties G S)) : LocalOn S (ink F):=by
 intro x y h; unfold ink; have he:(x∈F)=(y∈F):=p x y h; by_cases v:x∈ F; · rw [Set.indicator_of_mem v, Set.indicator_of_mem (he ▸ v)]
 rw [Set.indicator_of_notMem v,Set.indicator_of_notMem (he ▸ v)]
include p
abbrev market : FD.OrderF (FD.BasicIid.P2 (Site n)) (Ξ G S β x) where
 see W:= Ties G W
 more A B e _ _ h:= agrees_mono h (Finset.coe_subset.mpr e)
 pair A B h F K g f F' K':= by
    letI:IsProbabilityMeasure ν:= paid p x
    have he:= congrFun (back_factors p (inkE g) (inkE f) (ink_t _ _ F') (ink_t _ _ K') (Finset.disjoint_coe.mpr (FD.BasicIid.P2U.mp h)) β) x; have ht:ink F*ink K=ink (F∩K):=funext fun i=> by by_cases l:i∈F <;> by_cases h:i∈K <;> simp [ink,l,h]
    rw [ht,Pi.mul_apply,mass p x (F∩K) (g.inter f),mass p x F g,mass p x K f,←Complex.ofReal_mul,Complex.ofReal_inj] at he; apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).1; rw [ENNReal.toReal_mul]; exact he -- tune rw ink wrappers
lemma field_map{X:Type*}[MeasurableSpace X] (Y:Config G m){A:Support n}(f:Z→X)(h:Measurable f)(t:LocalOn A f) (B:Support m)(v:∀ i∈ A,Push.GridApprox.window (S.ratio.embed i) (reach S.patch)⊆ ↑B)(u:Agrees B x Y): (Ξ G S β x).map f=(Ξ G S β Y).map f:=by
 haveI:IsProbabilityMeasure (Ξ G S β x):= paid p x; haveI:IsProbabilityMeasure (Ξ G S β Y):= paid p Y; ext i w; rw [Measure.map_apply h w,Measure.map_apply h w]; let X':= f ⁻¹' i; have he : LocalOn A (ink X'):= ink_t _ _ (fun x y p=> propext (by change f x ∈ i↔ f y ∈ i; rw [t x y p]))
 let Z':= h w; have g:= back_local p (inkE Z') he β (B:Set (Site m)) v x Y u; rw [mass p x _ Z',mass p Y _ Z',Complex.ofReal_inj] at g; exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 g
end YM.CF.DPress.Chess.Transit
