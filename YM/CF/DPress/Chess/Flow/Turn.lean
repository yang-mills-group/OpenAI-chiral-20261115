import YM.CF.DPress.Chess.Flow.Pair
import YM.CF.DPress.Chess.Planes.Sleeve
import YM.Branch.Covariant
/-! Reflection action (at grid displacement) on generated field and shared Forest. No positivity from this yet. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Transit
open Function Filter Lattice RG Wilson MeasureTheory ProbabilityTheory Push.GridApprox FD Skye Tree Precision Rush Spire
open Cube (More assembly)
open scoped Topology BigOperators Pointwise Classical ENNReal NNReal Bough
variable (W:Wall){n m:Side}{K:Ratio n m}{S:StepData (More n) (More m)} (t:S.ratio= ratio K)(p:S.patch.Branches S.kernel SU.group)
variable {X Y:Type*}[MeasurableSpace X][MeasurableSpace Y]{μ:Measure X}{ν:Measure Y}
lemma expect {R:Type*}[NormedAddCommGroup R][NormedSpace ℝ R][SecondCountableTopology R][MeasurableSpace R][BorelSpace R](f:X→Y)(h:MeasurePreserving f μ ν)(g:Y→ R)(t:Measurable g): (∫ x,g (f x)∂μ)=(∫ x, g x∂ν):=by rw [←h.map_eq,integral_map h.measurable.aemeasurable t.aestronglyMeasurable]
namespace Turn
local notation "Ω" => W.boost K.count
include t p
lemma density(β:ℝ)(x:Pane m)(y:Pane n): S.density β ((Ω).shine m x) (W.shine n y)= S.density (G:=SU.group) β x y:=by
 let P:=W.joy n; rw [Wall.shine,Wall.shine,←W.rod, revoke,revoke]; change S.density (G:=SU.group) β (pull P.s ((assembly m).embed (K.embed P.b)) x) (pull _ _ _)=_; rw [show (assembly m).embed _= (ratio K).embed ((assembly n).embed P.b) from (reA K P).symm,←t]; exact S.channel p P.s ((assembly n).embed (W.joy n).b) β x y -- tune
lemma fields(β:ℝ) (x:Pane m): MeasurePreserving (W.shine n) (Ξ SU.group S β x) (Ξ SU.group S β ((Ω).shine m x)):=by
 let g:= W.shine n; let H:=Ξ SU.group S β; let P:=H x; let Q:=H ((Ω).shine m x); let h:= (W.trail n).measurable; refine ⟨h,?_⟩; haveI:IsProbabilityMeasure P:= paid p x; haveI:IsProbabilityMeasure Q:= paid p _; ext i v; rw [Measure.map_apply h v]
 have e(A:Set (Pane n))(z:Pane m)(t:MeasurableSet A) : (H z).real A= ∫ x',(S.density (G:=SU.group) β z x')*(A.indicator (fun _=> (1:ℝ)) x')∂ prior SU.group (More n):= by
   letI:IsProbabilityMeasure (H z):= paid p z; change _=∫ x',(S.density (G:=SU.group) β z x')• (A.indicator (fun _=> (1:ℝ)) x') ∂prior SU.group (More n); rw [←card p z,integral_indicator t,setIntegral_const,smul_eq_mul,mul_one] -- tune Π infer
 change P _=Q _; refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp ?_; rw [←measureReal_def,←measureReal_def]; unfold P Q; rw [e _ _ v,e _ _ (h v)]; let Y:= (Ω).shine m x; let f(y:Pane n):= S.density β Y y * (i.indicator (fun _=>(1:ℝ)) y); have hf:Measurable f:= ((S.isKernel p β).meas.comp measurable_prodMk_left).mul (measurable_const.indicator v)
 change _=∫ y,f y∂_; rw [←expect (W.shine n) (W.trail n) f hf]; exact integral_congr_ae (Eventually.of_forall fun y=> by dsimp only [f,Y]; rw [density W t p]; by_cases h:W.shine n y ∈ i <;> simp [h])
open AnalyticBridge.GaussianFieldAlignment
omit p t
lemma geo {n m:Side}(S:StepData n m)(s:Signed)(b:Site n): Injective (Locations.forest (S:=S) s b):=by
 intro i j t; apply Bough.S_ext S.ratio; intro x; obtain ⟨x,rfl⟩:=(StepData.sendSites s (S.ratio.embed b)).surjective x; let k:=affine s (S.ratio.embed b) x; let z:=i.up k; let p:=j.up k; have he:= congrArg (fun y:Forest S.ratio=>y.height x) t; have ht:= congrArg (fun y:Forest S.ratio=> y.up x) t; change z.rotate s⁻¹=p.rotate s⁻¹ at ht; refine Prod.ext ?_ he; have hg:= congrArg (Step.rotate · s) ht; change z=p; simpa only [Step.rotate_mul,mul_inv_cancel,Step.rotate_one] using hg
private lemma rosy{I:Ratio (More n) (More m)}(p:S.ratio=I)(s:Sweep n) : Injective (fun i: Forest I=>(p ▸ Locations.forest (S:=S) s.s ((assembly n).embed s.b) (p.symm ▸ i): Forest I)):=by subst I; apply geo
include t
lemma σF : Bijective (fun i:Forest (ratio K) => moveTree K S t i (W.joy n)):=by have he: Injective (fun i:Forest (ratio K) => moveTree K S t i (W.joy n)):= rosy t (W.joy n); exact ⟨he,Finite.injective_iff_surjective.mp he⟩
abbrev ζF := Equiv.ofBijective _ (σF W t)
lemma forest [Nonempty (Forest (ratio K))] : MeasurePreserving (ζF W t) (Bough.St (ratio K)) (Bough.St (ratio K)):= FD.Cash.pm_P _ _ (fun i=>rfl)
end Turn
end YM.CF.DPress.Chess.Transit
