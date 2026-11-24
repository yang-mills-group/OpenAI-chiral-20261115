import YM.SU5.Thin.Avalanche.MomentShift
import YM.SU5.Circuit.Quartet
/-!
# Under changing bodies

Use rotational trick (variant of Regis/Breeze) for a Wick recursion. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Regis.Resonance
open Function Filter Metric MeasureTheory ProbabilityTheory NormedSpace InnerProductSpace Finset
open scoped Topology BigOperators InnerProductSpace ENNReal NNReal Classical
variable {E: Type*}[NormedAddCommGroup E][InnerProductSpace ℝ E][MeasurableSpace E][BorelSpace E][FiniteDimensional ℝ E]
local notation "μ"=> stdGaussian E
local notation "φ"=>(μ).prod μ
local notation "ℭ"=> Valued μ
local notation "ℬ"=> Valued φ
abbrev spanX (x:E): E→ℝ:= inner ℝ x
abbrev east (f:E→ℝ): E×E→ℝ:= f ∘ Prod.fst
abbrev west (f:E→ℝ): E×E→ℝ:= f ∘ Prod.snd
lemma fromV (x:E): ℭ (spanX x):=⟨fun k=> IsGaussian.memLp_dual μ (toDual ℝ E x) k (by simp)⟩
lemma eastV (f:E→ℝ) (h:Valued μ f): ℬ (east f):= h.pulled (measurePreserving_fst ..)
lemma westV (f:E→ℝ) (h:Valued μ f): ℬ (west f):= h.pulled (measurePreserving_snd ..)
open ContinuousLinearMap (rotation)
abbrev cable (f:E×E→ℝ)(t:ℝ): E×E→ℝ:= f ∘ rotation t
lemma shift_zero (f:E×E→ℝ):cable f 0=f:=by ext; simp [cable,ContinuousLinearMap.rotation_apply]
private lemma buy_cos {f:E×E→ℝ}(h:Valued φ f): Beat φ (fun t=> Real.cos t • f) 0:=by simpa using Beat.oneB Real.cos _ (Real.hasDerivAt_cos 0) _ h
private lemma buy_sin {f:E×E→ℝ}(h:Valued φ f): Beat φ (fun t=> Real.sin t • f) f:=by simpa using Beat.oneB Real.sin _ (Real.hasDerivAt_sin 0) _ h
lemma east_sign (x:E) : Beat φ (cable (east (spanX x))) (west (spanX x)):= by
 let f:=spanX x; have p:=buy_cos (eastV f (fromV x)); have h:= Beat.two p (buy_sin (westV f (fromV x))); rw [zero_add] at h; convert h using 1; ext t z; simp [cable, ContinuousLinearMap.rotation_apply,east,west,f,spanX,inner_add_right,inner_smul_right]
lemma west_sign (x:E) : Beat φ (cable (west (spanX x))) (-(east (spanX x))):=by
 let f:=spanX x; have p:=buy_cos (westV f (fromV x)); have h:= Beat.two (Beat.neg (buy_sin (eastV f (fromV x)))) p; rw [add_zero] at h; convert h using 1; ext t z; simp [cable, ContinuousLinearMap.rotation_apply,east,west,f,spanX,inner_add_right,inner_smul_right]; -- linarith
lemma wire (f g:E×E→ℝ): cable (f*g)= cable f * cable g:=rfl
lemma profit (f g:E×E→ℝ)(h:Beat φ (cable f) g) : ∫ i,g i∂φ=0:= by
 have hb:= h.entry; have hp(t:ℝ):∫ i,cable f t i∂φ=∫ i,f i∂φ:=by
    have ht: Measure.map (rotation t) φ=φ:= IsGaussian.map_rotation_eq_self (by exact integral_id_stdGaussian) t; have hy:Integrable f (φ):= shift_zero f ▸ (h.label 0).1.accepted; have hu:AEStronglyMeasurable f (Measure.map (rotation t) φ):= by rw [ht]; exact hy.aestronglyMeasurable
    refine Eq.trans (integral_map (show AEMeasurable (rotation t) φ from by fun_prop) hu).symm ?_; rw [ht] -- parentheses ∫ i,f .. not (f (r..)).
 simp_rw [hp] at hb; exact hb.unique (hasDerivAt_const _ _)
variable (L:List E)
-- recurrence
abbrev payday (L:List E): E→ℝ:= (L.map spanX).prod
abbrev memo (L:List E):ℝ:= ∫ i,payday L i∂ μ
lemma payday_val: ℭ (payday L):=Valued.more _ fun i u=> by obtain ⟨j,g,rfl⟩:= List.mem_map.mp u; exact fromV j
def adder (L:List E):E×E→ℝ :=
 match L with
 | [] => 0
 | i::L=> east (spanX i)*adder L+west (spanX i) * east (payday L)
lemma momentum : Beat φ (cable (east (payday L))) (adder L):=by induction L with
 | nil=> rw [adder]; exact Beat.stand _ (eastV _ (payday_val [])) -- cable constant definitional
 | cons i L ih=>
    rw [adder]; change Beat φ (cable (east (spanX i)*east (payday L))) _;
    rw [wire]; have he:=Beat.mix (east_sign i) ih; rwa [shift_zero,shift_zero] at he
lemma integral_one_l (x:E→ℝ) : (∫ z, east x z ∂φ) = ∫ z,x z ∂μ:=by
 simpa [east,Function.comp_def] using integral_prod_mul («μ»:=μ) («ν»:=μ) x (fun _=>(1:ℝ))
-- gap fertility. fix recurrence using auxiliary L-left.
def roster (a:E)(M:List E)(L:List E):ℝ:=
 match L with
 | []=> 0
 | i::L=> inner ℝ a i * memo (M ++ L)+ roster a (M++[i]) L
local notation "Φ(f)"=> integral (φ) (f)
lemma sprue (a:E)(M:List E): (∫ x,(east (payday M)*west (spanX a)*adder L) x ∂φ) = roster a M L:=by
 induction L generalizing M with
 | nil=>simp [adder, roster]
 | cons i L ih=>
    let f(y):=spanX a y*spanX i y; let g:= east (payday (M ++ L)); let F:=east (payday M)*west (spanX a)
    have hp:east (payday M)*east (spanX i)=east (payday (M++[i])):=by unfold east payday; simp; rfl -- List.map etc
    have he:g=east (payday M)*east (payday L):=by unfold g east payday; simp; rfl -- ..
    have ht: F*adder (i::L)=(east (payday (M++[i]))*west (spanX a)*adder L)+g*west f:=by rw [adder]; unfold F; rw [he,←hp]; rw [show west f=west (spanX a)*west (spanX i) from rfl]; ring
    rw [show east _*west _*adder (i::L)= _ from ht]; simp_rw [Pi.add_apply]; rw [integral_add]
    · rw [ih]; have hf:(∫ x, (g*west f) x∂φ)= memo (M++L)*inner ℝ a i:=by
         rw [show inner ℝ a i=∫ x,f x∂μ from (Head.Brecht.appraisal a i).symm]; exact integral_prod_mul ..
      rw [hf,add_comm,mul_comm (memo (M++L)),roster]
    exacts [(((eastV _ (payday_val _)).times (westV _ (fromV a))).times ((momentum L).label 0).2).accepted, ((eastV _ (payday_val _)).times (westV _ ((fromV a).times (fromV i)))).accepted]
lemma gramStein (x:E) : memo (x::L)=roster x [] L:=by
 let f:=east (payday L); let g:=cable f; let h:=west (spanX x); let b:= h*f; let p:= east (payday (x::L)); have hz: Beat φ (cable b) (h*adder L-p):=by unfold b; rw [wire]; have ht:=Beat.mix (west_sign x) (momentum L); rw [shift_zero,shift_zero,neg_mul] at ht; exact ht
 have hp:=profit _ _ hz; simp_rw [Pi.sub_apply] at hp; rw [integral_sub ((westV _ (fromV x)).times ((momentum L).label 0).2 |>.accepted) ((eastV _ (payday_val _)).accepted)] at hp
 unfold memo; rw [←integral_one_l,← show _=∫ i,p i∂φ from sub_eq_zero.mp hp,← sprue (M:=[]) L x]; rw [show east (payday ([]:List E))=1 from rfl,one_mul] -- simp ∑1∙
end YM.Regis.Resonance
#print axioms YM.Regis.Resonance.gramStein
