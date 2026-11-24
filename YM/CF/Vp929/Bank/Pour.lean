import YM.CF.Vp929.Bank.Yard
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Plume.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Tarn Cay Slate Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Appel.Rate Lilt Girt
open scoped Topology ContDiff BigOperators InnerProductSpace NNReal ENNReal Classical
variable {N P B:Side} {S:StepData (Domain N B) (Domain P B)} {E:Type}
local notation "G₀"=> SU.group
local notation "Co"=> SU.group.Color
local notation "Fx"=> Domain P B
local notation "A_"=> Bond (Domain P B)
local notation "Ω"=> Cord S
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
variable (L:Support (Domain N B)) {h t b v a C:ℝ}
local notation "T" => booths L S
local notation "mu₀" => plummy S
abbrev grains (L:Support (Domain N B)) (F:SU.group.Color→ ℂ) (x:Cord S):=∏ i∈booths L S,F (x.2.1.2 i)
lemma grains_m (F:SU.group.Color→ ℂ) (h:Measurable F): Measurable (grains (S:=S) L F):= Finset.measurable_fun_prod _ fun i _=> h.comp ((measurable_pi_apply i).comp measurable_snd.fst.snd)
lemma grains_r (F:SU.group.Color→ ℂ)(x:Ω): grains L F (yearT x L)=grains L F x:=prod_congr rfl fun i h=> congrArg F (if_pos (mem_filter.mp h).2)
def pour (h:ℝ)(z:ℂ)(f:Ω→E):= ∫ x, grains L (flask G₀ h z) x • f x ∂plummy S h
variable (ht:0<t)(hp:0<h)
include ht hp
lemma pour_eq (z:ℂ)(f:Cord S→E) (hf:StronglyMeasurable f)(hx:∀ x:Ω, f x=f (yearT x L)): pour L h z f=(∫ x,(grains L (fun i=> flask G₀ h z i/(cupB t h i:ℂ)) x) • f x∂posed S t h):= by
 let g(x:Ω):= grains L (fun i=>flask G₀ h z i/(cupB t h i:ℂ)) x; have hg:Measurable g:= grains_m _ _ (by unfold flask cupX cupB Appel.Rate.cup;fun_prop); have hu(x: Co):0<cupB t h x:=cupB_pos ht hp x
 have hp':∀ x,f x=f (yearT x L):=hx; let F(x:Ω):=g x • f x; have hF: StronglyMeasurable F:=hg.stronglyMeasurable.smul hf; have he:= (cup_comp (G:=G₀) (t^2)).measurable.div_const (n_cup (G:=G₀) (t^2) h)
 haveI:=feast_nn G₀ hp; haveI:=pitched_p (G:=G₀) ht hp
 change _=(∫ i,F i∂yard S (fun _=> pitched G₀ t h)); rw [rotate (ν:=fun _=>feast G₀ h) _ L (fun i=> cupB t h) (fun i=> he) (fun i _ x=> (hu x).le) (fun i _=> pitcher_eq ht hp) F hF ?_]; unfold pour
 · refine integral_congr_ae (Eventually.of_forall fun x=>?_); dsimp only [F]; rw [RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]; apply congrArg (· • f x); unfold g grains; change _=(↑(∏ i∈T,cupB t h (x.2.1.2 i)):ℂ)*_; rw [Complex.ofReal_prod,←prod_mul_distrib]; refine prod_congr rfl fun i hv=>?_ ; field_simp [(Complex.ofReal_ne_zero.mpr (hu _).ne' : (cupB t h (x.2.1.2 i) : ℂ)≠0)]
 intro x; unfold F g; rw [grains_r ..]; exact congrArg _ (hx x)
lemma pour_real (f:Ω→E)(hf:StronglyMeasurable f)(hx:∀ x:Ω,f x=f (yearT x L)): pour L h (t^2:ℝ) f= ∫ x,f x∂posed S t h:=by
 rw [pour_eq L ht hp _ f hf hx]; refine integral_congr_ae (Eventually.of_forall fun i=> ?_); have P(x:SU.group.Color): flask G₀ h (t^2:ℝ) x/(cupB t h x:ℂ)=1:= by rw [flask,cupX_real,jug_real,cupB,Complex.ofReal_div]; exact div_self (Complex.ofReal_div _ _ ▸ Complex.ofReal_ne_zero.mpr (cupB_pos ht hp x).ne')
 simp only [grains,P,prod_const_one,one_smul]
lemma grains_cost(z:ℂ)(p:z.re=t^2)(s:‖jug G₀ h (t^2:ℝ)‖/‖jug G₀ h z‖ ≤ Real.exp b)(x:Ω): ‖grains L (fun i=>flask G₀ h z i/(cupB t h i:ℂ)) x‖ ≤ Real.exp ((T).card*b):= by
 unfold grains; rw [Complex.norm_prod,Real.exp_nat_mul]; refine le_trans (prod_le_prod (g:=fun _=> Real.exp b) (fun i _=>norm_nonneg _) fun i _=>(abs_cupB ht hp z p _).trans_le s) (le_of_eq (by simp))
omit ht hp
private theorem sf {G:Type} [MeasurableSpace G] (m:Measure G)[IsProbabilityMeasure m]: SFinite m:=by infer_instance
variable (u:ℝ)
lemma axis_cost_tail (H:Patron a C) (h:1≤v)(p:0≤u) :
    (mu₀ v).real {x|¬textP L x u} ≤ (T).card*(Real.exp (-a*u^2)*C) := by
 let mu:=plummy S v; let ϕ:= feast G₀ v; have hp:=zero_lt_one.trans_le h; haveI:IsProbabilityMeasure mu:= plum_p S hp; haveI:IsProbabilityMeasure ϕ:= feast_nn G₀ hp
 haveI:=Appel.how (α:=Bond Fx) G₀ hp; haveI:=feast_nn G₀ hp; haveI:IsProbabilityMeasure (suit S):=by unfold suit; infer_instance
 haveI:= lum_p S hp; haveI : SFinite (springT S v):=sf _
 let g (i:Bond Fx) (x:Cord S):=x.2.1.2 i; have e(i:Bond Fx): MeasurePreserving (g i) mu ϕ:= (measurePreserving_eval (fun _:Bond Fx=> feast G₀ v) i).comp ((measurePreserving_snd («μ»:=suit S)).comp ((measurePreserving_fst).comp measurePreserving_snd))
 let U(i:Bond Fx):=g i ⁻¹' (closedBall 0 u)ᶜ; rw [show {x:Ω|¬textP L x u}=⋃ i∈T,U i from by ext x; simp [textP,U,g,mem_closedBall_zero_iff,booths]]; refine (measureReal_biUnion_finset_le ..).trans ((sum_le_sum fun i _=>(show mu.real (U i)=ϕ.real (closedBall 0 u)ᶜ from ?_).trans_le (H.tail u p h)).trans (le_of_eq (by simp)))
 exact congrArg ENNReal.toReal ((e i).measure_preimage (isClosed_closedBall.measurableSet.compl.nullMeasurableSet))
/-- Larger hat representative law with density on inside characters, on the retained text set.
 For comparing the two real recipes at different Pilot cuts. -/
lemma pour_hat (hp:0<u)(p:u≤ v)(f:Ω→ E)(hf:StronglyMeasurable f)(hx:∀ x:Ω,f x=f (yearT x L)):
    (∫ x,f x ∂mu₀ u)=∫ x, (if textP L x u then (Appel.point G₀ v/Appel.point G₀ u)^(T).card • f x else (0:E))∂ mu₀ v:=by
 let A:= Appel.point G₀ v/Appel.point G₀ u; have ht:0 < A:= div_pos (point_p (hp.trans_le p)) (point_p hp)
 let D : Co→ℝ:= (closedBall 0 u).indicator fun _=> A; have e: Measurable D:= measurable_const.indicator isClosed_closedBall.measurableSet; have q(x:Co):0≤D x:=Set.indicator_nonneg (fun _ _=> ht.le) x
 have h:feast G₀ u=(feast G₀ v).withDensity (fun x=>ENNReal.ofReal (D x)):=by
   rw [show (fun x=>ENNReal.ofReal (D x))=(closedBall 0 u).indicator (fun _=>ENNReal.ofReal A) from ?_,withDensity_indicator isClosed_closedBall.measurableSet,withDensity_const]; exact feast_insideD p hp; funext x; by_cases e:x∈closedBall (0:Co) u<;> simp [D,e]
 haveI:=feast_nn G₀ hp; haveI:=feast_nn G₀ (hp.trans_le p); rw [show mu₀ u=yard S (fun i=> feast G₀ u) from rfl,rotate _ (fun i=> feast G₀ v) L (fun _=>D) (fun _=>e) (fun i _=>q) (fun _ _=>h) f hf hx]; refine integral_congr_ae (Eventually.of_forall fun i=>?_); dsimp only; split
 · rename_i t; rw [show (∏ j∈T, D (i.2.1.2 j))= A^(T).card from (prod_congr rfl (g:=fun _=>A) fun j v=> Set.indicator_of_mem (mem_closedBall_zero_iff.mpr (t j (mem_filter.mp v).2)) _).trans (by simp [booths])]
 rename_i t; unfold textP at t; push Not at t; obtain ⟨j,h,x⟩:=t; rw [Finset.prod_eq_zero (show j∈T from mem_filter.mpr ⟨mem_univ j,h⟩) (f:=fun j=> D (i.2.1.2 j)) (Set.indicator_of_notMem (mt mem_closedBall_zero_iff.mp x.not_ge) _),zero_smul]
end YM.CF.Plume.Rate
