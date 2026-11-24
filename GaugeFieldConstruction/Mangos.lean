import GaugeFieldConstruction.Herald
import YM.Extraction.Inherited

/-!
# Detection on the one-slot joint-angular-separated budget
-/
set_option autoImplicit false
set_option synthInstance.maxSize 5800
noncomputable section
namespace YM.GaugeFieldConstruction.Ember
open Calibration Raw Cauchy Row LabelAction Empire Fathom Payroll Function Filter Set TopologicalSpace Analysis MeasureTheory Points Bulb Palace Module Record
open scoped Topology BigOperators ContDiff
open Floor Wick Invoice Gap Metric Extraction
attribute [local instance] iG iF iX iU iT2 iW2 iV iS

-- prove Foil existence from plenum by nhds criterion & Ball
lemma bulging (x:E4) (V : Set E4) (h: V ∈𝓝 x): ∃ b : Bulb, Bulb.lit b x ∧ b.run ⊆ V:= by
  obtain ⟨r,hr,hR⟩:= Metric.mem_nhds_iff.mp h
  let B:ContDiffBump x:= ⟨r/3,r/2, by positivity,by linarith⟩
  refine ⟨⟨B,B.contDiff,B.hasCompactSupport⟩,B.eventuallyEq_one_of_mem_ball (mem_ball_self B.rIn_pos),?_⟩
  change tsupport B ⊆ _; rw [B.tsupport_eq]; exact Subset.trans (closedBall_subset_ball (show B.rOut < r by dsimp [B]; linarith)) hR
lemma locality {x : Points 2} (u : x∈generic 2):
    ∃ K : Set (Points 2), IsOpen K ∧ x∈K ∧ K⊆generic 2 ∧ ∀ t : Test 2, tsupport t⊆K→ ∃ b : Foil,b.p=t := by
  classical
  -- tensorized coordinate separation
  let Y:=fun (p : Points 2 × E4)=> ∀ i:Axis, p.1 0 i ≠ p.2 i
  have hu : ∀ᶠ p in 𝓝 (x,x front),Y p := by
    refine eventually_all.mpr (fun i=> (isOpen_ne_fun (f:=fun p:Points 2 × E4=> p.1 0 i) (g:=fun p=> p.2 i) (by fun_prop) (by fun_prop)).mem_nhds ?_)
    exact fun h=> (by decide : (0:Fin 2)≠front) (u i h)
  rw [nhds_prod_eq] at hu
  obtain ⟨s,hs,V,hV,F⟩:= Filter.mem_prod_iff.mp hu
  obtain ⟨a,ha,hA⟩:=bulging _ _ hV
  obtain ⟨b,hb,hB⟩:=bulging (x front) {z| a.lit z} ha.eventuallyEq_nhds
  obtain ⟨c,hc,hC⟩:=bulging (x front) {z| b.lit z} hb.eventuallyEq_nhds
  have hba : Before b a:= ⟨fun _ h=> hB h⟩
  have hcb : Before c b:=⟨fun _ h=> hC h⟩
  let H (u: Points 2) := u∈generic 2 ∧ u∈ s ∧ a.lit (u front) ∧ b.lit (u front) ∧ c.lit (u front)
  have ht (b:Bulb) (h:b.lit (x front)): ∀ᶠ p in 𝓝 x,b.lit (p front):=(loc front).continuous.continuousAt.tendsto h.eventuallyEq_nhds
  have hv : ∀ᶠ p in 𝓝 x,H p:= Eventually.and (p:=fun x=>x∈generic 2) ((genericOpen 2).mem_nhds u) (Eventually.and hs ((ht a ha).and ((ht b hb).and (ht c hc))))
  obtain ⟨U,hU,p,R⟩:= _root_.mem_nhds_iff.mp (show {p| H p} ∈ 𝓝 x from hv)
  refine ⟨U,p,R,fun i u=> (hU u : H i).1, fun t h=>?_⟩
  have E {i : Points 2} (p:i∈ tsupport t): H i:=hU (h p)
  have P x (r : x∈tsupport t) {i} (u:i∈a.run): Y (x,i) := F ⟨(E r).2.1, hA u⟩
  have D x (r : x∈ tsupport t):∀ j : Fin 2,j≠ front → x j∉ a.run:=by
    intro j w; have he:j=0:=by fin_cases j; rfl; exact (w rfl).elim
    intro hx; rw [he] at hx; exact (P x r hx 0 rfl)
  refine ⟨⟨t,(fun i r=>(E r).1),a,b,c,⟨fun x r=>(E r).2.2.1,D⟩,
    ⟨fun x r=>(E r).2.2.2.1,fun x r i q h=> D x r i q (surrounded (b:=a) (hB h))⟩,
    ⟨fun x r=>(E r).2.2.2.2, fun x r i q h=> D x r i q (surrounded (b:=a) (hB (surrounded (b:=b) (hC h))))⟩, hba,hcb, fun x r _ p i=> P x r p i⟩,rfl⟩ -- hcb order?

-- rewrite with free pairs
lemma vid {K : Points 2→ℂ} (h:ContinuousOn K (conf 2)) (v:∀ f:Foil,f.p.applyTo K=0) : EqOn K 0 (conf 2):= by
  apply Order.equal h continuousOn_const
  intro x w; obtain ⟨s,hs,t,u,r⟩:=locality w
  have ht:=Subset.trans u (generic_conf _)
  have hh:= h.mono ht
  have H:= hs.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ:=volume) (hh.locallyIntegrableOn hs.measurableSet)
  refine Measure.eqOn_open_of_ae_eq (μ:=volume) ((ae_restrict_iff' hs.measurableSet).mpr (H ?_)) hs hh continuousOn_const t
  intro f hf hp hu
  let g := Complex.ofRealCLM ∘ f
  have F: tsupport g⊆ tsupport f:= tsupport_comp_subset (map_zero Complex.ofRealCLM) f
  let q : Test 2:= ⟨g,Complex.ofRealCLM.contDiff.comp hf,hp.comp_left (map_zero Complex.ofRealCLM),(Subset.trans (F.trans hu) ht)⟩
  obtain ⟨p,he⟩:= r q (F.trans hu); rw [← v p, he]; exact integral_congr_ae (Eventually.of_forall fun x=> Complex.real_smul)

-- two-point free kernels as functions

def pr : Points 2 →L[ℝ] E4:= loc front - loc (0:Fin 2)
lemma pr_val (x): pr x=x front-x 0:= rfl
lemma pr_gap {i} (p:i∈conf 2): pr i≠0 := sub_ne_zero.mpr (fun t=> (by decide : front ≠0) (p t))

def pane (f : SmoothGap): Points 2→ℂ:= f.val ∘ pr
lemma pane_diff {x : Points 2} (f : SmoothGap) (h:x∈conf 2): ContDiffAt ℝ ∞ (pane f) x:= (healthy f (pr_gap h)).comp x pr.contDiff.contDiffAt
lemma natural (f : SmoothGap): ContinuousOn (pane f) (conf 2) := fun x u=> (pane_diff f u).continuousAt.continuousWithinAt
lemma pane_der (v : SmoothGap) (a): EqOn (D (direction front a) (pane v)) (pane (Gap.step a v)) (conf 2):= by
  intro x hx
  have e:=flash a v (pr_gap hx)
  have ht: pr (direction front a)=basis a:= by
    rw [pr_val]; simp only [direction,PiLp.single_eq_same,PiLp.single_eq_of_ne _ (by decide : (0:Fin 2) ≠front),sub_zero] -- check
  change _ = (Gap.step _ _).val _; rw [e]; unfold pane D; rw [fderiv_comp _ ((healthy _ (pr_gap hx)).differentiableAt (by simp)) pr.differentiableAt,ContinuousLinearMap.fderiv,ContinuousLinearMap.comp_apply,ht]; rfl

def shown (v : SmoothGap): Bond 2:= (TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul ℂ ℂ) volume (pane v)).toLinearMap
lemma posts (v : SmoothGap) (p : Test 2) : shown v p=p.applyTo (pane v) := by
  change TestFunction.integralAgainstBilinCLM _ _ _ p=_
  rw [TestFunction.integralAgainstBilinCLM_eq_integral (show LocallyIntegrableOn _ ((patch 2):Set (Points 2)) volume from (natural v).locallyIntegrableOn (conf_open 2).measurableSet)]; rfl
lemma floats (v : SmoothGap) (p : Foil): shown v p.p=p.p.applyTo (pane v) := posts ..
lemma empt {v} (p:∀ f : Foil,shown v f.p=0): v=0 := by
  have ht:=vid (natural v) (fun f=> (floats v f).symm.trans (p f))
  apply Gap.eyes; intro z hz
  rw [map_zero]; let x:=points (![0,z]:Fin 2→E4)
  have hp: x∈conf 2:= by intro i j e; fin_cases i <;> fin_cases j <;> first| rfl| exact (hz e).elim| exact (hz e.symm).elim
  have hv: pr x=z:=sub_zero _
  have he: v.val (pr x)=0:= ht hp; rwa [hv] at he

def boast : SmoothGap→ₗ[ℂ] Bond 2 where
  toFun:=shown
  map_add' v w:= by
    ext1 x
    rw [posts, LinearMap.add_apply,posts,posts]; unfold Test.applyTo
    rw [← integral_add (Test.smearing x (natural v)) (Test.smearing x (natural w))]; exact integral_congr_ae (Eventually.of_forall fun y=> mul_add ..)
  map_smul' c w:= by
    ext1 x
    change shown (c • w) x=c * shown w x; rw [posts,posts]; unfold Test.applyTo; rw [← integral_const_mul]; exact integral_congr_ae (Eventually.of_forall fun y=> mul_left_comm ..)
lemma point_der (w:SmoothGap) (i) : paid front i (boast w)=boast (Gap.step i w):= by
  ext1 p; rw [pays]
  change -shown w _=shown _ p
  rw [posts,posts,← Test.apply_eq p (pane_der w i)]; unfold Test.applyTo; rw [tilt_pays]
  have H := Test.smearing (tilt (direction front i) p) (natural w); simp_rw [tilt_pays] at H
  have V :ContinuousOn (D (direction front i) (pane w)) (conf 2):= (natural (Gap.step i w)).congr (pane_der w i)
  exact Eq.symm (integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable H (Test.smearing p V) (Test.smearing p (natural w))
    (fun x _=> diffT p x) fun x h=> (pane_diff w (p.tsupport_subset h)).differentiableAt (by simp))

-- feel free field probes

def script (b: UV five) : Shell →ₗ[ℂ] Bond 2 := boast ∘ₗ Invoice.paper.flip b
abbrev silky (b: UV five): UV five→ₗ[ℂ] Bond 2:=script b ∘ₗ shells five
lemma quote (b) (f): script b f=boast (Invoice.paper f b):= rfl
lemma clear_l (w) (b:UV five) (i): paid front i (script b w)=script b (P i w):=by rw [quote,point_der,quote, show paper (P i w) b=Gap.step i (paper w b) from right_leg ..]
lemma clear_point (w b i): paid front i (silky b (Calibration.lift four w))=silky b (Calibration.deriv i w):= by rw [LinearMap.comp_apply,LinearMap.comp_apply, clear_l]; rw [show shells five (Calibration.lift four w)=shells four w from LinearMap.congr_fun (shell_lift four) w]; exact congr_arg (script b) (Eq.symm (LinearMap.congr_fun (scene i) w))
lemma nullB {w} (v : ∀ b (j:Foil),script b w j.p=0):paper w=0 := by
  apply LinearMap.ext; intro b; exact empt (v b)
lemma dollarB {w} (v : ∀ b (j:Foil), silky b w j.p=0):w=0 := select.mp (nullB v)
end YM.GaugeFieldConstruction.Ember
