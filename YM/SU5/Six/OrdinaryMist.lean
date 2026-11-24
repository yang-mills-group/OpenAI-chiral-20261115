import YM.SU5.Six.MacroGrid
import YM.SU5.Aria.Dyad
set_option autoImplicit false
noncomputable section
namespace YM
open Function Set Filter Metric MeasureTheory
open scoped Topology NNReal ENNReal Classical BigOperators
open CF.Buffered.Afterglow.Tower.Aria (Mist)
namespace MacroGrid
/-!
# Spatial projection by ORDINARY pose smearing

For Vantage→ColorHil z continuous with compact support. The readings need not
be continuous under extrapolating mesh values from the *raw* unprojected
translations, but the character has a single Ellis sequence on all the axes.
We use the Mist to approximate trading a near-zero displacement in an ordinary
(grid weighted) quadrature; we *don't* insert the Mist into the measured
prices. Unlike using a continuous partition, the approximation is measured
in L¹ of ALL pose variables simultaneously by the vector DCT price.
-/
variable {I:Type}[Fintype I]
local notation "R" => I→ℝ
local notation "Λ"=> I→ℤ
local notation "μ"=> (volume : Measure (I→ℝ))
section floor
variable (H:Hilbert)(f g:(I→ℝ)→H)(x:I→ℝ)(U:(I→ℤ)→H.Op)(h:ℝ)(p:0<h)(B:HasCompactSupport f)
def poseApprox (H:Hilbert)(f:(I→ℝ)→H)(U:(I→ℤ)→H.Op)(h:ℝ) : H:= ∫ x:I→ℝ,floorCost h (fun k=>U k (f (atTick h k))) x
local notation "X"=> floorTicks h
local notation "φ"=> atTick (I:=I) h
include B p
lemma floor_pay : Integrable (floorCost (I:=I) h (fun k=> U k (f (atTick h k)))) μ := by
 apply floors_integrable h p; refine (finite_ledger h p (tsupport f) B).subset fun i u=>subset_closure ?_
 intro g; exact u ((congrArg (fun x:H=>U i x) (show f (atTick h i)=0 from g)).trans (map_zero (U i)))
lemma floor_bound (b:HasCompactSupport g)(e:∀ k x,‖U k x‖= ‖x‖):
  dist (poseApprox H f U h) (poseApprox H g U h) ≤ ∫ x:I→ℝ, ‖f (φ (X x))-g (φ (X x))‖:= by
 rw [poseApprox,poseApprox,dist_eq_norm,← integral_sub (floor_pay H f U h p B) (floor_pay H g U h p b)]; apply norm_integral_le_integral_norm ..|>.trans_eq
 unfold floorCost; simp_rw [← map_sub,e]
lemma floor_plus (b:HasCompactSupport g) : poseApprox H (f+g) U h= poseApprox H f U h+poseApprox H g U h:=by
 rw [poseApprox,poseApprox,poseApprox, ← integral_add (floor_pay H f U h p B) (floor_pay H g U h p b)]; unfold floorCost; simp_rw [Pi.add_apply,map_add]
omit B p in
lemma floor_scale (c:ℂ) : poseApprox H (c • f) U h=c • poseApprox H f U h:=by
 unfold poseApprox floorCost; simp_rw [Pi.smul_apply,map_smul]; rw [integral_smul]
omit B p
lemma relabel (k:Λ) (s:0<h): X (φ k+x)=k+X x:=by
 funext i; change ⌊(atTick h k i+x i)/h⌋=k i+⌊x i/h⌋; unfold atTick; rw [add_div,mul_div_cancel_right₀ _ (ne_of_gt s),add_comm _ (_/_), Int.floor_add_intCast, add_comm]
local notation "Μ"=> floorCost (I:=I)
def afterShift(k:R)(f:(R)→H): (R)→H:= f ∘ (fun x=> -k+x)
include p
lemma floor_shift (k:Λ)(V:H.Op) (v:∀ j, U (k+j)=(U j).comp V) :
    poseApprox H (V ∘ f) U h=poseApprox H (afterShift H (φ k) f) U h:= by -- arg order shadow
 unfold poseApprox
 let F:= fun x:I→ℝ=> floorCost h (fun i:I→ℤ=> U i (afterShift H (atTick h k) f (atTick h i))) x
 rw [←integral_add_left_eq_self («μ» :=volume) (f:=F) (atTick h k)] -- match pattern maybe eta
 refine integral_congr_ae (Eventually.of_forall fun x=>?_)
 unfold F floorCost; dsimp only [Function.comp_apply]; rw [relabel x h k p,v (floorTicks h x),tick_add,afterShift,Function.comp_apply]
 rw [show -φ k+(φ k+φ (floorTicks h x))=φ (floorTicks h x) from by abel]; rfl
end floor

section translates
variable (H:Hilbert)(f:(I→ℝ)→H)(u:Continuous f)(v:HasCompactSupport f)
include v
lemma compact_after (p:R): HasCompactSupport (afterShift H p f):= v.comp_homeomorph (Homeomorph.addLeft (-p))
local notation "L" p:max x:max=> ‖(afterShift H p f - f) x‖
omit v
include u
lemma continuous_L (p:R): Continuous (fun x=> L p x):= (((u.comp (continuous_const.add continuous_id)).sub u).norm) -- synt
include v
lemma shift_integral : Tendsto (fun p=> ∫ x,L p x ∂μ) (𝓝 (0:R)) (𝓝 0):= by
 obtain ⟨C,c,h⟩:= v.exists_pos_le_norm
 obtain ⟨B,e⟩:= u.bounded_above_of_compact_support v
 let X:= Metric.closedBall (0:R) (C+1)
 let T:=X.indicator (fun _=>2*B)
 let g(p x:R):= L p x
 have ht: Tendsto (fun p:R=> ∫ x,g p x∂μ) (𝓝 (0:R)) (𝓝 (∫ x:R, g 0 x∂μ)):= by
   refine tendsto_integral_filter_of_dominated_convergence T (Eventually.of_forall fun p=> (continuous_L H f u p).aestronglyMeasurable) ?_ ((integrable_indicator_iff isClosed_closedBall.measurableSet).2 (integrableOn_const (isCompact_closedBall .. |>.measure_ne_top))) ?_
   · filter_upwards [ball_mem_nhds (0:R) (show 0<(1:ℝ) by norm_num)] with i e'
     apply ae_of_all
     intro x; by_cases p:x∈X
     · rw [show T x= 2*B from indicator_of_mem p _, Real.norm_eq_abs, abs_of_nonneg (show 0≤g i x from norm_nonneg _)]
       exact (norm_sub_le ..|>.trans (add_le_add (e (-i+x)) (e x))).trans_eq (by ring)
     have hr : C+1 < ‖x‖ := by simpa [X,Metric.mem_closedBall,dist_zero_right] using p
     have hx: f (-i+x)=0:= h _ (by
        have ht:‖x‖≤‖i‖+‖-i+x‖:= by nth_rw 1 [show x=i+(-i+x) by abel]; exact norm_add_le ..
        have hp: ‖i‖≤1:= by rw [Metric.mem_ball,dist_zero_right] at e'; exact e'.le
        linarith)
     rw [show g i x=0 from (congrArg norm (show f (-i+x)-f x=0 from by rw [hx,h x (by linarith),sub_self])).trans norm_zero,norm_zero,show T x=0 from Set.indicator_of_notMem p _]
   apply ae_of_all
   intro i; exact Continuous.tendsto (f:=fun p=> g p i) (by unfold g afterShift; change Continuous fun p:R=> ‖f (-p+i)-f i‖; fun_prop) _
 rw [show (∫ x,g 0 x∂μ)=0 by unfold g afterShift; simp] at ht; exact ht
end translates

variable {G:Type}[AddCommGroup G](H H':Hilbert)
variable (e:H' →L[ℂ] H) (π' : H→L[ℂ] H') (η: G→(I→ℝ)) (F:G→H.Op) (W:(I→ℝ)→ H'.Op)
    (Δ:ℕ→(I→ℤ)→G)(h:ℕ→ℝ)(p:∀ i, 0<h i)(t:Tendsto h atTop (𝓝 0))
    (d:∀ i k, η (Δ i k)=atTick (h i) k)(c:∀ i a b,Δ i (a+b)=Δ i a+Δ i b)
    (s:∀ g,∀ᶠ i in atTop, ∃ k, Δ i k=g) (U:∀ a b:G,F (a+b)=(F a).comp (F b)) (u:∀ i x,‖F i x‖=‖x‖)
    (v:∀ x:H',Continuous (fun p=> W p x)) (E:∀ (g:G) (a:H'), F g (e a)=e (W (η g) a)) -- need joint W, norm
    (℘: Continuous (fun p : (I→ℝ)×H'=> W p.1 p.2))
-- op norm domination for shaking and event
variable (J:ℕ→Mist G)(p₀:∀ X∈𝓝 (0:I→ℝ),∀ᶠ n in atTop,(J n).holds (fun i=>η i∈ X))
    (w:∀ x:H, Tendsto (fun n=>(J n).mean (fun g=>F g x)) atTop (𝓝 (e (π' x))))
variable (g : (I→ℝ)→ H)(b:HasCompactSupport g)(q:Continuous g)
private def mistPrice (D:Mist G): H.Op := D.mean F
private lemma mist_here (D:Mist G)(x:H): mistPrice H F D x=D.mean (fun i=> F i x):= (D.mean_linear' F (ContinuousLinearMap.apply ℂ H.space x)).symm -- namespace import
include b p
private lemma mixes (i:ℕ)(D:Mist G): D.mean (fun a=>poseApprox H (F a ∘ g) (F ∘ Δ i) (h i))=
    poseApprox H (mistPrice H F D ∘ g) (F ∘ Δ i) (h i):=by
 induction D with
 | point a=> rfl
 | midP A B l x=>
    let a':= mistPrice H F A; let b':=mistPrice H F B
    let cA:= a' ∘g; let cB:=b' ∘g
    have he : mistPrice H F (.midP A B) ∘ g = (1/2:ℂ) • (cA+cB):=rfl
    rw [he,floor_scale,floor_plus H cA cB _ _ (p i) (b.comp_left (map_zero a')) (b.comp_left (map_zero b')),Mist.mean, l,x]
omit b p
local notation "A" X:max i:max=>poseApprox H X (F ∘ Δ i) (h i)
include π' w q b t p d c u p₀ U s
private lemma wash (ε:ℝ)(o:0<ε):∀ᶠ i in atTop,dist (poseApprox H g (F ∘ Δ i) (h i)) (poseApprox H ((e ∘ π') ∘ g) (F ∘ Δ i) (h i)) < ε:=by
  let V(x:I→ℝ):= e (π' (g x)); let P(i):= mistPrice H F (J i) ∘ g
  have ht:HasCompactSupport V:= (b.comp_left (map_zero π')).comp_left (map_zero e)
  have hp:Continuous V:= e.continuous.comp (π'.continuous.comp q)
  have hP(i):HasCompactSupport (P i):=b.comp_left (map_zero _)
  have hq(i):Continuous (P i):=(mistPrice H F (J i)).continuous.comp q
  have he:Tendsto (fun i=> ∫ x:R, ‖P i x-V x‖) atTop (𝓝 0):= by
    have y:‖e.comp π'‖≥0:= norm_nonneg _
    let D(x:R):= (‖e.comp π'‖+1)*‖g x‖
    have e':Tendsto _ _ (𝓝 (∫ _:R,(0:ℝ))) := tendsto_integral_filter_of_dominated_convergence (F:=fun i:ℕ=> fun x:R=>‖P i x-V x‖) D
      (Eventually.of_forall fun i=> ((hq i|>.sub hp).norm.aestronglyMeasurable)) (Eventually.of_forall fun i=> ae_of_all _ (fun x=>by
        have hy:‖P i x‖ ≤ ‖g x‖:= by change ‖mistPrice H F (J i) (g x)‖ ≤_; rw [mist_here]; apply Mist.mean_budget; exact (J i).solves _ fun a=> (u a _).le
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        have hv: ‖V x‖≤‖e.comp π'‖*‖g x‖:=(e.comp π').le_opNorm _
        exact (norm_sub_le ..|>.trans (add_le_add hy hv)).trans_eq (by unfold D; ring))) ((q.integrable_of_hasCompactSupport b («μ» :=μ)).norm.const_mul _) (ae_of_all _ (fun x=>by
          have hv:Tendsto (fun i=> P i x) atTop (𝓝 (V x)):= (w (g x)).congr fun i=> (mist_here ..).symm
          simpa only [sub_self,norm_zero] using (hv.sub_const (V x)).norm))
    simpa only [integral_zero] using e'
  obtain ⟨m,G₀,Q⟩:= ((he.eventually (gt_mem_nhds (show 0<ε/2 from half_pos o))).and (p₀ _ ((shift_integral H g q b).eventually (gt_mem_nhds (show 0< ε/2 from half_pos o))))).exists
  let D:= J m
  have hz(W:(R)→ H) (f:HasCompactSupport W)(v:Continuous W)(X:(R)→H)(q:Continuous X)(l:HasCompactSupport X)(d:(∫ x:R, ‖W x-X x‖)<ε/2):
      ∀ᶠ i in atTop, dist (poseApprox H W (F∘Δ i) (h i)) (poseApprox H X (F∘Δ i) (h i))<ε/2:= by
    have ht:Tendsto (fun i=>∫ x:R, ‖(W-X) (atTick (h i) (floorTicks (h i) x))‖) atTop (𝓝 (∫ x:R, ‖W x-X x‖)):= rSum_limit h t _ (v.sub q|>.norm) p ((f.sub l).norm)
    filter_upwards [ht.eventually (gt_mem_nhds d)] with i e
    exact lt_of_le_of_lt (floor_bound H _ _ _ (h i) (p i) f l (fun i' x=> u _ x)) e
  have hy(a:G)(p':D.reaches a): ∀ᶠ i in atTop, dist (poseApprox H (F a ∘ g) (F ∘ Δ i) (h i)) (poseApprox H g (F ∘ Δ i) (h i))≤ ε/2:= by
     have hu: (∫ x:R, ‖afterShift H (η a) g x-g x‖)<ε/2:= Mist.holds_at D|>.1 Q a p' -- might syntax
     have hx:Continuous (afterShift H (η a) g):= q.comp (continuous_const.add continuous_id)
     filter_upwards [s a, hz (afterShift H (η a) g) (compact_after H g b _) hx g q b hu] with i vo t
     obtain ⟨k,gk⟩:= vo; rw [floor_shift H g _ (h i) (p i) k _ (fun j=>show F (Δ i (k+j))=(F (Δ i j)).comp (F a) from by rw [add_comm k,c,gk,U]), ←d, gk]
     exact t.le
  filter_upwards [hz (P m) (hP m) (hq m) V hp ht G₀, (D.hasReach.eventually_all).mpr hy] with i z d
  have h₁:dist (poseApprox H (P m) (F∘Δ i) (h i)) (poseApprox H g (F∘Δ i) (h i))≤ε/2:= by
     rw [show P m=mistPrice H F D ∘g from rfl,← mixes H F Δ h p g b]
     exact D.ceiling _ _ _ (Mist.holds_at D|>.2 d) -- tune
  rw [dist_comm] at h₁
  exact (dist_triangle _ (poseApprox H (P m) (F∘Δ i) (h i)) _).trans_lt (add_halves ε ▸ add_lt_add_of_le_of_lt h₁ z)
omit π' w q b t p d c u p₀ U s
include π' w q b t p d c u p₀ U s E ℘
lemma pays_projection : Tendsto (fun i=>poseApprox H g (F ∘ Δ i) (h i)) atTop (𝓝 (e (∫ x:R,W x (π' (g x))))) := by -- edit
  let y(x:R):= W x (π' (g x)); let z(x:R):=e (y x)
  have ht: Continuous y:= ℘.comp (continuous_id.prodMk (π'.continuous.comp q))
  have hf: HasCompactSupport y:= b.mono (fun x (t:y x≠0) v=> t (by change W x (π' (g x))=_; rw [show g x=0 from v,map_zero,map_zero]))
  have hv: Tendsto _ _ (𝓝 (∫ x,z x ∂μ)):= rSum_limit h t z (e.continuous.comp ht) p (hf.comp_left (map_zero e))
  rw [show (∫ x,z x∂μ)=e (∫ x:R,y x) from ((e.restrictScalars ℝ).integral_comp_comm (ht.integrable_of_hasCompactSupport («μ» :=μ) hf))] at hv -- syntax order
  let L:=fun x:R=>e (π' (g x)); let T(i):=poseApprox H L (F ∘ Δ i) (h i)
  have hT:Tendsto T atTop (𝓝 (e (∫ x:R,y x))):= hv.congr fun i=>by
    unfold T poseApprox floorCost; apply integral_congr_ae (Eventually.of_forall fun x=>?_); unfold z y; dsimp only [L,Function.comp_apply]; rw [← d]; exact (E (Δ i _) _).symm -- rw replaces g_poses too; adjust
  refine (tendsto_iff_of_dist ?_).2 hT; apply Metric.tendsto_nhds.mpr; intro ε o; simp only [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg]
  exact wash H H' e π' η F Δ h p t d c s U u J p₀ w g b q ε o
end MacroGrid
end YM
