import YM.SU5.FiniteGaugeData.Galope.Chic
import YM.SU5.FiniteGaugeData.Steam.Hearth
/-! # Upper gauge pressure rate, plus allowance on number of failures.
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 20000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Galope
open Function Finset Filter MeasureTheory Matrix Lattice Wilson RG Next.Rank Spindle Next.SectorChange Wrist Lantern Lantern.Cup RouteM Recruit Cold
open Pressure Precision Laurent Bloch Rally Drachma.Tame Drachma.Tokens Poeme Haute
open CF.Window.Steve
open scoped Topology InnerProductSpace Matrix ContDiff BigOperators Classical Kronecker Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge} {s:Stage}{R:PathData G}{P:Bed}{M k w v:ℕ}{A:Finset (Cell n)}{Z:Finset (Site n)}{o:Site n}{γ C r x Λ α η τ μ a h ε β t:ℝ}{J:ChartRatio G}
namespace Sage
open Avenue
-- specialized to exact t threshold
variable {p:BudgetPoint}
lemma commit {A:Finset (Cell n)} (u:Config G n): misses u t=A ↔ ∀ i:Cell n,i∈A ↔ t<G.chord (faceValue u i):=by
 rw [Finset.ext_iff]; simp only [misses,mem_filter,mem_univ,true_and]; apply forall_congr'; intro x; exact Iff.comm
abbrev closedM (G:Gauge)(t:ℝ)(A:Finset (Cell n)):= {u:Config G n| misses u t=A} -- despite name, only measurable
lemma green(t:ℝ)(A:Finset (Cell n)): MeasurableSet (closedM G t A):=by
 unfold closedM; simp_rw [commit,Set.setOf_forall]; apply MeasurableSet.iInter; intro i
 by_cases h:i∈A
 · simp only [h,true_iff]; exact (isOpen_lt continuous_const (show Continuous (fun U:Config G n=> G.chord (faceValue U i)) by unfold faceValue; fun_prop)).measurableSet
 simp only [h,false_iff, not_lt]; apply IsClosed.measurableSet; exact isClosed_le (by unfold faceValue; fun_prop) continuous_const
variable {e:Config G n→ℝ}
def grains (e:Config G n→ℝ)(A:Finset (Cell n))(t:ℝ): Config G n →ℝ:= (closedM G t A).indicator e
lemma protectedA (A:Finset (Cell n))(t:ℝ)(h:Envelope e): Envelope (grains e A t):=by unfold grains Set.indicator; letI := Classical.decPred (fun x=> x∈closedM G t A); exact Envelope.piece (green t A) h (Envelope.const _)
abbrev tribute (t:ℝ) (p:BudgetPoint)(x:Config G n):ℝ:= (misses x p.threshold).card*t
-- uses univ.powerset (vs Finset.univ card). tune.
lemma eats(t:ℝ)(p:BudgetPoint)(e:Config G n→ℝ) : (fun x:Config G n=> Real.exp (tribute t p x)*e x) = fun x=> ∑ A: Finset (Cell n), Real.exp (A.card*t)*(grains e A p.threshold x):=by
 funext i; let c:= misses i p.threshold; rw [sum_eq_single c]; swap; · intro j hj t'; simp only [grains,Set.indicator_of_notMem (show i∉closedM G p.threshold j from Ne.symm t'),mul_zero]
 · unfold grains; rw [Set.indicator_of_mem (show i∈closedM G p.threshold c from rfl)] -- tune
 simp
lemma covering (p:BudgetPoint)(t:ℝ)(h:Envelope e): Envelope (fun x:Config G n=> Real.exp (tribute t p x)*e x):= by
 rw [eats]; exact Envelope.sum _ _ (fun i=> (Envelope.const _).mul (protectedA i p.threshold h))
lemma logply(s:Stage)(p:BudgetPoint)(β:ℝ)(W:R.Bounds s.clip s.width s.paths Λ)(A:Finset (Cell n)) : Envelope (grains (fun V:Config G n=>Real.exp (-(R.principal s.clip p β V))) A p.threshold):= protectedA A p.threshold ((PathData.principal_env W p β).neg.exp) -- tune
-- factor horizon growth independent size
lemma authorize (F:Arms G s)(Y:LocalRatio J)(Pmax:ℝ)(Hb:0≤Λ)(e:0<ε): ∀ᶠ x in atTop, ∀ β:ℝ,x/2≤β → β≤2*x →∀ p:BudgetPoint,p.threshold=temp x →∀ (n:Side),Intro n (radiusB x) →∀ (P:Bed)(a:ℝ),Floor P s.clip n a Pmax → 0<a →∀ R:PathData G, R.Bounds s.clip s.width s.paths Λ→ Attached P R → ∀ A:Finset (Cell n),
 (∫ U:Config G n, grains (fun V:Config G n=> Real.exp (-R.principal s.clip p β V)) A p.threshold U∂prior G n) ≤ Real.exp (angular n J P β + ε * ser n-A.card*(bonusK p s β* (3/4))) :=by
 let u:= ε/8; have hu:0<u:=div_pos e (by norm_num); obtain ⟨μ,hμ,α,hα,h',w'⟩:=resonant u hu G; obtain ⟨H,h,b⟩:=committed Y Pmax
 have hw:Tendsto (fun x:ℝ=> diamC*H/radiusB x) atTop (𝓝 0):= tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp Work.E01.radiusB_tendsto)
 filter_upwards [eventually_gt_atTop (0:ℝ),attainer F Y hμ hα h',great_pos F Hb hα hu,hw.eventually (ge_mem_nhds hu),b,posterior s H h] with x hx hy pz w hB v β p₀ p1 p hz n u' P a q m R W hW A
 obtain ⟨v',hK⟩:=hy β p₀ p hz n u'; let k:=coreN (radiusB x); let T:=glow A (lic (radiusB x)); let f:=grains (fun V:Config G n=> Real.exp (-R.principal s.clip p β V)) A p.threshold; apply silo (I:=buy T k) f _ (logply s p β W A); intro O
 let τ:=bonusK p s β; have hp:= (only_pays O P v' (le_refl T) q m W hW f (logply s p β W A) (fun U V=> ?_)); swap -- nested holes
 · by_cases h:misses U p.threshold=A; · exact ⟨(commit U).mp h, (Set.indicator_of_mem (show U∈closedM _ p.threshold A from h) _).le⟩
   exact False.elim (V (Set.indicator_of_notMem (show U∉closedM _ p.threshold A from h) _))
 apply hp.trans; refine (fee_cost A v' q m hK hu h (show Real.log μ- _≤u from (by linarith only [w',hu])) (hB β p₀ p1) u').trans (Real.exp_monotone ?_)
 have he:0 ≤ ser n:=Nat.cast_nonneg _; have hL:=bonus_fit s x hx p hz p₀; unfold u at *; linarith only [pz β p₀ p1 p hz n,mul_le_mul_of_nonneg_right w he, mul_le_mul_of_nonneg_left (le_trans v (div_le_div_of_nonneg_right hL (by norm_num))) (Nat.cast_nonneg (α:=ℝ) A.card), mul_nonneg e.le he]
private lemma tax_faces (Z:ℝ): ∑ i:Finset (Cell n), Real.exp (i.card*Z) ≤ Real.exp ((ser n) * Fintype.card PlaqAxes * Real.exp Z):=by
 have he(x:Finset (Cell n)): Real.exp (x.card*Z)=∏ i∈x,Real.exp Z:=by rw [Real.exp_nat_mul,prod_const]; -- tune
 have hp : ∑ i:Finset (Cell n), Real.exp (i.card*Z)=∏ i:Cell n,(Real.exp Z+1):=by simp_rw [he]; rw [Finset.prod_add_one]; congr
 rw [hp]; calc
    _ ≤ ∏ i:Cell n,Real.exp (Real.exp Z):= prod_le_prod (fun _ _=>by positivity) (fun _ _=>Real.add_one_le_exp _)
    _ = _:= by rw [← Real.exp_sum, sum_const,card_univ,Fintype.card_prod,nsmul_eq_mul]; unfold ser; push_cast; rfl
lemma monetize (h:LocalRatio J)(F:Arms G s)(Pmax:ℝ)(b:0≤Λ)(e:0<ε): ∀ᶠ x in atTop, ∀ β:ℝ,x/2≤β → β≤2*x →∀ p:BudgetPoint,p.threshold=temp x →∀ (n:Side),Intro n (radiusB x) →∀ (P:Bed)(a:ℝ),Floor P s.clip n a Pmax → 0<a →∀ R:PathData G, R.Bounds s.clip s.width s.paths Λ→ Attached P R → ∀ η:ℝ,η ≤ bonusK p s β /2 → (∫ U:Config G n, Real.exp (tribute η p U) * Real.exp (-R.principal s.clip p β U) ∂prior G n) ≤ Real.exp (angular n J P β + ε * ser n):=by
 let u:= ε/2; have hu:0<u:=half_pos e; have hz:Tendsto (fun x => (Fintype.card PlaqAxes:ℝ) * Real.exp (-(frostM s x/4))) atTop (𝓝 0):=by
    have hr:= (frost_t s).atTop_div_const (r:=4) (by norm_num); simpa only [mul_zero] using! (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hr)).const_mul (Fintype.card PlaqAxes:ℝ) -- tune
 filter_upwards [eventually_gt_atTop (0:ℝ),authorize F h Pmax b hu,hz.eventually (ge_mem_nhds hu)] with x pₓ y v β p0 q0 p he n z P a hc c R W ha η hp
 let e(V:Config G n):=Real.exp (-R.principal s.clip p β V); let ν:= prior G n; let r:= Real.exp (angular n J P β + u*ser n); let k:=bonusK p s β; let K:= -(frostM s x/4)
 change (∫ U:Config G n, (fun X=>Real.exp (tribute η p X)*e X) U∂ν)≤_
 rw [eats η p e, integral_finsetSum]; swap; · intro i v; exact ((logply s p β W i).integrable _).const_mul _ -- tune
 simp_rw [integral_const_mul]; have hm (A: Finset (Cell n)): Real.exp (A.card*η) * (∫ i,grains e A p.threshold i ∂ν) ≤ r*Real.exp (A.card*K):=by
    apply (_root_.mul_le_mul_of_nonneg_left (y β p0 q0 p he n z P a hc c R W ha A) (Real.exp_pos _).le).trans; unfold r; rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone
    have hg : η -bonusK p s β*(3/4) ≤ K := by unfold K; linarith only [bonus_fit s x pₓ p he p0,hp]
    linarith only [mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (α:=ℝ) A.card)]
 refine (sum_le_sum (fun i _=> hm i)).trans ?_; rw [← mul_sum]; apply (_root_.mul_le_mul_of_nonneg_left (tax_faces K) (Real.exp_pos _).le).trans; rw [←Real.exp_add]; apply Real.exp_monotone
 unfold u; unfold u at v; linarith only [mul_le_mul_of_nonneg_left v (Nat.cast_nonneg (α:=ℝ) (Fintype.card (Site n)))]
-- Return to actual physical gauges. Full channels & bonus invariant on THIS observation..
def colored (s:Stage)(P:PathData G)(η β:ℝ)(p:BudgetPoint)(V:Config G n):ℝ:= Real.exp (tribute η p V) *Real.exp (-P.inChannels s.clip p β V)
lemma color_cost (η β:ℝ)(p:BudgetPoint)(h:R.Bounds s.clip s.width s.paths Λ) : Envelope (colored (n:=n) s R η β p):= covering p η ((PathData.channels_env h p β).neg.exp)
private abbrev share:= (Fintype.card Signed:ℝ)⁻¹
lemma air_stride (f:Signed→ℝ) : Real.exp (-( (Fintype.card Signed:ℝ)⁻¹ *∑ i:Signed,f i)) ≤ share *∑ i:Signed,Real.exp (- f i):=by
 have he:= convexOn_exp.map_sum_le (t:= (univ: Finset Signed)) (w:=fun i=>share) (p:=fun i=> -f i) (fun i _=>by unfold share; positivity) (by simp [share]) (fun i _=>Set.mem_univ _) -- tune
 simp only [smul_eq_mul,mul_neg, sum_neg_distrib, ←mul_sum] at he; exact he
lemma revenue (h:LocalRatio J)(Pmax Λ:ℝ)(b:0≤Λ)(s:Stage)(e:0<ε): ∀ᶠ x in atTop, ∀ β:ℝ,x/2≤β → β≤2*x →∀ p:BudgetPoint,p.threshold=temp x →∀ (n:Side),Intro n (radiusB x) →∀ (P:Bed)(a:ℝ),Floor P s.clip n a Pmax → 0<a →∀ R:PathData G, R.Bounds s.clip s.width s.paths Λ→ Attached P R → ∀ η:ℝ,η ≤ bonusK p s β /2 → (∫ U:Config G n, colored s R η β p U ∂prior G n) ≤ Real.exp (angular n J P β + ε * ser n):=by
 obtain ⟨F⟩:= negotiates G s; filter_upwards [monetize h F Pmax b e] with x v β p0 q0 p he n z P a hc c R W ha η hp
 let A:=Real.exp (angular n J P β + ε*ser n); let I(i:Signed)(V:Config G n):= R.principal s.clip p β (pull i 0 V); let X(V:Config G n):=Real.exp (tribute η p V)*Real.exp (-R.principal s.clip p β V); let μ:=prior G n; let f(i:Signed)(V:Config G n):= X (pull i 0 V)
 let Y(V:Config G n):= share*∑ i:Signed, f i V; have hh(V:Config G n): colored s R η β p V≤Y V:=by
    have ht(i:Signed): f i V= Real.exp (tribute η p V)*Real.exp (-I i V):=by unfold f X; simp_rw [tribute,match_miss V i 0]; rfl
    unfold Y colored PathData.inChannels; simp_rw [ht]; rw [← Finset.mul_sum,mul_left_comm]; refine mul_le_mul_of_nonneg_left (air_stride (fun i=> I i V)) (Real.exp_pos _).le -- tune
    -- infer
 let H:=covering p η (n:=n) ((PathData.principal_env W p β).neg.exp); have hw: Envelope X:= H; have hf(i:Signed): Integrable (f i) μ:= (prior_pull i (0:Site n)).integrable_comp_of_integrable (hw.integrable μ)
 have hg(i:Signed):(∫ V,f i V ∂μ)≤A:=by
    have he': (∫ V,X V ∂μ)=(∫ V,f i V∂μ):=by
       have hm:= (prior_pull i (0:Site n) (G:=G)); have hi':= integral_map (μ:=μ) (f:=X) hm.measurable.aemeasurable (hw.meas.aestronglyMeasurable); rw [hm.map_eq] at hi'; exact hi' -- tune accent
    rw [← he']; exact v β p0 q0 p he n z P a hc c R W ha η hp
 refine (integral_mono ((color_cost η β p W).integrable _) ((integrable_finsetSum _ (fun i _=> hf i)).const_mul share) hh).trans ?_; change ∫ V,Y V∂μ ≤ A; unfold Y; rw [integral_const_mul,integral_finsetSum]; swap; · exact fun i _=>hf i
 exact ((mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=>hg i)) (by unfold share; positivity:0≤ share))).trans_eq (by simp [share])
end Sage
end YM.SU5.FiniteGaugeData.Galope
