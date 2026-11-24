/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Vp929.Stage.Plant
import YM.Next.RANK.LineBox

/-!
# The canonical beta is observable from the field

With the regulator constants of one fixed step. Continuity need not be assumed in
norm (budgets don’t come in that topology here). We use the pure Lie line in the
gauge test, purchasing a uniform Taylor estimate on the regular aperture.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
namespace LocalLimit
variable {s : Side} {p : BudgetPoint} {i : Scree.Hub s}
  {F : RegBudget s} {A : Scree.InkD s} {h b C x : ℝ}

local notation "ray" => AnalyticBridge.VerifiedReset.line

def directionCurrency (p : BudgetPoint) (X : tangD s) : ℝ :=
  p.threshold / (1+‖X‖)

private lemma currency_pos (p : BudgetPoint) (X : tangD s) : 0 < directionCurrency p X :=
  div_pos p.threshold_pos (by positivity)

private lemma currency_dir (p : BudgetPoint) (X : tangD s) (o : Skye.Seat s) :
    p.dirBound o (directionCurrency p X • X) := by
  intro i
  rw [Pi.smul_apply,norm_smul,Real.norm_of_nonneg (currency_pos p X).le]
  calc
    _ ≤ directionCurrency p X * (1+‖X‖) := by
      exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm X i).trans (le_add_of_nonneg_left zero_le_one))
        (currency_pos p X).le
    _ = _ := div_mul_cancel₀ _ (ne_of_gt (by positivity : 0 < 1+‖X‖))
    _ ≤ _ := le_mul_of_one_le_right p.threshold_pos.le (one_le_pow₀ (by simp))

private lemma along_paid (X : tangD s) (hc : 1 ≤ h) (v : PressB p i A h b)
    (u : pingS p.threshold i.val.2 (ray X x)) (j : ℕ) (hj : j ≤ p.order) :
    let M : ℝ → ℝ := Test.unRl A ∘ ray X
    ContDiffAt ℝ j M x ∧ ‖iteratedDeriv j M x‖ ≤ ‖Complex.reCLM‖*b / directionCurrency p X ^ j := by
  intro M
  have hg := (Test.lintR v hc).toll (ray X x) u
  let L := (ContinuousLinearMap.id ℝ ℝ).smulRight X
  let G := Test.unRl A ∘ increment (ray X x)
  have he : (fun t : ℝ=> M (x+t)) = G ∘ L :=
    funext fun t=> congrArg (Test.unRl A) (Next.Rank.Spindle.progress (1:Pane s) X x t)
  have ht : ContDiffAt ℝ j G 0 := hg.paid.of_le (by exact_mod_cast hj)
  have h' : ContDiffAt ℝ j (G ∘ L) 0 := (show ContDiffAt ℝ j G (L 0) from L.map_zero ▸ ht).comp _ L.contDiff.contDiffAt
  constructor
  · have hx : M = (G ∘ L) ∘ fun t=> t-x := by rw [←he]; ext y; simp
    rw [hx]
    exact (show ContDiffAt ℝ j (G ∘ L) (x-x) from (by rwa [sub_self])).comp x (f:=fun t=> t-x) (by fun_prop)
  have e : iteratedDeriv j M x = iteratedFDeriv ℝ j G 0 (fun _=> X) := by
    calc
      _ = iteratedDeriv j (fun t=> M (x+t)) 0 := by rw [iteratedDeriv_comp_const_add]; simp
      _ = _ := by
        rw [he, iteratedDeriv, Push.Uniform.iter_lin_at (show ContDiffAt ℝ j G (L 0) from L.map_zero ▸ ht), map_zero,
          ContinuousMultilinearMap.compContinuousLinearMap_apply]; simp [L]
  rw [e, le_div_iff₀ (pow_pos (currency_pos p X) _),mul_comm]
  let c := directionCurrency p X
  have hz := hg.token j hj (fun _=> c • X) (fun _=> currency_dir p X _)
  change ‖iteratedFDeriv ℝ j G 0 (fun _=> c • X)‖ ≤ _ at hz
  rw [show iteratedFDeriv ℝ j G 0 (fun _=> c • X) = c^j • iteratedFDeriv ℝ j G 0 (fun _=> X)
      from ?_, norm_smul,Real.norm_of_nonneg (pow_pos (currency_pos _ X) _).le] at hz
  · exact hz
  rw [(iteratedFDeriv ℝ j G 0).map_smul_univ (fun _=>c) (fun _=>X)]; simp

open AnalyticBridge.VerifiedReset (flat_critical)

private lemma along_first_zero (X : tangD s) (hc : 1 ≤ h) (v : PressB p i A h b) :
    iteratedDeriv 1 (Test.unRl A ∘ ray X) 0 = 0 := by
  let M := Test.unRl A ∘ ray X
  let L := (ContinuousLinearMap.id ℝ ℝ).smulRight X
  let G := Test.unRl A ∘ increment (1:Pane s)
  have h : fderiv ℝ G 0 = 0 := flat_critical Thera.yet_one (Test.lintR v hc).regular
  have ht : ContDiffAt ℝ 2 G 0 := AnalyticBridge.VerifiedReset.germ_diff (Test.lintR v hc).regular
  have he : (Test.unRl A ∘ ray X) = G ∘ L := rfl
  rw [he, iteratedDeriv_one, deriv, fderiv_comp 0 ?_ L.differentiableAt, L.map_zero, h]; swap
  · rw [map_zero]; exact ht.differentiableAt (by norm_num)
  rw [ContinuousLinearMap.zero_comp]; rfl

private def gaugedHubSum (F : RegBudget s) (X : tangD s) (x : ℝ) :=
  ∑ i, Test.unRl (F i) (ray X x)

private lemma all_hubs_sum {X : tangD s} (v : pingS p.threshold univ (ray X x)) :
    (Pastry.pane (exponentL p F (ray X x))).re = gaugedHubSum F X x := by
  have hv (i : Scree.Hub s) : pingS p.threshold i.val.2 (ray X x) :=
    fun p h=> v p (fun q=> h (Disjoint.mono_left (subset_univ _) q))
  unfold exponentL numbE; simp_rw [fun j:Scree.Hub s=> Set.indicator_of_mem (show ray X x ∈ setOf (fun U:Pane s=>pingS p.threshold j.val.2 U) from hv j) (F j)]
  rw [Pastry.pane_f,Complex.re_sum]; rfl

private lemma hubSmooth (hc : 1 ≤ h) (hf : IncX Utrue F p h b) (X : tangD s)
    (hp : pingS p.threshold univ (ray X x)) (j : ℕ) (hj : j ≤ p.order) :
    ContDiffAt ℝ j (gaugedHubSum F X) x ∧
    ‖iteratedDeriv j (gaugedHubSum F X) x‖ ≤ (Fintype.card (Scree.Hub s):ℝ) *
      (‖Complex.reCLM‖*b / directionCurrency p X ^ j) := by
  obtain ⟨c,g,t⟩ := hf.weight
  let U(i:Scree.Hub s) := Test.unRl (F i) ∘ ray X
  have q(i:Scree.Hub s) := along_paid X hc (g i) (fun p h=> hp p (fun q=> h (Disjoint.mono_left (subset_univ _) q))) j hj
  refine ⟨ContDiffAt.sum (f:=U) (fun i _=> (q i).1),?_⟩
  have hz i : 0 ≤ c i := Beau.grit_p p (g i) (zero_le_one.trans hc)
  have hy(i:Scree.Hub s) : c i ≤ b := by
    let W(k:Scree.Hub s) := if i.val.1=k.val.1 then p.mass k.val.2 (c k) else 0
    calc
      _ ≤ W i := by unfold W; rw [if_pos rfl]; exact BudgetPoint.loMass p _ _ (hz i)
      _ ≤ ∑ i,W i := single_le_sum (fun i _=> by unfold W; split; exact mul_nonneg (Real.exp_pos _).le (hz i); exact le_rfl) (mem_univ i)
      _ ≤ _ := t _
  change ‖iteratedDeriv j (fun a=>∑ i,U i a) x‖ ≤ _
  rw [iteratedDeriv_fun_sum (f:=U) (fun i _=> (q i).1)]
  refine (norm_sum_le ..).trans ((sum_le_sum (fun i _=> (q i).2.trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hy i) (norm_nonneg _))
    (pow_pos (currency_pos p X) _).le))).trans_eq ?_); simp

private lemma sum_first_zero (hc : 1 ≤ h) (hf : IncX Utrue F p h b) (X : tangD s) :
    iteratedDeriv 1 (gaugedHubSum F X) 0 = 0 := by
  obtain ⟨c,g,t⟩ := hf.weight
  let U(i:Scree.Hub s) := Test.unRl (F i) ∘ ray X
  change iteratedDeriv 1 (fun x=> ∑ i,U i x) 0 = _
  have he : ray X 0 = (1:Pane s) := by simp [AnalyticBridge.VerifiedReset.line]
  rw [iteratedDeriv_fun_sum (f:=U) (fun i _=> (along_paid X hc (g i) (he ▸ ping_f p _) 1 (by have := p.order_ge; omega)).1)]; exact sum_eq_zero fun i _=> along_first_zero X hc (g i)

private lemma sum_hess_zero {σ : ℝ} (hg : gaugeTest σ F p = 0) :
    iteratedDeriv 2 (gaugedHubSum F (transverse σ)) 0 = 0 := by
  change (sites s)⁻¹*_ = 0 at hg
  rw [mul_eq_zero] at hg
  exact (Test.exponent_track (transverse σ) p F|>.iteratedDeriv_eq (n:=2)) ▸ (hg.resolve_left (inv_ne_zero (lt_of_lt_of_le zero_lt_one (sites_pos s)).ne'))


private lemma regular_taylor (hc : 1 ≤ h) (hf : IncX Utrue F p h b) {σ k : ℝ} (hg : gaugeTest σ F p = 0)
    (hu : 0 < k) (hp : ∀ a ∈ Set.Icc (0:ℝ) k, pingS p.threshold univ (ray (transverse (s:=s) σ) a)) :
    let D := (Fintype.card (Scree.Hub s):ℝ) *
      (‖Complex.reCLM‖*b / directionCurrency p (transverse (s:=s) σ) ^ 3)
    ‖gaugedHubSum F (transverse σ) k - gaugedHubSum F (transverse σ) 0‖ ≤ D*k^3 / 2 := by
  let X := transverse (s:=s) σ
  let U := gaugedHubSum F X
  let S := Set.Icc (0:ℝ) k
  intro D
  have hz : (0:ℝ) ∈ S := Set.left_mem_Icc.mpr hu.le
  have he (i : ℕ) (hi : i≤3) (x : ℝ) (p' : x∈S) := hubSmooth hc hf X (hp x p') i (le_trans hi (le_trans (by norm_num : 3 ≤ 6) p.order_ge))
  have hw (i : ℕ) (hi : i≤3) (x : ℝ) (p' : x∈ S) : iteratedDerivWithin i U S x = iteratedDeriv i U x := iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hu) (he i hi x p').1 p'
  have ht := taylor_mean_remainder_bound (n:=2) (C:=D) (f:=U) hu.le (fun i hi => ContDiffWithinAt.of_le (he 3 le_rfl i hi).1.contDiffWithinAt (by norm_num)) (Set.right_mem_Icc.mpr hu.le) (fun y u=> by rw [hw _ le_rfl _ u]; exact (he 3 le_rfl y u).2)
  rw [taylor_within_apply,sum_range_succ,sum_range_succ,sum_range_one,
    hw 0 (by norm_num) _ hz,hw 1 (by norm_num) _ hz,hw 2 (by norm_num) _ hz,show iteratedDeriv 2 U 0=0 from sum_hess_zero hg, show iteratedDeriv 1 U 0=0 from sum_first_zero hc hf X] at ht
  norm_num [Nat.factorial] at ht
  exact ht

open Push.BetaTransport

-- Full angle room is not needed; just accuracy of positive flux test.
private lemma flux_lower {A : PathData SU.group} {f : Clip} {d e g σ : ℝ}
    {L : Side} (p : BudgetPoint) (h : A.Bounds f d e g) (hf : Frequency L s σ) :
    ∃ c > (0:ℝ), ∀ᶠ x : ℝ in 𝓝[>] (0:ℝ), c * x^2 ≤ kinetic A f p (ray (transverse (s:=s) σ) x) := by
  let X := transverse (s:=s) σ
  let B := Test.takeB X A f
  have he : 0 < B := by
    have e := (mul_pos (Test.posed f) (zero_lt_one.trans_le (sites_pos s))).trans_le (Test.split_rate h hf)
    linarith
  let c := B/2
  refine ⟨c,half_pos he,?_⟩
  have hT : Tendsto (fun x:ℝ=> kinetic A f p (ray X x)/x^2) (𝓝[>] (0:ℝ)) (𝓝 B) :=
    (Test.tide h X p).mono_left (nhdsGT_le_nhdsNE _)
  filter_upwards [hT.eventually (le_mem_nhds (half_lt_self he)), self_mem_nhdsWithin] with x p hx
  exact (le_div_iff₀ (pow_pos (show 0<x from hx) _)).1 p

variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d : ℝ} {m B : Side} {U : Grasp V.U B d}
local notation "Ω" => mid m B

/-- The slow beta is continuous in the input family when its output density is
continuous pointwise and its gauge-counter test is zero. Not trying to propagate
sup-norm continuity of coefficient budgets. `b` prices their curvature estimates. -/
lemma continuous_beta_of_dens
    {F : Scree.Loom (mid m B)} {k : ℕ} {I : Interest (mid m B)} {f : Clip} {p : BudgetPoint}
    {A : PathData SU.group} {d₀ d₁ d₂ h b x σ : ℝ} {L : Side}
    (hh : 1 ≤ h) (u : Roof (mid m B) x d k F) (hr : U.roundZ ≤ (mid m B).val)
    (hf : Frequency L (mid m B) σ) (hA : A.Bounds f d₀ d₁ d₂) (tags : Ids (mid m B))
    {T : Type*} [TopologicalSpace T] (G : T → Corr (mid m B)) (o : T → ℂ) (β : T → ℝ)
    (hG : ∀ t, IncX Utrue (G t).1 p h b) (hx : ∀ t, gaugeTest σ (G t).1 p = 0)
    (H : ∀ y : Pane (mid m B), Rue.FleetS p.threshold y → Continuous fun t=>
      denZ (construct p A f I (β t) (G t) (o t)) U F (y,tags)) : Continuous β := by
  let X := transverse (s:=Ω) σ
  let Y(a:ℝ) : Orbit Ω := (ray X a,tags)
  let r : Set ℝ := {a|pingS p.threshold univ (ray X a)}
  let M(a:ℝ) := changeM U (F (Y a)) I.M
  let g(a:ℝ) := kinetic A f p (ray X a)
  let Z(t:T) := denZ (construct p A f I (β t) (G t) (o t)) U F
  let C (a:ℝ) :=
    A.inChannels f p 0 (ray X a) + (Pec.pigment I.I (F (Y a))).re -
            (Pastry.pane (Hest.boat (I.P.den (F (Y a))))).re
  let readβ (a:ℝ) (t:T) := Real.log ‖inner ℂ (M a) (Z t (Y a))‖ + C a
  have hread a (hr' : a∈r) t := sea_read U A f F I (G t) (o t) (β t) (Y a) (Test.homeFlag (r:=p.threshold) hr') hr (u.paid _)
  have hl a (hr':a∈r) t : readβ a t =
      (o t).re + gaugedHubSum (G t).1 X a - β t * g a := by
    unfold readβ
    unfold M Z; rw [hread a hr' t,Complex.norm_exp,Real.log_exp]; unfold C g
    simp only [Complex.add_re,Complex.sub_re,Complex.ofReal_re]; dsimp only [Y]
    rw [all_hubs_sum (show pingS p.threshold _ (ray X a) from hr'), channels_split _ (β t),
      channels_split _ (0:ℝ),zero_mul,zero_add]
    ring
  have hr0 : ray X 0 = 1 := by simp [AnalyticBridge.VerifiedReset.line]
  have ht : 0∈r := by change pingS _ _ (ray X 0); rw [hr0]; exact ping_f _ _
  have hg0 : g 0 = 0 := by rw [show g 0 = kinetic A f p (ray X 0) from rfl,hr0,kinetic_one]
  have hct (a) (hr':a∈r) : Continuous (readβ a) := by
    apply Continuous.add _ continuous_const
    refine Continuous.log ((continuous_const.inner (H (ray X a) (Test.QuiltB.home_fleet hr'))).norm) ?_
    intro t
    unfold M Z; rw [hread a hr' t]; exact (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _))
  let D := (Fintype.card (Scree.Hub Ω):ℝ) * (‖Complex.reCLM‖*b / directionCurrency p X ^ 3)
  let f'(a:ℝ) (t:T) := (readβ 0 t - readβ a t)/g a
  obtain ⟨c,hc,hac⟩ := flux_lower p hA hf
  have hn : r∈𝓝 (0:ℝ) := Test.homeS X p
  have hu : ∀ᶠ a:ℝ in 𝓝[>] (0:ℝ), ∀ t, dist (f' a t) (β t) ≤ a*D/(2*c) := by
    obtain ⟨d,e,g₀⟩ := Metric.mem_nhds_iff.mp hn
    filter_upwards [hac, ((gt_mem_nhds e).filter_mono nhdsWithin_le_nhds), self_mem_nhdsWithin] with a ha m (hp : 0<a) t
    have ht' y (v : y ∈ Set.Icc (0:ℝ) a) : y∈r :=
        g₀ (by rw [mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg v.1]; exact v.2.trans_lt m)
    let E(a) := gaugedHubSum (G t).1 X a
    have hv : c*a^2 ≤ g a := ha; have hw : 0 < g a := (by positivity : 0 < c*a^2).trans_le hv
    have hy : f' a t - β t= (E 0-E a)/g a := by
      unfold f'; rw [hl 0 ht,hl a (ht' a ⟨hp.le,le_rfl⟩),hg0]; unfold E; field_simp; ring
    have hC : |E a-E 0| ≤ D*a^3/2 := regular_taylor hh (hG t) (hx t) hp ht'
    rw [Real.dist_eq,hy,abs_div,abs_of_pos hw,abs_sub_comm]
    apply le_trans (div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hc (pow_pos hp _)) hv)
    refine (div_le_div_of_nonneg_right hC (by positivity)).trans_eq ?_; field_simp
  refine TendstoUniformly.continuous (p:=𝓝[>] (0:ℝ)) (F:=f') ?_ (Eventually.frequently ?_)
  swap
  · exact ( (show ∀ᶠ x in 𝓝 (0:ℝ), x∈r from hn).filter_mono nhdsWithin_le_nhds).mono fun a ha => Continuous.div_const ((hct 0 ht).sub (hct a ha)) _
  rw [Metric.tendstoUniformly_iff]; intro ε hε
  have h : Tendsto (fun a:ℝ=> a*D/(2*c)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [zero_mul, zero_div,id_eq] using ((show Tendsto id (𝓝[>] (0:ℝ)) (𝓝 0) from tendsto_id.mono_left nhdsWithin_le_nhds).mul_const D).div_const (2*c)
  filter_upwards [hu, h.eventually (gt_mem_nhds hε)] with a h₁ h₂ t; rw [dist_comm]; exact lt_of_le_of_lt (h₁ t) h₂

end LocalLimit
end YM.CF.Py.Rate
