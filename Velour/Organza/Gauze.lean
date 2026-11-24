import YM.Heat.Lift

/-! # R, the only energy scale we need for cap lifting

Use B=R-inverse on its common smooth space; R intended as (1+Energy)^(-1).
The crucial buy will be that with energy scale charged on both sides one can
use nothing but the geometric cap estimates upwards of any positive padding,
then **transfer all the energy losses to one side** with Minkowski smearing.
Avoid unbounded spectral multipliers & graph-scale completion.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 1100
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)

private noncomputable def fibers (u:ℝ) : H.Op:= Real.exp (-u) • S.E u.toNNReal
lemma contHeat : ContinuousOn (fun u:ℝ=> S.E u.toNNReal) (Set.Ioi 0) := by
 refine (S.localHeat.continuousOn.comp continuous_ofReal.continuousOn
  (s:=Ioi 0) (fun _ h=>show _ from h)).congr fun u hu=>?_
 have ht:0<u.toNNReal:= Real.toNNReal_pos.mpr hu
 change S.E _ = S.F _
 rw [← S.roots_heat ht, duration,Real.coe_toNNReal u (le_of_lt hu)]
private lemma fibers_cont : ContinuousOn S.fibers (Ioi 0):= by
 unfold fibers
 exact (Real.continuous_exp.comp continuous_neg).continuousOn.smul S.contHeat
private lemma fibers_norm (u:ℝ) : ‖S.fibers u‖ ≤ Real.exp (-u):=by
 rw [fibers,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
 exact mul_le_of_le_one_right (by positivity) (S.shrinks _)
private lemma fibers_good : IntegrableOn S.fibers (Ioi 0):=
 (integrableOn_exp_neg_Ioi 0).mono' (S.fibers_cont.aestronglyMeasurable measurableSet_Ioi)
    (ae_of_all _ S.fibers_norm)
/-- Bounded inverse energy weight. -/
def gauze : H.Op:= ∫ u in Ioi (0:ℝ), S.fibers u
local postfix:max "♮" => gauze


lemma gauze_norm : ‖S.gauze‖≤1:= by
 exact (norm_integral_le_of_norm_le (integrableOn_exp_neg_Ioi 0) (ae_of_all _ S.fibers_norm)).trans
   (le_of_eq integral_exp_neg_Ioi_zero)
lemma gauze_unbroken (Z:H.Op)(h : ∀ t, Commute Z (S.E t)): Commute Z S.gauze:= by
  let M := ContinuousLinearMap.mul ℂ H.Op
  change M Z S.gauze = M.flip Z S.gauze
  rw [gauze,← (M Z).integral_comp_comm S.fibers_good,← (M.flip Z).integral_comp_comm S.fibers_good]
  exact integral_congr_ae (ae_of_all _ fun u=> by
    change Z * (Real.exp (-u) • S.E _)=(Real.exp (-u) • S.E _)*Z
    rw [mul_smul_comm,smul_mul_assoc,(h _).eq])
lemma gauze_heated (t) : Commute (S.E t) S.gauze := S.gauze_unbroken _ (fun u=>
 show (S.E t).comp (S.E u) = _ from by rw [← S.time,add_comm,S.time]; rfl)
lemma gauze_star : star S.gauze=S.gauze:=by
 let L:H.Op→L[ℝ] H.Op :=
    { toFun:= star, map_add':= star_add, map_smul':= fun t y=> star_smul t y, cont:=continuous_star }
 change L S.gauze=_
 rw [gauze, ←L.integral_comp_comm S.fibers_good]
 exact integral_congr_ae (ae_of_all _ fun u=> by
   change star (S.fibers u) = S.fibers u
   have h (t) : star (S.E t)= S.E t:= S.sym _
   rw [fibers,star_smul,h]; rfl)
private lemma fibers_head (u:ℝ≥0) :
  IntervalIntegrable S.fibers volume 0 (u:ℝ) :=
 (intervalIntegrable_iff_integrableOn_Ioc_of_le u.coe_nonneg).mpr
   (S.fibers_good.mono_set Ioc_subset_Ioi_self)

private lemma fibers_shift (u:ℝ≥0) :
  ∫ t in Ioi (u:ℝ), S.fibers t = Real.exp (-(u:ℝ)) • (S.E u * S.gauze):= by
  let M := ContinuousLinearMap.mul ℂ H.Op (S.E u)
  rw [←(measurePreserving_add_left volume (u:ℝ)).setIntegral_preimage_emb
    (measurableEmbedding_addLeft _),show (fun x:ℝ=>↑u + x) ⁻¹' Ioi (u:ℝ)=Ioi 0 by
        ext; simp,show S.E u * _= M S.gauze from rfl,gauze,← M.integral_comp_comm S.fibers_good,
     ← integral_smul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t p=> ?_)
  rw [fibers,fibers,neg_add, Real.exp_add, mul_smul,
    Real.toNNReal_add u.coe_nonneg (le_of_lt p),Real.toNNReal_coe, S.time]
  change _= _ • (S.E u * (_ • _))
  rw [mul_smul_comm]; rfl


private lemma split_pay (u:ℝ≥0) :
 S.gauze = (∫t in 0..(u:ℝ), S.fibers t) + Real.exp (-(u:ℝ)) • (S.E u * S.gauze):= by
  rw [← S.fibers_shift, intervalIntegral.integral_of_le u.coe_nonneg]
  refine (Eq.trans ?_ (setIntegral_union
     (Set.disjoint_left.mpr (fun _ hv hx=>not_lt.mpr hv.2 hx))
     measurableSet_Ioi (S.fibers_head u).1
     (S.fibers_good.mono_set (Ioi_subset_Ioi u.coe_nonneg))))
  rw [Ioc_union_Ioi_eq_Ioi u.coe_nonneg]; rfl

lemma gauze_tug (u:ℝ≥0) :
   ‖S.gauze - S.E u * S.gauze‖ ≤ 2 * (u:ℝ):= by
  let W := S.E u * S.gauze
  let Z:=∫t in (0:ℝ)..↑u, S.fibers t
  have t: ‖Z‖≤ (u:ℝ):= by
    have h : |(u:ℝ)-0| = (u:ℝ):= by rw [sub_zero,abs_of_nonneg u.coe_nonneg]
    exact (intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=↑u) (C:=1)
      (fun x y=> (S.fibers_norm x).trans (Real.exp_le_one_iff.mpr (neg_nonpos.mpr
        ((show (0:ℝ)<x from
         (show x∈ Ioc (0:ℝ) ↑u from uIoc_of_le u.coe_nonneg ▸ y).1)).le)))).trans_eq (by rw [one_mul,h])


  have h : ‖W‖≤1:=(norm_mul_le ..).trans (mul_le_one₀ (S.shrinks _) (norm_nonneg _) S.gauze_norm)
  have h₁ : 0≤1-Real.exp (-(u:ℝ)):=sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr u.coe_nonneg))
  have h₂ : 1-Real.exp (-(u:ℝ))≤↑u:=by linarith only [Real.add_one_le_exp (-(u:ℝ))]
  have hx : S.gauze - W= Z - ((1:ℝ)- Real.exp (-u)) • W:=by
    calc
      _ = Z + Real.exp (-u) • W - W:= congrArg (· - W) (S.split_pay u)
      _ = _ := by rw [sub_smul,one_smul]; abel
  rw [hx]; refine (norm_sub_le ..).trans ?_
  rw [norm_smul,Real.norm_of_nonneg h₁]
  rw [two_mul]; exact add_le_add t ((mul_le_of_le_one_right h₁ h).trans h₂)


private lemma gauze_flow (u:ℝ) (p:0<u) :
 HasDerivAt (fun y=> S.E y.toNNReal * S.gauze) (S.E u.toNNReal * S.gauze - S.E u.toNNReal) u := by
  let q (r:ℝ) := ∫t in (0:ℝ)..r, S.fibers t
  have it (r:ℝ)(g:0<r) : Real.exp r • (S.gauze - q r)= S.E r.toNNReal * S.gauze:= by
    have h : S.gauze - q r=Real.exp (-r) • (S.E r.toNNReal * S.gauze) := by
      have H₀ := S.split_pay r.toNNReal
      rw [Real.coe_toNNReal r g.le] at H₀
      exact (sub_eq_iff_eq_add).mpr (H₀.trans (add_comm ..))
    rw [h, smul_smul, ← Real.exp_add,add_neg_cancel,Real.exp_zero,one_smul]
  have iu: IntervalIntegrable S.fibers volume 0 u:=(Real.coe_toNNReal u p.le) ▸ S.fibers_head (u.toNNReal)
  have hq: HasDerivAt q (S.fibers u) u:= intervalIntegral.integral_hasDerivAt_right iu
    (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi S.fibers_cont u p)
    (S.fibers_cont.continuousAt (Ioi_mem_nhds p))
  have ik:= ((Real.hasDerivAt_exp u).smul (hq.const_sub S.gauze)).congr_of_eventuallyEq
    (f₁:= fun y=> S.E y.toNNReal * S.gauze)
    (show _ =ᶠ[𝓝 u] _ from (eventually_gt_nhds p).mono fun y hy=>(it y hy).symm)
  rw [it _ p, fibers, smul_neg, smul_smul, ← Real.exp_add, add_neg_cancel,
    Real.exp_zero, one_smul, neg_add_eq_sub] at ik
  exact ik

lemma deriv_gauze (t:ℝ≥0)(v : 0<t): deriv S.F (t:ℝ) * S.gauze = S.E t * S.gauze - S.E t := by
 let p := (S.localHeat _ (dur.mpr v)).differentiableAt.hasDerivAt
 have h : HasDerivAt (fun y:ℝ=> S.E y.toNNReal) (deriv S.F (t:ℝ)) (t:ℝ):=by
    have k := p.scomp (t:ℝ) (hasDerivAt_id' (t:ℝ)).ofReal_comp
    rw [ofReal_one, one_smul] at k
    refine k.congr_of_eventuallyEq ?_
    exact (eventually_gt_nhds (show 0<(t:ℝ) from v)).mono fun y hy=> by
     change S.E _= S.F _
     rw [← S.roots_heat (Real.toNNReal_pos.mpr hy),duration,Real.coe_toNNReal _ hy.le]
 have k := (h.mul_const S.gauze).unique (S.gauze_flow (t:ℝ) v)
 rwa [Real.toNNReal_coe] at k


lemma heat_weighted (t:ℝ≥0)(p:0<t): ∃Z, S.E t = Z * S.gauze := by
  refine ⟨S.E t - deriv S.F (t:ℝ), ?_⟩
  rw [sub_mul, S.deriv_gauze _ p]; abel
lemma gauze_injective: Injective S.gauze := by
  obtain ⟨Z,e⟩:=S.heat_weighted 1 zero_lt_one
  intro x y h; exact sub_eq_zero.mp (S.heat_faithful 1 (x-y) (by
    rw [e, map_sub, mul_apply_eq_comp, mul_apply_eq_comp,h,sub_self]))

lemma heat_scale (t:ℝ≥0)(p:0<t)(n:ℕ): ∃ Z, S.E t = S.gauze ^ n * Z:= by
 induction n generalizing t with
 | zero=> exact ⟨_,(one_mul _ |>.symm).trans (congrArg (· * S.E t) (pow_zero _).symm)⟩
 | succ n ih =>
    let s:= t/2
    have j:0<s:= half_pos p
    obtain ⟨Z,r⟩:=ih s j; obtain ⟨U,v⟩:= S.heat_weighted s j
    have o:star (S.E s)=S.E s:=S.sym s
    have h:S.E s=S.gauze * star U:=o.symm.trans (by conv_lhs=> rw [v,star_mul,S.gauze_star])
    refine ⟨star U * Z,?_⟩
    calc
     S.E t = S.E s * (S.gauze^n * Z):=by rw [←r];exact (congrArg S.E (add_halves t).symm).trans (S.time s s)
     _ = _:=by rw [←mul_assoc,((S.gauze_heated s).pow_right n).eq]

               rw [h,pow_succ]; simp only [mul_assoc]

lemma gauze_const {vac:H} (h:∀ t, S.E t vac=vac): S.gauze vac=vac:=by
 let M:= ContinuousLinearMap.apply ℂ H.space vac -- params?
 change M S.gauze=vac
 rw [gauze, ← M.integral_comp_comm S.fibers_good]
 change ∫ u:ℝ in Ioi 0, (Real.exp (-u) • S.E u.toNNReal) vac=vac
 simp_rw [smul_apply, h]
 rw [integral_smul_const, integral_exp_neg_Ioi_zero,one_smul]
#check S.edge
#print axioms heat_scale


lemma raise_lined (t:ℝ≥0)(p:0<t)(r:ℝ) :
  HasDerivAt (fun y=> S.edge (y*r) * S.E t * S.gauze)
     (((r:ℂ)*I) • (S.E t * (1 - S.gauze))) 0:= by
  have v:(duration t + sideways (0*r)) ∈ inside := length.mpr p
  have h: HasDerivAt (fun y:ℝ=>duration t + sideways (y*r)) (-((r:ℂ)*I)) 0 := by
    unfold sideways; rw [←neg_mul]
    exact (by
      have hx:= (((hasDerivAt_id' (0:ℝ)).mul_const r).ofReal_comp.neg.mul_const I).const_add (duration t)
      rwa [one_mul] at hx)
  have z := (((S.localHeat _ v).differentiableAt.hasDerivAt).scomp 0 h).mul_const S.gauze
  simp only [zero_mul,side_zero,add_zero,smul_mul_assoc] at z
  have g : deriv S.F (duration t) * S.gauze= _ := S.deriv_gauze t p
  rw [g,show _-_ = -(S.E t * (1-S.gauze)) by rw [mul_sub, mul_one, neg_sub], neg_smul, smul_neg,neg_neg] at z
  exact z.congr_of_eventuallyEq (Eventually.of_forall fun y=>
    congrArg (· * S.gauze) <| show _ = S.F (duration t+sideways (y*r)) by
        rw [← S.roots_heat p]
        exact S.along (dur.mpr p) _)
