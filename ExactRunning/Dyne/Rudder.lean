import ExactRunning.Dyne.Hatch

/-!
# Transport of the quadratic coefficient

`hatch_touch`: through second order in magnetic momentum, incoming
leg from previous file can be replaced by its ideal representative,
zero except on central alias (scalar times unit polarization there).
`cargo_transfer` concludes, collecting scalar and volume factors.
-/

set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

set_option synthInstance.maxSize 1024

open Pairing

variable {G : Gauge} {E I : Pylon G} {m L : Side} {X : BlockTie E I}
variable {ι : Type} [Fintype ι] [DecidableEq ι]

open Asymptotics

lemma Cost.even {f : ℝ → ℂ} (h : ContDiffAt ℝ 2 f 0)
    (w : ∀t, f (-t)=f t) : Cost (fun t=> f t-f 0) := by
  have ha : HasDerivAt f (deriv f 0) (-0) := by
    rw [neg_zero]; exact (h.differentiableAt (by simp)).hasDerivAt
  have ht : HasDerivAt f ((-1:ℝ)•deriv f 0) 0 := by
    convert! ha.scomp 0 (hasDerivAt_neg _) using 1
    funext; exact (w _).symm
  have hd : deriv f 0=0 := by
    have hm := ht.deriv
    rw [neg_one_smul] at hm
    linear_combination hm / 2
  have hy := (isBigO_refl (fun t:ℝ=> t^2) (𝓝 0)).smul (isBigO_const_one ℝ (quad f) _)
  exact ((touch_quad h).small.isBigO.add
    (hy.congr_right fun _=>mul_one _)).mono nhdsWithin_le_nhds |>.congr_left fun _=>by rw [hd,smul_zero]; abel

namespace BlockTie
variable (X)
variable {K : Kin (Entry G)}

lemma fare_cost (i) :
    Cost (fun t=> X.coin i (-tilt 0 t) * X.coin i (tilt 0 t) - (inch X.L:ℂ)^2) := by
  let f := X.coin i
  have h : ContDiffAt ℝ 2 f (tilt 0 0) := tilt_zero 0 ▸ X.coin_lit i
  have k : ContDiffAt ℝ 2 f (-tilt 0 0) := by rwa [tilt_zero,neg_zero,← tilt_zero 0]
  have q : ContDiffAt ℝ 2 (tilt 0) 0 := (tilt_smooth 0).contDiffAt.of_le le_top
  refine (Cost.even (f:=fun t=> _)
    ((k.comp 0 q.neg).mul (h.comp 0 q)) ?_)
     |>.congr_left ?_
  all_goals simp [f,tilt_zero, tilt_neg,X.coin_zero,pow_two,mul_comm]

lemma Inert.weight {ι : Type} [Fintype ι] {x y : Phase ι} {K : Kin ι} {p : Momentum}
    (h : Inert K p x y) (c d : ℂ) : Inert K p (c•x) (d•y) := fun v => by
  simp [smul_dotProduct,mulVec_smul,dotProduct_smul,(h v).1,(h v).2]

variable {r : ℝ}

lemma hatch_hit (w : Lateral (X.back r) K LinearMap.id)
    (i) (l) (t) :
    X.hatch (-tilt 0 t) i (-l) ⬝ᵥ
      K (aliasAt (tilt 0 t) l) *ᵥ X.hatch (tilt 0 t) i l = X.harmonic K i l t := by
  refine Inert.minus ?_
  simp only [hatch,add_sub_cancel_left]
  rw [show pageD G 0 (aliasAt (-tilt 0 t) (-l))=pageD G 0 (-aliasAt (tilt 0 t) l) from
        congr_arg (tintedLocal G) (rolls_symbol (alias_counter _ _) _)]
  exact w.hit ((Ode.magnetic (ridge r)).aliases X l) t _ _

abbrev ideal (K : Kin (Entry G)) i (l : Site X.L) (t : ℝ) :=
  X.aim i (-l) (-tilt 0 t) ⬝ᵥ K (aliasAt (tilt 0 t) l) *ᵥ X.aim i l (tilt 0 t)

lemma ideal_cont (k : Score (X.back r) K) (l : Site X.L)
    {u v : ℝ → Phase (Entry G)}
    (ha : ContinuousAt u 0)
    (hb : ContinuousAt v 0) :
    ContinuousAt (fun t => u t ⬝ᵥ K (aliasAt (tilt 0 t) l) *ᵥ v t) 0 := by
  let z := (Ode.magnetic (ridge r)).aliases X l
  have hc : ContinuousAt (fun t=> K (aliasAt (tilt 0 t) l)) 0 :=
    continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j=> (k z i j).continuous.continuousAt
  exact (((continuous_fst.dotProduct
        ((continuous_fst.comp continuous_snd).matrix_mulVec (continuous_snd.comp continuous_snd))).tendsto _).comp
      (ha.tendsto.prodMk_nhds (hc.tendsto.prodMk_nhds hb.tendsto)))

lemma hatch_touch (k : Score (X.back r) K) (w : Lateral (X.back r) K LinearMap.id)
    (i l) : Touch (X.harmonic K i l) (X.ideal K i l) := by
  let z := (Ode.magnetic (ridge r)).aliases X l
  have hc : ContinuousAt (fun t=> K (aliasAt (tilt 0 t) l)) 0 :=
    continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j=> (k z i j).continuous.continuousAt
  have ha : ContinuousAt (fun t=> X.aim i (-l) (-tilt 0 t)) 0 :=
    ContinuousAt.comp (g:=X.aim i (-l)) (by rw [tilt_zero,neg_zero]; exact (X.aim_lit _ _).continuousAt)
      (tilt_smooth 0).continuous.continuousAt.neg
  have hb : ContinuousAt (fun t=> X.aim i l (tilt 0 t)) 0 :=
    ContinuousAt.comp (g:=X.aim i l) (by rw [tilt_zero]; exact (X.aim_lit _ _).continuousAt)
      (tilt_smooth 0).continuous.continuousAt
  refine Touch.on_cut (X.harmonic_smooth k i l).continuous.continuousAt
    (X.ideal_cont k l ha hb) ?_

  let u t := X.hatch (-tilt 0 t) i (-l) - X.aim i (-l) (-tilt 0 t)
  let v t := X.hatch (tilt 0 t) i l - X.aim i l (tilt 0 t)
  have inert :
      Inert K (aliasAt (tilt 0 0) l) (X.aim i (-l) (-tilt 0 0)) (X.aim i l (tilt 0 0)) := by
    by_cases e : l=0
    · subst l
      simp only [aim,tilt_zero,neg_zero,if_true,show aliasAt 0 (0:Site X.L)=0 by simp [aliasAt]]
      exact Inert.weight (w.zero k i) _ _
    simp only [aim,e,neg_eq_zero,if_false]
    intro v
    simp
  refine (shake (u:=u) (v:=v) hc ha.continuousWithinAt hb.continuousWithinAt
    ?_ (X.hatch_cost _ i l) inert).congr_left ?_
  · intro j
    simpa only [u, tilt, smul_neg,axes_flip] using!
      X.hatch_cost (-(Lattice.step (0:Axis))) i (-l) j
  intro t
  dsimp only [u,v]
  rw [add_sub_cancel,add_sub_cancel,X.hatch_hit w i l t]

lemma ideal_sum (K : Kin (Entry G)) (i) (t) :
    ∑ l, X.ideal K i l t =
      (X.coin i (-tilt 0 t)*X.coin i (tilt 0 t)) *
      magcurve K i (inch X.L * t) := by
  rw [sum_eq_single (0:Site X.L)]
  · simp only [ideal,neg_zero,aim, ↓reduceIte, mulVec_smul, dotProduct_smul,smul_dotProduct,
               single_dotProduct, mulVec_single]
    have hx : aliasAt (tilt 0 t) (0:Site X.L)=tilt 0 (inch X.L*t) := by
      unfold tilt
      rw [alias_zero_loc,smul_smul]
    simp [hx,magcurve,mul_assoc,mul_left_comm]
  · intro l _ h; simp [ideal,aim,h]
  simp

/-- Alias sum carries exactly the intensive magnetic coefficient. -/
theorem cargo_transfer (k : Score (X.back r) K) (w : Lateral (X.back r) K LinearMap.id)
    (i) : rQuad (X.cargo K i) = alphaK K i := by
  have c : ContDiff ℝ 2 (magcurve K i) :=
    k (Ode.magnetic _) _ _
  let g t := magcurve K i (inch X.L * t)
  have cg : ContDiff ℝ 2 g := c.comp (contDiff_const.mul contDiff_id)
  have q : Tendsto g cutRay (𝓝 0) := by
    suffices g 0 = 0 from this ▸ cg.continuous.continuousAt.continuousWithinAt
    have e := (w.zero k i (Pi.single (stripe i) 1)).1
    simp [g,magcurve,tilt_zero,mulVec_single,single_dotProduct] at e ⊢
    exact e

  have H := Touch.sum (fun l (_ : l∈univ)=> X.hatch_touch k w i l)
  simp only [X.ideal_sum K i] at H
  let f := (inch X.L)^2 • g
  have R : Touch (fun t=> ∑ l, X.harmonic K i l t) f := by
    refine H.trans (Touch.on_cut H.hg
      (continuousAt_const.smul cg.continuous.continuousAt) ?_)
    exact (soft_change (X.fare_cost i) q).congr_left fun t => by
      rw [sub_mul]
      simp only [f,g,Pi.smul_apply,Complex.real_smul, Complex.ofReal_pow]
  set d : ℝ := (X.L.val : ℝ) ^ 4
  have hr : Touch (X.cargo K i) (d • f) :=
    ((Touch.const d).smul R).congr
      (Eventually.of_forall fun t=>by simp [cargo,d])
      EventuallyEq.rfl
  have cf : ContDiff ℝ 2 f := cg.const_smul (inch X.L^2)
  have one : d * (inch X.L^2*(inch X.L^2)) =1 := by
    calc _=(inch X.L * X.L.val)^4 := by unfold d;ring
         _=1 := by rw [inch_unit,one_pow]
  rw [rQuad.touch (X.cargo_smooth k i) (show ContDiff ℝ 2 (d•f) from cf.const_smul d) hr,
      rQuad.weight cf, rQuad.weight cg,rQuad, show quad (Complex.re ∘ g)=_ from quad_rescale (f:=Complex.re ∘ magcurve K i)
        (Complex.reCLM.contDiff.comp c) (inch X.L)]
  simp only [smul_eq_mul,←mul_assoc]
  rw [mul_assoc d (inch X.L^2) _,one,one_mul]
  rfl

end BlockTie
end ExactRunning
