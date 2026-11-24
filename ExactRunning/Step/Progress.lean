import ExactRunning.Step.Test

/-!
# Tangency in external variables

At the level of first external derivatives, `X.lead` can stand in for
`T.B` (in chart at the trivial fields; see `Test.progress`). Enough
for second order if used in a quantity with vanishing first derivative,
and for passage back to the true saddle in `Fit` statements.
-/


set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree


variable {U H Y : Type} [NormedAddCommGroup U] [NormedAddCommGroup H] [NormedAddCommGroup Y]
  [NormedSpace ℝ U] [NormedSpace ℝ H] [NormedSpace ℝ Y]

/-- Two analytic shapes agreeing through first. -/
structure Progress (p q : U → H) : Prop where
  hp : ContDiffAt ℝ ω p 0
  hq : ContDiffAt ℝ ω q 0
  p0 : p 0=0
  q0 : q 0=0
  eq : fderiv ℝ p 0=fderiv ℝ q 0

namespace Progress
variable {p q : U → H}

lemma smooth (h : Progress p q) {f : H → Y} (hf : ContDiffAt ℝ ω f 0) :
    ContDiffAt ℝ ω (f ∘ p) 0 ∧ ContDiffAt ℝ ω (f ∘ q) 0 :=
  ⟨ContDiffAt.comp _ (h.p0.symm ▸ hf) h.hp, ContDiffAt.comp _ (h.q0.symm ▸ hf) h.hq⟩

lemma derivatives (h : Progress p q) {f : H → Y} (hf : ContDiffAt ℝ ω f 0) :
    fderiv ℝ (f ∘ p) 0 = fderiv ℝ (f ∘ q) 0 := by
  rw [fderiv_comp, fderiv_comp,h.p0,h.q0,h.eq]
  all_goals
    try simp only [h.p0,h.q0]
    apply ContDiffAt.differentiableAt _ (by simp : ω≠0)
  all_goals first | exact h.hp | exact h.hq | exact hf


lemma quadratic (h : Progress p q) {f : H → ℝ} (hf : Flat f) : Tandem 2 (f ∘ p) (f ∘ q) := by
  refine ⟨(h.smooth hf.smooth).1, (h.smooth hf.smooth).2,fun i hi => ?_⟩
  interval_cases i
  · ext1;simp [h.p0,h.q0]
  · ext1; rw [iteratedFDeriv_one_apply,iteratedFDeriv_one_apply,h.derivatives hf.smooth]
  ext1 v; rw [show v=![v 0,v 1] by funext i; fin_cases i <;> rfl,
   ← Work.F05.bend_apply, ← Work.F05.bend_apply,hf.bend h.hp h.p0,hf.bend h.hq h.q0,h.eq]

lemma fit {p q : ℝ → H} {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {P : ModeCut m} {Q : ModeCut n} (h : Progress p q) {A : H → Matrix m n ℝ}
    (ha : Memo A 0) (hA : Fit P Q (A ∘ p)) : Fit P Q (A ∘ q) := by
  have hx := fun i j => h.smooth (ha i j)
  have hv : Van1 (fun t => A (q t) - A (p t)) := by
    intro i j
    have hp := (((hx i j).2.differentiableAt (by simp)).hasDerivAt.sub
      ((hx i j).1.differentiableAt (by simp)).hasDerivAt)
    rw [deriv,deriv,h.derivatives (ha i j),sub_self,hasDerivAt_iff_isLittleO_nhds_zero] at hp
    simpa [h.p0,h.q0] using hp
  have hk : Van1 (fun t => A (p t) - A (q t)) := by
    simp_rw [← neg_sub (A (q _)) _]; exact fun _ _ => (hv _ _).neg_left
  refine ⟨fun i j => (hx i j).2.continuousAt,
    (hA.van.add ((hv.mul_left (MatCont.const P.e)).add (hk.mul_right (MatCont.const Q.e)))).congr ?_⟩
  exact Eventually.of_forall fun t=> by simp only [Function.comp_apply,Matrix.mul_sub,Matrix.sub_mul];abel

lemma comp {D : Type} [NormedAddCommGroup D] [NormedSpace ℝ D] {p q : D → H}
    {r s : U → D} (h : Progress p q) (g : Progress r s) :
    Progress (p ∘ r) (q ∘ s) := by
  refine ⟨(g.smooth h.hp).1,(g.smooth h.hq).2,by simp [g.p0,h.p0],
     by simp [g.q0,h.q0],(g.derivatives h.hp).trans ?_⟩
  rw [fderiv_comp _ _ (g.hq.differentiableAt (by simp)),
      fderiv_comp _ _ (g.hq.differentiableAt (by simp)), g.q0, h.eq]
  all_goals rw [g.q0];first | exact h.hp.differentiableAt (by simp) | exact h.hq.differentiableAt (by simp)

lemma refl (hp : ContDiffAt ℝ ω p 0) (ho : p 0=0) : Progress p p :=
  ⟨hp,hp,ho,ho,rfl⟩

end Progress
namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}

def plait (X : BlockTie E I) (y : Link G m) := retract (X.lead m y)
lemma plait_analytic : ContDiffAt ℝ ω (X.plait (m:=m)) 0 :=
  X.lead_lit.log X.lead_zero
lemma plait_zero : X.plait (m:=m) 0=0 := by rw [plait,X.lead_zero,retract_one]
lemma plait_fine (y : Link G m) :
    (fderiv ℝ X.plait 0 y).1 = uniformM (X.W m) y := by
  let F := ContinuousLinearMap.fst ℝ (Link G (X.up m)) (BaseSites G m)
  have he : F ∘ X.plait =ᶠ[𝓝 0] ⇑(uniformM (G:=G) (X.W m)) :=
    (show Tendsto (uniformM (G:=G) (X.W m)) (𝓝 0) (𝓝 0) by
      simpa only [map_zero] using (uniformM (G:=G) (X.W m)).continuous.tendsto 0).eventually input_encodes
  have hp := he.fderiv_eq (𝕜:=ℝ)
  rw [fderiv_comp 0 F.differentiableAt (X.plait_analytic.differentiableAt (by simp)),
    F.fderiv,(uniformM (G:=G) (X.W m)).fderiv] at hp
  exact DFunLike.congr_fun hp y

def stroll (X : BlockTie E I) (y : Link G m) : Point G m (X.up m) := (y,X.plait y)
def Test.street (T : X.Test m) (y : Link G m) : Point G m (X.up m) := (y,retract (T.B y))

namespace Test
variable (T : X.Test m)

lemma progress : Progress X.stroll T.street := by
  let F := T.tree
  let K (p : Point G m (X.up m)) := (p.1,retract (enroll (X.S m) (X.choice m) (Stationary.extend p.2)))
  have h : Thaw (fun p : Point G m (X.up m) => enroll (X.S m) (X.choice m) (Stationary.extend p.2)) 0 :=
     X.B0_lit.to_cap X.branches _ X.B0_fine
  have ho : enroll (X.S m) (X.choice m) (G:=G) 1=1 :=
    dressed_one (fedora_style X.branches (X.choice m))
  have hK : ContDiffAt ℝ ω K 0 :=
    contDiffAt_fst.prodMk (h.log (by rw [Prod.snd_zero,extend_zero];exact ho))
  have hp : K ∘ pace T.tree T.shellChart (X.W m) (X.choice m) =ᶠ[𝓝 0] T.street :=
     (wage_live T.critical X.branches (X.choice m) (W:=X.W m)).mono fun _ hx => Prod.ext rfl (congr_arg retract hx)
  exact ⟨contDiffAt_id.prodMk X.plait_analytic,
    contDiffAt_id.prodMk (T.thaw.log T.b0),Prod.ext rfl X.plait_zero,Prod.ext rfl
     (by rw [street,T.b0]; exact retract_one), (stem_pay (X.choice m) T.critical T.guess X.branches (hK.differentiableAt (by simp))).symm.trans
           hp.fderiv_eq⟩

lemma rook : X.Rest (fun z => retract (T.B z)) 1 1 := by
  refine ⟨T.thaw.log T.b0,by rw [T.b0,retract_one],contDiffAt_id,rfl,?_⟩
  filter_upwards [T.stable,(T.b0 ▸ T.thaw.cont.tendsto : Tendsto T.B _ (𝓝 1)).eventually extend_retract]
    with z hz hb
  simpa only [mul_one,hb]

include T
lemma plait_legal (y : Link G m) :
    X.thick 1 1 *ᵥ cash (helmets _ _ _) (fderiv ℝ X.plait 0 y) + X.spat 1 1 *ᵥ y=0 := by
  have he := DFunLike.congr_fun T.progress.eq y
  have hp := (contDiffAt_id (𝕜:=ℝ) (n:=ω) (x:=(0:Link G m))).differentiableAt (by simp)
  unfold stroll Test.street at he
  erw [(hp.hasFDerivAt.prodMk ((X.plait_analytic (m:=m)).differentiableAt (by simp)).hasFDerivAt).fderiv,
     (hp.hasFDerivAt.prodMk (T.rook.sr.differentiableAt (by simp)).hasFDerivAt).fderiv] at he
  rw [show fderiv ℝ X.plait 0 y = _ from congrArg Prod.snd he]
  exact X.rest_coarse X.sitting_zero T.rook _

lemma travel {C : Joint G m (X.up m) → Config G m → ℝ}
    (h : Flat (fun p => C (X.B0 p) (X.V0 p))) :
    Tandem 2 (fun y => C (X.lead m y) (input G m y))
          (fun y => C (T.B y) (input G m y)) := by
  refine (T.progress.quadratic h).congr ?_ ?_
  · filter_upwards [(X.lead_zero ▸ X.lead_lit.cont.tendsto : Tendsto (X.lead m) _ (𝓝 1)).eventually extend_retract]
      with z hz using congr_arg (fun b => C b (input G m z)) hz
  filter_upwards [(T.b0 ▸ T.thaw.cont.tendsto : Tendsto T.B _ (𝓝 1)).eventually extend_retract]
    with z hz using congr_arg (fun b => C b (input G m z)) hz

lemma travel_fit {k l : Type} [Fintype k] [DecidableEq k] [Fintype l] [DecidableEq l]
    {P : ModeCut k} {Q : ModeCut l}
    {C : Joint G m (X.up m) → Config G m → Matrix k l ℝ} (hc : Memo (fun p => C (X.B0 p) (X.V0 p)) 0)
    {g : ℝ → Link G m} (hg : ContDiffAt ℝ ω g 0) (h0 : g 0=0)
    (h : Fit P Q (fun t => C (X.lead m (g t)) (input G m (g t)))) :
    Fit P Q (fun t => C (T.B (g t)) (input G m (g t))) := by
  have hv : Tendsto g (𝓝 0) (𝓝 0) := h0 ▸ hg.continuousAt.tendsto
  refine ((T.progress.comp (.refl hg h0)).fit hc (h.congr ?_)).congr ?_
  · filter_upwards [hv.eventually ((X.lead_zero ▸ X.lead_lit.cont.tendsto : Tendsto (X.lead m) _ (𝓝 1)).eventually extend_retract)]
        with t hz using congr_arg (fun b => C b (input G m (g t))) hz.symm
  filter_upwards [hv.eventually ((T.b0 ▸ T.thaw.cont.tendsto : Tendsto T.B _ (𝓝 1)).eventually extend_retract)]
        with t hz using congr_arg (fun b => C b (input G m (g t))) hz

end Test
end BlockTie
end ExactRunning
