import ExactRunning.Step.Thrust
import ExactRunning.Calc.Agree

/-!
# Finite-period graph

At available periods the actual saddle lifts to a nearby shell of `J`;
its Schur complement matches the completed next classical Hessian
to second order (`schur_touched`); use `rest_schur` pointwise then
the degree-four classical agreement in a moving chart.
-/


set_option linter.unusedSectionVars false
noncomputable section
namespace ExactRunning
open YM Stationary Lattice Laurent Bloch RG
open Function Filter Finset Matrix
open scoped BigOperators ContDiff Topology ComplexConjugate Matrix

open Exterior Wilson Precision
open Tree

namespace BlockTie
variable {G : Gauge} {E I : Pylon G} {m : Side} {X : BlockTie E I}


/-- Exponentiating W and using the added coarse-site frame associated
with centered frame = identity. -/
def lead (X : BlockTie E I) (m) := chevron (X.S m) (X.choice m) (X.W m) (G:=G)

lemma lead_zero : X.lead m 0=1 := chevron_zero _ _ _ X.branches
lemma lead_lit : Thaw (X.lead m) 0 := chevron_lit _ _ _ X.branches

namespace Test
variable (T : X.Test m)

/-- True stationary graph (lifting tree saddle into joint fields). -/
def B (T : X.Test m) := liftedUp T.tree (X.W m) T.shellChart
lemma b0 : T.B 0 = 1 := lift_origin T.critical
lemma b01 : (T.B 0).1 = 1 := congrArg Prod.fst T.b0

lemma thaw : Thaw T.B 0 := liftedThaw T.critical

lemma stable : ∀ᶠ z in 𝓝 0, X.Stable (T.B z) (input G m z) :=
  veteran_status T.critical X.branches _ E.paths


include T
lemma high_unit : IsUnit (X.high (m:=m) 1 1).det := by
  have h := (tribute T.critical X.branches E.paths T.gap X.hg X.hμ (X.choice m) X.actual).self_of_nhds.1
  rw [input_zero, encamp_zero T.critical] at h
  rw [X.high_eq]; exact h.ne'.isUnit

def eff := fun x => X.J m (input G m x) (T.B x)

lemma tandem : Tandem 4 T.eff (fun y => mainTerm I.p I.r (input _ _ y)) := by
  let Q := fun x => tested T.tree (X.choice m) E.p E.r x (T.shellChart x)
  let P := fun x : fieldDir G m 1 => mainTerm I.p I.r (represent x)
  have h : Tandem 4 Q P :=
    ⟨(T.classicalMatch 0 (by decide) (X.choice m)).1,
     (T.classicalMatch 0 (by decide) (X.choice m)).2.1,fun i hi =>
     (T.classicalMatch i hi (X.choice m)).2.2⟩
  refine (h.pre (k:=arm G m 1) ((arm G m 1).contDiff.contDiffAt) (map_zero _)).congr ?_ .rfl
  filter_upwards [salary T.critical X.branches (X.choice m) E.paths (X.W m),
    wage_live T.critical X.branches (X.choice m) (W:=X.W m)] with z hz ht
  change Q (arm G m 1 z)= X.J m (input G m z) (T.B z)
  exact hz.symm.trans (congr_arg (X.J m (input G m z)) ht)

omit T
def offset (z y : Link G m) := content (input G m y * input G m z)
lemma offset_zero : offset (0 : Link G m) 0=0 := by simp [offset]
lemma offset_analytic : ContDiffAt ℝ ω (Function.uncurry (offset (G:=G) (m:=m))) 0 := by
  refine (?_ : Army (fun p : Link G m×Link G m => input G m p.2 * input G m p.1) 0).logL (by simp)
  exact (Army.powL contDiffAt_snd).mul (Army.powL contDiffAt_fst)

lemma offset_input :
    ∀ᶠ p in 𝓝 (0 : Link G m×Link G m), input G m (offset p.1 p.2)=input G m p.2 * input G m p.1 :=
  ((show Tendsto (fun p : Link G m × Link G m => input G m p.2 * input G m p.1) (𝓝 0) (𝓝 1) by
    convert (((Army.powL (G:=G) (x:=(0 : Link G m×Link G m)) contDiffAt_snd).mul
      (Army.powL contDiffAt_fst)).cont.tendsto) using 2; simp).eventually content_encodes)

lemma thaw_inv {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y] {g : Y→ Joint G m (X.up m)}
   (hg : Thaw g 0) : Thaw (fun y=> (g y)⁻¹) 0 :=
   ⟨hg.1.inv,hg.2.inv⟩

include T
/-- Graph in left-increment charts at B(z) and its coarse background. -/
def lathe (z y : Link G m) := retract (T.B (offset z y) * (T.B z)⁻¹)

lemma lathe_ready :
    (∀ᶠ z in 𝓝 0, X.Rest (T.lathe z) (T.B z) (input G m z)) ∧
    (∀ᶠ p in 𝓝 (0 : Link G m×Link G m), Stationary.extend (T.lathe p.1 p.2)*T.B p.1=T.B (offset p.1 p.2)) := by
  let d := Function.uncurry (offset (G:=G) (m:=m))
  let A (p : Link G m × Link G m) := T.B (d p) * (T.B p.1)⁻¹
  have hd : d 0=0 := offset_zero
  have ha : A 0=1 := by simp [A,hd]
  have hh := (show Thaw T.B (d 0) by rw [hd]; exact T.thaw).comp (w:=d) offset_analytic
  have hj := T.thaw.comp (w:=Prod.fst (α:=Link G m) (β:=Link G m)) (x:=0) contDiffAt_fst
  have hp : Thaw A 0 := hh.mul (thaw_inv hj)
  have hl := (show ContDiffAt ℝ ω (Function.uncurry T.lathe) 0 from hp.log ha)
  have hm : ∀ᶠ p in 𝓝 (0:Link G m×Link G m),
      Stationary.extend (T.lathe p.1 p.2)*T.B p.1=T.B (offset p.1 p.2) := by
    filter_upwards [(ha ▸ hp.cont.tendsto : Tendsto A _ (𝓝 1)).eventually extend_retract] with p hx
    rw [show lathe T p.1 p.2 = retract (A p) from rfl, hx]; simp [A,d]; rfl
  refine ⟨?_,hm⟩
  have ht : Tendsto (fun z : Link G m => (z, (0:Link G m))) (𝓝 0) (𝓝 0) :=
    tendsto_id.prodMk_nhds tendsto_const_nhds
  have hu : ∀ᶠ p : Link G m × Link G m in 𝓝 0,
      X.Stable (Stationary.extend (T.lathe p.1 p.2)*T.B p.1) (input G m p.2 * input G m p.1) := by
    have hd' : Tendsto d (𝓝 0) (𝓝 0) := hd ▸ offset_analytic.continuousAt.tendsto
    filter_upwards [hd'.eventually T.stable, hm, offset_input] with p hz hj hk
    rw [hj, ← hk];exact hz
  filter_upwards [ht.eventually (hl.eventually (by simp)), ht.eventually hu.eventually_nhds, input_encodes]
    with z hx hz hy
  refine ⟨Work.F05.hold_jet hx, by simp [lathe,offset,hy],contDiffAt_id,rfl,
    Work.F05.hold_near hz⟩

private lemma duet :
    Tandem 4 (fun a : Link G m × Link G m =>
            X.sitting (T.B a.1) (input G m a.1) (T.lathe a.1 a.2,a.2))
          (fun a => burn I.p I.r (input G m a.1) a.2) := by
  refine (T.tandem.pre offset_analytic offset_zero).congr ?_ ?_
  · filter_upwards [offset_input, T.lathe_ready.2] with p hx hj
    change X.J m (input G m (offset p.1 p.2)) (T.B (offset p.1 p.2))= X.J m _ (Stationary.extend (T.lathe p.1 p.2)*T.B p.1)
    rw [hj,hx]
  filter_upwards [offset_input] with p hx
  exact congr_arg (mainTerm I.p I.r) hx

lemma high_live : ∀ᶠ z in 𝓝 0, IsUnit (X.high (T.B z) (input G m z)).det := by
  have h := (X.high_memo T.thaw T.b01
    (v:=input G m) (Army.powL contDiffAt_id)).det_val
  refine (h.continuousAt.eventually_ne
    (show (X.high _ _).det ≠ 0 by rw [input_zero,b0]; exact T.high_unit.ne_zero)).mono fun _ h => h.isUnit

theorem schur_touched {k : ℝ → Link G m} (hk : ContDiffAt ℝ ω k 0) (h0 : k 0 = 0) :
    MatTouch (fun t => X.schur (T.B (k t)) (input G m (k t)))
      (fun t => epMat I.p I.r (input G m (k t))) := by
  have he := T.duet
  have ht := X.full_fare T.thaw T.b01 (v:=input G m) (Army.powL contDiffAt_id)
  have hd : Tendsto k (𝓝 0) (𝓝 0) := h0 ▸ hk.continuousAt.tendsto
  have hx := (memo_flash X.hμ (Army.powL (G:=G) hk)).1
  have hv := hx.cross hx.spot
  intro i j
  let A := pocket (Lines G m 1)
  have hp := (he.hess_touch hk h0 ![A i,A j]).add (Touch.refl ((hv i j).continuousAt))
  refine hp.congr ?_ ?_
  · filter_upwards [hd.eventually T.lathe_ready.1, hd.eventually (X.movers T.thaw T.b01),
      hd.eventually T.high_live, hd.eventually ht] with t h h' u s
    rw [X.rest_schur s h h' u,damage,Matrix.add_apply,LinearMap.toMatrix₂_apply,Work.F05.bend_apply]
  filter_upwards with t
  rw [epMat, flare, damage, Matrix.add_apply,LinearMap.toMatrix₂_apply,Work.F05.bend_apply]

end Test
end BlockTie
end ExactRunning
