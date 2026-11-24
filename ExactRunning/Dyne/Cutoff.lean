import ExactRunning.Dyne.Deck

/-!
# End comparison via real quadratic Taylor coefficient

`balanced`: outgoing (endpoint, high) costs vs incoming (endpoint).
`re_fare`: thermal via tree determinant at no cut vs draft including q.
Both assuming only scalar `Melody` conditions on terms pulled over W.
`h_toFull` will tie them together.
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

-- removing the cut from the gapped determinant
namespace Latitude
open MeasureTheory

abbrev spec (S : Scene ι) (d : ℝ) (a b : ι) := fun t=> (ridge d).run S (tilt 0 t) a b

theorem spectrum {S : Scene ι}
    (h : ∀ d, (ridge d).Medium S) (a b : ι) :
    Tendsto (fun d => quad (spec S d a b)) (𝓝[>] 0)
            (𝓝 (quad (spec S (-1) a b))) := by
  let g := fun p => quad (fun t => S (tilt 0 t) p a b)
  have hx : ∀d, quad (spec S d a b) = (ridge d).mean g :=
    fun d => (h d).peel (tilt_smooth 0) (tilt_real 0)
      (Ode.magnetic _).quiet a b
  simp_rw [hx]
  refine tendsto_native ?_
  rw [← full_region]
  exact Latitude.integrableOn full (fun _ hx =>
    (((h (-1)).line (tilt_smooth 0) (tilt_real 0) (Ode.magnetic _).quiet a b).quad_regular
      _ hx).continuousAt)

end Latitude

/-- Has no-cut limit of second Taylor coefficient. -/
def Uptake (f : ℝ → ℝ → ℂ) : Prop := (∀r, ContDiff ℝ 2 (f r)) ∧
  Tendsto (fun r => quad (f r)) (𝓝[>] 0) (𝓝 (quad (f (-1))))

lemma Uptake.sum {u : ι → ℝ → ℝ → ℂ} (h : ∀i, Uptake (u i)) :
    Uptake (fun r t => ∑ i,u i r t) := by
  suffices hx : ∀s : Finset ι, Uptake (fun r t=> ∑ i ∈ s,u i r t) from hx _
  intro s
  induction s using Finset.induction with
  | empty =>
    simp only [sum_empty]
    exact ⟨fun r=>contDiff_const,tendsto_const_nhds⟩
  | @insert a s ha ih =>
    simp only [sum_insert ha]
    have he r := quad_add ((h a).1 r).contDiffAt (ih.1 r).contDiffAt
    change ∀r, quad (fun t=> u a r t+∑ i∈s,u i r t) = _ at he
    exact ⟨fun r=> ((h a).1 r).add (ih.1 r), by
      simp_rw [he]
      exact (h a).2.add ih.2⟩

lemma Uptake.mul {u} (h : Uptake u) (c : ℂ) : Uptake (fun r t=> c * u r t) := by
  refine ⟨fun r=> (h.1 r).const_smul c,?_⟩
  have he r : quad (fun t=> c*u r t) = _ := quad_weight (h.1 r).contDiffAt c
  simp_rw [he];exact h.2.const_smul _

lemma Uptake.spec {S : Scene ι} (h : ∀ d, (ridge d).Medium S) (x : Phase ι) :
    Uptake (fun r t=> x ⬝ᵥ (ridge r).run S (tilt 0 t) *ᵥ x) := by
  refine Uptake.sum fun i=> Uptake.mul (Uptake.sum fun j=> ?_) _
  have he : Uptake (fun r => Latitude.spec S r i j) :=
    ⟨fun r=> ((h r).smooth (tilt_smooth 0) (tilt_real 0) (Ode.magnetic _).quiet i j).of_le
       (WithTop.coe_le_coe.mpr le_top), Latitude.spectrum h _ _⟩
  simpa only [mul_comm (x j)] using he.mul (x j)

namespace BlockTie
variable (X)

theorem h_toFull (i : G.ColorIndex) :
    Tendsto (fun r => X.hValue r i) (𝓝[>] 0)
      (𝓝 (X.hValue (-1) i)) := by
  simp_rw [hValue, fun r=> rQuad_val (X.h_song r i).smooth]
  exact Complex.continuous_re.tendsto _ |>.comp
    (Uptake.spec X.h_scenes (defaultArm G (Pi.single (stripe i) 1))).2

variable {r : ℝ} (h : 0<r)

include h
/-- End comparison @ cutoff. It is enough to know the quadratic real
coefficient of the incoming term. -/
theorem balanced {U : ℝ → ℂ} (i : G.ColorIndex)
    (g : Melody X.lo i (fun m=> X.pullIn m r) U)
    (k : rQuad U = epValue E.F (X.back r) i) :
    X.hValue r i + epValue I.F (ridge r) i = epValue E.F (X.back r) i := by
  have e := Playing.through (I.endpoint.medium (D:=ridge r) h) (I.endpoint.data h)
  let Z := magcurve ((ridge r).run (epScene I.F)) i
  have a : X.zPaid r i = X.hPaid r i + Z := by
    refine Melody.eq_of_touch (ridge r) (X.z_song h i) ((X.h_song r i).add (e.bare i)) ?_
    intro m hm
    obtain ⟨T⟩ := X.test hm
    exact T.separated (X.h_safe ..) (X.z_safe h _) (X.railings _ _)
  have b : X.zNext r i = U := by
    rw [← add_zero U]
    refine Melody.eq_of_touch (ridge r) (X.z_reprise h i)
      (g.add (Melody.const (fun m=>X.k_const m r))) ?_
    exact fun _ _ x v => X.reduced (X.z_safe h _) (X.railings _ _) _ v (X.send_high v) (X.send_low v)
  rw [← k, ← b, rQuad.touch (X.z_reprise h i).smooth (X.z_song h i).smooth (X.z_deviation h _), a,
    rQuad.add (X.h_song r i).smooth (e.bare (lo:=0) i).smooth]
  rfl

omit h

theorem budget_end {u : ℕ → Side} (g : Tendsto (fun n=> (u n).val) atTop atTop) :
    Tendsto (fun n=> X.budget (u n) * 2) atTop (𝓝 0) := by
  have r := Real.tendsto_exp_atBot.comp
    (Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr X.hr) (tendsto_natCast_atTop_atTop.comp g))
  simpa [budget] using (r.const_mul X.toll).mul_const 2

theorem re_fare {U V : ℝ → ℂ} (i : G.ColorIndex) (e : Melody X.lo i X.inLaw U)
    (b : Melody X.lo i X.billLaw V) : rQuad U + X.hValue (-1) i = rQuad V := by
  let a := e.add (X.h_song (-1) i)
  suffices h : Complex.re ∘ (U+X.hPaid (-1) i)=Complex.re ∘ V by
    rw [hValue, ← rQuad.add e.smooth (X.h_song (-1) i).smooth]
    exact congr_arg quad h
  refine Radian.equalizer (Complex.continuous_re.comp a.smooth.continuous)
    (Complex.continuous_re.comp b.smooth.continuous) ?_
  intro t ht
  obtain ⟨w⟩ := (Ode.magnetic (.full)).pitch ht X.lo
  have e := ((Complex.continuous_re.tendsto _).comp (a.plays w) |>.sub ((Complex.continuous_re.tendsto _).comp (b.plays w))).abs
  refine sub_eq_zero.mp <| abs_eq_zero.mp <| le_antisymm
    (le_of_tendsto_of_tendsto e (X.budget_end w.grows) ?_) (abs_nonneg _)

  exact Eventually.of_forall fun n=> by
    obtain ⟨T⟩ := X.test (w.large n)
    exact T.echo_price (w.face n) (stripe i) (stripe i)

end BlockTie
end ExactRunning
