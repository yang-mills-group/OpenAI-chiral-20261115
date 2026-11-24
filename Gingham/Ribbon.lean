import Velour.Wadding.Sachets
import Velour.Wadding.Pleats
import Gingham.Excise
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe

namespace Spine.Gingham

/-- A single simultaneous detector placement. In particular the
tsupports of **real** test-function slots are spacelike separated
(units c=1; stronger condition using one Cartesian component here).
The seam is at 0. Width accounted *inside* the wall budgets. -/
structure Weave where
  blot : SampleDose
  well : SampleDose
  wound : ℝ≥0
  topay : 0 < wound
  blot_one : blot.Normalized
  well_one : well.Normalized
  ra : Set Vantage
  rb : Set Vantage
  ta : tsupport blot.val ⊆ ra
  tb : tsupport well.val ⊆ rb
  oa : IsOpen ra
  ob : IsOpen rb
  ba : IsCompact (closure ra)
  bb : IsCompact (closure rb)
  l : ℝ
  r : ℝ
  room_a : Corners 3 l 0 blot wound
  room_b : Corners 3 0 r well wound
  gap : ℝ
  strict : 0 < gap
  stagger : ∀ x ∈ ra, ∀ y ∈ rb, (∀ i : Axis, gap < |y i - x i|) ∧
                  x 3 < y 3 ∧ y 3 - x 3 + gap < |y 0 - x 0|
  -- explicit bump prescription (can remove structure constraint if needed)
  -- separate proof after notions

/-- Translate a SampleDose by z, preserving the normalization and footprint. -/
def trim (B : SampleDose) (z : Vantage) : SampleDose where
  val y := B.val (y-z)
  smooth := B.smooth.comp (by fun_prop)
  budget := B.budget.comp_homeomorph (Homeomorph.subRight z)

lemma trim_in (B:SampleDose) (z y : Vantage) :
    y∈tsupport (trim B z).val ↔ y-z ∈ tsupport B.val := by
  rw [show tsupport (trim B z).val =
      (Homeomorph.subRight z)⁻¹' tsupport B.val from
       ((Homeomorph.subRight z).preimage_closure (Function.support B.val)).symm]; rfl

lemma trim_ahead (B : SampleDose) (p : E4) :
    sachet_LocalFieldBounds (trim B (foldSpace p)) = Boundary.Probe.ahead p (sachet_LocalFieldBounds B) := by
  ext1 y; exact congrArg (fun v => (B.val v:ℂ)) (foldSpace.map_sub y p).symm

lemma trim_one (B : SampleDose) (z : Vantage) (e : B.Normalized) :
    (trim B z).Normalized := by
  refine ⟨fun _=>e.1 _, (integral_sub_right_eq_self B.val z).trans e.2⟩

/-- Our chosen doses are *always* these dyadically sized test bumps plus
a possible small real time slew. -/
noncomputable abbrev nib (p : Vantage) (i : ℕ) := slider p (chosen p i)

def Condenses (p : Vantage) (B:ℕ→SampleDose) : Prop :=
  (∀ i,(B i).Normalized) ∧
  ∀ U ∈ 𝓝 p, ∀ᶠ i in atTop, tsupport (B i).val ⊆ U
lemma nib_to (p:Vantage) : Condenses p (nib p) :=
  ⟨fun _=>prescribed ..,concentrates p⟩
lemma condenses_after {p : Vantage}{B:ℕ→SampleDose} (e : Condenses p B)
    {g : ℕ→Vantage}(h:Tendsto g atTop (𝓝 0)) :
    Condenses p (fun i=>trim (B i) (g i)) := by
  refine ⟨fun i=>trim_one _ _ (e.1 i), fun U v=>?_⟩
  have he := ((continuous_fst.add continuous_snd
    : Continuous fun b:Vantage × Vantage=>b.1+b.2).tendsto (p,0)).eventually
      (show U ∈ 𝓝 (p+(0:Vantage)) by rwa [add_zero])
  have hu : (fun b:Vantage × Vantage=>b.1+b.2) ⁻¹' U ∈ 𝓝 (p,0) := he
  rcases mem_nhds_prod_iff.mp hu with ⟨V,hV,W,hW,s⟩
  filter_upwards [e.2 V hV,h.eventually hW] with i f t y k
  have hz : y-g i ∈ tsupport (B i).val := (trim_in ..).mp k
  have mn : y-g i+g i ∈ U := s (show (y-g i, g i) ∈ V ×ˢ W from ⟨f hz,t⟩)
  simpa using mn

lemma Condenses.reply {p : Vantage}{B:ℕ→SampleDose} (e : Condenses p B)
    {H:Hilbert}{F:Vantage→H} (v:Continuous F) :
    Tendsto (fun i=> DoseTravel.beam H (B i) F)
           atTop (𝓝 (F p)) := by
  refine Metric.tendsto_nhds.mpr fun d r=>?_
  have t := e.2 (F ⁻¹' Metric.ball (F p) (d/2))
      ((v.tendsto p).eventually (Metric.ball_mem_nhds _ (half_pos r)))
  filter_upwards [t] with i h
  rw [dist_eq_norm]
  refine (DoseTravel.tol p H F v _ (e.1 i) _ ?_).trans_lt (half_lt_self r)
  intro j q; rw [←dist_eq_norm]
  exact (Metric.mem_ball.mp (h q)).le

/-- The gap *and* the positive pads, including real-time spacing and
spacelike placements. Tick used at each core price is still separate. -/
def Spacing (d r : ℝ) (z : Vantage × Vantage) : Prop :=
     (∀ j : Axis, d < |z.2 j - z.1 j|) ∧
     z.1 3 < z.2 3 ∧ z.2 3 - z.1 3 + d < |z.2 0 - z.1 0| ∧
     z.1 3 - -(2*r) > r/2 ∧ 0 - z.1 3 > r/2 ∧
     z.2 3 - 0 > r/2 ∧ 2*r - z.2 3 > r/2

lemma spacing_nhds (d r : ℝ) (z : Vantage × Vantage) (p : Spacing d r z) :
    ∀ᶠ b in 𝓝 z, Spacing d r b := by
  have hx (j:Axis) : Continuous (fun y : Vantage × Vantage=>y.1 j) := by fun_prop
  have hy (j:Axis) : Continuous (fun y : Vantage × Vantage=>y.2 j) := by fun_prop
  have ha (j) := ((hy j).sub (hx j)).abs
  obtain ⟨p,a,b,s,t,h,c⟩ := p
  unfold Spacing
  exact (eventually_all.mpr fun i => tendsto_const_nhds.eventually_lt
       ((ha i).tendsto z) (p i)).and
     ((((hx 3).tendsto z).eventually_lt ((hy 3).tendsto z) a).and

     (((((hy 3).sub (hx 3)).add continuous_const).tendsto z|>.eventually_lt ((ha 0).tendsto z) b).and
     ((tendsto_const_nhds.eventually_lt (((hx 3).sub continuous_const).tendsto z) s).and
     ((tendsto_const_nhds.eventually_lt ((continuous_const.sub (hx 3)).tendsto z) t).and
     ((tendsto_const_nhds.eventually_lt (((hy 3).sub continuous_const).tendsto z) h).and
       (tendsto_const_nhds.eventually_lt ((continuous_const.sub (hy 3)).tendsto z) c))))))

/-- For candidate centred readings at -r,r, can enlarge to smooth test charges. -/
lemma weaves_late (r : ℝ≥0) (p q : Vantage) {B C : ℕ → SampleDose}
    (x : 0<r) (u : Condenses p B) (v : Condenses q C)
    (t : p 3 = -(r:ℝ)) (w : q 3=r)
    (g : ∀ j : Axis, j ≠ 3 → p j ≠ q j)
    (e : 2*(r:ℝ)< |q 0 - p 0|) :
    ∀ᶠ i in atTop, ∃ a : Weave, a.blot=B i ∧ a.well=C i ∧ a.wound = r/2 ∧
                                 a.l = -(2*(r:ℝ)) ∧ a.r = 2*r := by
  have rr : (0:ℝ)<r := x
  have g' : ∀ j : Axis, p j ≠ q j := by
    intro j; by_cases h:j=3
    · rw [h,t,w]; linarith
    exact g j h
  have hsp : ∀ᶠ d:ℝ in 𝓝[>] 0, Spacing d r (p,q) := by

    apply Eventually.filter_mono nhdsWithin_le_nhds
    have h : ∀ᶠ d in 𝓝 0, ∀ j:Axis,d< |q j - p j| :=
        eventually_all.mpr fun i=>gt_mem_nhds (abs_pos.mpr (sub_ne_zero.mpr (g' i).symm))
    filter_upwards [h,gt_mem_nhds (sub_pos.mpr e)] with d a b
    refine ⟨a,?_,?_,?_,?_,?_,?_⟩
    all_goals simp only [t,w]; linarith
  obtain ⟨d,hd,hd'⟩ := (hsp.and self_mem_nhdsWithin).exists
  obtain ⟨U,u1,R,r1,hUR⟩ := (mem_nhds_prod_iff (s:=setOf (Spacing d r))).mp
      (spacing_nhds d r (p,q) hd)
  obtain ⟨a,u2,u3⟩ := Metric.mem_nhds_iff.mp u1
  obtain ⟨b,r2,r3⟩ := Metric.mem_nhds_iff.mp r1
  have works (m n:Vantage) (i:m ∈ Metric.ball p a) (j:n∈Metric.ball q b) :
      Spacing d r (m,n) :=
    hUR (show (m,n)∈U×ˢR from ⟨u3 i,r3 j⟩)
  filter_upwards [u.2 _ (Metric.ball_mem_nhds _ u2),v.2 _ (Metric.ball_mem_nhds _ r2)] with i h k
  have he : (0:ℝ≥0)<r/2 := half_pos x

  refine ⟨⟨B i,C i,_,he,u.1 i,v.1 i,_,_,h,k,isOpen_ball,isOpen_ball,
          isBounded_ball.isCompact_closure,isBounded_ball.isCompact_closure,
          -(2*(r:ℝ)),2*r,?_,?_,d,hd',?_⟩,rfl,rfl,rfl,rfl,rfl⟩
  · intro m mm
    obtain ⟨-,-,-,d₁,d₂,-⟩ := works _ _ (h mm) (Metric.mem_ball_self r2)
    push_cast; exact ⟨d₁.le,d₂.le⟩
  · intro n nn
    obtain ⟨-,-,-,-,-,d₁,d₂⟩ := works _ _ (Metric.mem_ball_self u2) (k nn)
    push_cast; exact ⟨d₁.le,d₂.le⟩
  · intro m mm n nn
    obtain ⟨hu,hv,hw,-⟩ := works _ _ mm nn
    exact ⟨hu,hv,hw⟩

end Spine.Gingham
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
