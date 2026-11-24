import YM.CF.Vp929.Fixed.Tower
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
open Ione Beau Haro Cascade Fief VolumeRate Branch
open scoped Mew ENNReal
open CF.Mint
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L} {d : ℝ} {B N : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi} {h delay : ℝ} {D C R0 : ℝ → ℝ} (B1 : ℕ) {N0 : ℕ} {P : Prescription R B}

private lemma between_ae {x y : ℝ} (t : x<y) {p : ℝ → Prop} (h : ∀ᵐ x ∂volume,p x) :
    ∃ z : ℝ, x<z ∧ z<y ∧ p z := by
  haveI : (ae (volume.restrict (Set.Ioo x y))).NeBot := ae_restrict_neBot.mpr (by rw [Real.volume_Ioo]; exact (ENNReal.ofReal_pos.mpr (by linarith)).ne')
  obtain ⟨a,⟨x,y⟩,z⟩:= ((ae_restrict_mem (μ:=volume) (s:=Set.Ioo x y) measurableSet_Ioo).and (ae_restrict_of_ae h)).exists; exact ⟨a,x,y,z⟩
private lemma realCover {a : ℝ} {f : ℝ → Prop} {T : ℝ → Prop}
    (pt : ∀ᵐ x ∂volume, a≤x → T x) (hf : ∀ x ≥ a,T x → ∀ᵐ y ∂volume,x < y → y ≤ x+3 → f y) :
    ∀ᵐ y ∂volume, a+2 ≤ y → f y := by
  have h(n:ℕ):∃ x:ℝ,a+n<x ∧ x < a+n+1 ∧ T x := by
    obtain ⟨x,u,v,t⟩:= between_ae (show a+n< a+n+1 by linarith) pt; exact ⟨x,u,v,t (by linarith [show 0≤(n:ℝ) from Nat.cast_nonneg _])⟩
  choose x u v t using h
  filter_upwards [ae_all_iff.mpr fun n=> hf (x n) (by linarith [u n,show 0 ≤ (n:ℝ) from Nat.cast_nonneg _]) (t n)] with y e h
  let n:= ⌊y-a-1⌋₊; have p:n ≤ y-a-1:= Nat.floor_le (by linarith); have q:y-a-1 < n+1:= Nat.lt_floor_add_one _; exact e n (by linarith [v n]) (by linarith [u n])

/-- Reduction to the two stage purchases of VOLUME_GRANTS (analytic/canonical step and Top-cut
switching). This uses no more smallness or convergence assumptions on the partitions. -/
theorem from_service {KX b' vL c' l' b DD E C0 h1 r:ℝ}{kT d' :ℕ} (P_: Pic.Span W.pearl KX b' vL c' l' b kT)(Q:Roe.Port P_ DD E C0 h1 r d')(hX:C0 ≤ h)
    {Λ:(s:Side)→Scree.Loom s→Prop} (tF:RackedΛ Λ J) (g : Service V U W J q h D C R0 P N0 delay) (u : Retag V U W J h N0 delay) (hD : Chill_v D) (t : ∀ᶠ x in atTop, 0 ≤ D x) (hh : 1≤h) (hP : ((R.L.val:ℝ)^4)⁻¹ < VolumeRate.propagation) :
    ∃ a : ℝ, ∀ᵐ x ∂volume,a≤x → DActual V W J q h D C R0 B1 N0 P delay x Λ := by
  obtain ⟨z,M,hz,h⟩:= grant_music V W; obtain ⟨d,t'⟩:= toned_ae R.L
  obtain ⟨a,p⟩:= eventually_atTop.mp ((((usable V W J N0 (d0:=delay) hD t @h).and (base_point J N0 P_ Q hX hh)).and (strip_large.eventually_ge_atTop 512)).and (eventually_ge_atTop d))
  refine ⟨a+2, realCover (t'.mono fun x hx A=> hx (le_trans ?_ A)) ?_⟩
  · exact (p a le_rfl).2
  intro x hx ht; obtain ⟨T,hT⟩:=(p x hx).1.1.1 ht; let r:= Rx x; have hp:3 ≤ r/8:= by have:= (p x hx).1.2; unfold r Rx; linarith
  have hr:0<r:= by linarith
  let f : ℝ→ℝ := fun y=> (y-x)/r; have Hf:MeasureTheory.Measure.QuasiMeasurePreserving f volume volume := by
    have hx : f = (r⁻¹ • ·) ∘ (fun y:ℝ=> y + -x) := funext fun _ => by dsimp [f]; ring
    rw [hx]; exact (MeasureTheory.Measure.quasiMeasurePreserving_smul volume (inv_ne_zero hr.ne')).comp (measurePreserving_add_right volume _).quasiMeasurePreserving
  have H := (interval_choice (B1:=B1) g u hh hT tF (p x hx).1.1.2 hP); change ∀ᵐ τ∂volume.restrict _, _ at H; rw [ae_restrict_iff' measurableSet_Ioc] at H
  filter_upwards [Hf.ae H,t'] with y hy v hY q; have he : f y∈Set.Ioc (0:ℝ) (1/8) := ⟨div_pos (by linarith) hr,(div_le_iff₀ hr).2 (by linarith)⟩
  specialize hy he; have hz:x+f y*Rx x=y:= by unfold f; rw [div_mul_cancel₀ _ hr.ne']; ring
  rw [hz] at hy; obtain ⟨T,u⟩:= (p y (by linarith)).1.1.1 (v (by linarith [(p x hx).2])); exact hy T u
lemma select_one {Y : ℝ → Prop} (H : ∃ a : ℝ, ∀ᵐ x ∂volume,a≤x → Y x) (x : ℝ) : ∃ y : ℝ, x<y ∧ Y y := by
  obtain ⟨a,p⟩:= H; obtain ⟨y,h,-,q⟩:= between_ae (lt_add_one (max x a)) p; exact ⟨y,(le_max_left ..).trans_lt h,q ((le_max_right ..).trans h.le)⟩
end YM.CF.Py.Rate
