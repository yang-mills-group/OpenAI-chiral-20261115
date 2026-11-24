import SatinFixedContrastNovember4
import YM.SU5.Thin.SlabLimits
import YM.SU5.Thin.Pair

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "κ"=>P.calibration
section bounds
private lemma apronPermit (A:P.Apron)(δ:ℝ)(u:0≤δ)
    (K: PaidHeight (i:=P.period) (k:=P.cutoff) (a:=P.projection.rows) (b:=P.projection.columns) P.run P.large A.s δ)
    (M0:ℝ)(n:ℕ)(c:Axis→ℤ)
    (H:pay (P.shifts j (A.u j) A.F).val M0)
    (ht:Transom j (plow κ j (A.u j) A.S) c n) : ‖A.engine P j x‖ ≤Real.sqrt (thinStand P.par κ (A.u j+A.u j) n M0 δ) := by
  let D:= A.u j; let w:= D+D; let f:= A.cardB P j; let S:= plow κ j D A.S
  have hw: 0<w:=add_pos (A.pos j) (A.pos j)
  let B:= P.colorSpace j x; let F:= P.door j A.s w hw f (A.color P j)
  have hx:‖B F‖ ≤ ‖F‖ := NonUnitalStarAlgHom.norm_apply_le _ _
  refine hx.trans (slabBound P.run P.large P.law A.s P.history j false (P.room j) w f P.projection.clipped hw δ u K S ?_ ?_ M0 H n c ht)
  · exact (Tapestry.locates ..).1 (P.shifts_support j _ A.S A.bay)
  let ψ:= A.inside_shift P j; have hs:(w:ℤ)=(D:ℤ)+(D:ℤ):=Nat.cast_add D D; rw [hs]; exact ψ
private lemma allBound {X:Type*}(f:ℕ→X→ℝ) (t:∀ i,∃ y:ℝ,∀ x,f i x ≤ y) {B:ℝ}(p:∀ᶠ i in atTop,∀ x,f i x≤ B) : ∃ y> (0:ℝ),∀ i x,f i x ≤ y:= by
  obtain ⟨u,h⟩:= eventually_atTop.mp p
  choose y g using t
  let C:= ∑ i∈ Finset.range u, |y i|
  refine ⟨1+(C+|B|),by unfold C; positivity,fun i x=>?_⟩
  apply le_trans _ (le_add_of_nonneg_left zero_le_one)
  by_cases w:i≥ u
  · exact ((h i w _).trans (le_abs_self _)).trans (le_add_of_nonneg_left (sum_nonneg fun i _=>abs_nonneg _))
  exact ((g i _).trans (le_abs_self (y i))).trans ((single_le_sum (f:=fun i=> |y i|) (fun i _ => abs_nonneg _) (Finset.mem_range.mpr (Nat.lt_of_not_ge w))).trans (le_add_of_nonneg_right (abs_nonneg _)))
variable {P} {X:P.Register} {L M:ℝ} {S:Supplier}(v:uniform P X S L M)
include v
/-- These are ACTUAL bounds on this election/data. Hold stencil size
fixed in MICRO-LATTICE units (yet shrink in physical units; price of support
exported separately). Uniform even as width (of these operators) goes to zero!
Only these particular insertions in this theorem. Cannot assume the width
bound uniform for different normalizations, lattice diameters NOT fixed, etc. -/
lemma staticBeam (Z:Lead.Clan)(n:ℕ) : ∃ C>(0:ℝ), ∀ s:ℕ,∀ x:P.Spectrum0 j,
    ‖(P.thinString Z s n).engine P j x‖≤C := by
  obtain ⟨q,d,w,T,c,u,t,e⟩:= v.1.paper
  obtain ⟨a,g,f⟩:= heightGain P.run P.large P.law P.history u.extent
  let B (s):=P.thinString Z s n; let S:= plow κ j ((B 0).u j) (B 0).S; let F:=P.shifts j ((B 0).u j) (B 0).F; have he:InTest κ true S false F.val:=(Tapestry.locates ..).1 (P.shifts_support j _ _ (B 0).bay)
  obtain ⟨y,k⟩:=Journey.valuation P.run P.large he
  obtain ⟨A,d,h,ht⟩:= trans_exists j S
  apply allBound (B:=Real.sqrt (thinStand P.par κ ((B 0).u j+(B 0).u j) d y a)); swap
  · filter_upwards [f] with s b x
    exact apronPermit P j x (P.thinString Z s n) a g b y d A k ht
  intro i
  let W:= (B i).u j + (B i).u j
  let A₀:=P.door j (B i).s W (add_pos ((B i).pos j) ((B i).pos j)) ((B i).cardB P j) ((B i).color P j)
  exact ⟨‖A₀‖,fun x=> NonUnitalStarAlgHom.norm_apply_le (P.colorSpace j x) A₀⟩
end bounds
#print axioms staticBeam
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
