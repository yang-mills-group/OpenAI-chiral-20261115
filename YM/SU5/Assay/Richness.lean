import SatinFixedContrastNovember4
import YM.SU5.Assay.Swell
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set Six Ballad
local notation "Zs" => Ballad.Lead.Clan
/-!
 A further comparison: charge connected prices even against
 ordinary product of actual *dressed* individual prices, across
 the separation (no changes to either stance). Use usual oriented
 convention: earlier & later already posed as billed.
-/
namespace Slip
def joins (s:Slip):CrossRead:=Matrix.vecMulVec s.2.1 s.2.2
def tension (s:Slip):CrossRead:=s.1-s.joins
lemma tension_cont : Continuous tension := continuous_fst.sub ((continuous_fst.comp continuous_snd).matrix_vecMulVec (continuous_snd.comp continuous_snd))
lemma tension_mid (v:CrossRead): tension (v,0,0)=v:= by
 have h:joins ((v,0,0):Slip)=0:=by ext1 z w;exact zero_mul _
 unfold tension;rw [h,sub_zero]
/-- Margin on JOINT price determinant and all diagonals. -/
def strong (d:ℝ)(v:CrossRead):Prop:=d<‖v.det‖∧∀z,d<‖v z z‖
lemma strong_alive {d:ℝ}(v:CrossRead)(p:0<d)(h:strong d v):ReadsSix v:=
 ⟨norm_pos_iff.mp (p.trans h.1),fun z=>norm_pos_iff.mp (p.trans (h.2 z))⟩
/-- Strength both gross and net of products. -/
def stronghold (d:ℝ):Set Slip:={v|strong d v.1 ∧ strong d v.tension}
lemma strong_open (d:ℝ):IsOpen {v| strong d v}:=by
 have h(z:Zs):IsOpen {v:CrossRead|d < ‖v z z‖}:=isOpen_lt continuous_const <| ((continuous_apply z).comp (continuous_apply z)).norm
 rw [show {v|strong d v} = {v:CrossRead|d < ‖v.det‖} ∩ ⋂z:Zs,{v:CrossRead|d<‖v z z‖} from by ext; simp [strong]]
 exact (isOpen_lt continuous_const continuous_id.matrix_det.norm).inter (isOpen_iInter_of_finite h)
lemma garrison (d:ℝ): IsOpen (stronghold d):=((strong_open d).preimage continuous_fst).inter ((strong_open d).preimage tension_cont)
lemma rich {v:CrossRead}(u:ReadsSix v):∃d>0,stronghold d∈ 𝓝 ((v,0,0):Slip):=by
 have t:∀ᶠ d in 𝓝[>] (0:ℝ),0<d ∧ strong d v:= by
   have h(z):∀ᶠd in 𝓝[>] (0:ℝ), d < ‖v z z‖ := mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (norm_pos_iff.mpr (u.2 z)))
   have p:∀ᶠd in 𝓝[>] (0:ℝ),0<d:=self_mem_nhdsWithin
   have e:∀ᶠd in 𝓝[>] (0:ℝ),d<‖v.det‖:=mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (norm_pos_iff.mpr u.1))
   exact p.and (e.and (eventually_all.mpr h))
 obtain ⟨d,p,h⟩:= t.exists
 exact ⟨d,p,(garrison _).mem_nhds ⟨h,(tension_mid _).symm ▸ h⟩⟩
end Slip

lemma Fresco.garrison {P:Spine} {R:P.Register}{x:P.Spectrum0 3}{s n:ℕ}{F G:SampleDose}{D N:Doorway}{o:Orders} (p:P.Fresco R x s n D N o F G):
 ∃d>0,Slip.stronghold d∈ 𝓝 (P.frescoLimit x s n (D.turnCut N) F G):=Slip.rich p.paid.poles
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
