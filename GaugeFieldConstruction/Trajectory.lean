import YM.SU5.Six.Elected

-- precise regulator indices
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
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
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
/-!
Six-channel experiment: one character with all purchases, on an actual
Supplied physical Spine. Use the EXISTING Prototype.summit. No hypotheses
from a fixed-stencil alternative election (or a purported rotation guarantee).
The prefix chosen to prove the movement theorem here need not also solve other
tasks, e.g. the Glass co-election or Microcollapse of the source manuscript.
-/
namespace Spine

/-! # diagonal schedule used in physical stress and limiting kernels
keeps ONLY regulators on the single Period/Cutoff pledge. In particular the left hand side in terminal_beta is from these pairs, recommends no off-path at fixed cutoff. -/
variable (P:Spine)
abbrev diagonalᵢ := P.period ∘ P.projection.rows
abbrev diagonalₖ := P.cutoff ∘ P.projection.columns
local notation "I"=> P.diagonalᵢ
local notation "Kq"=> P.diagonalₖ
local notation "Λ"=> P.par
private abbrev periodMark(t:ℕ):=P.run.ir (P.diagonalᵢ t)
abbrev diagonalDepth:= P.run.uv ∘ Kq
local notation "δ"=> P.diagonalDepth

lemma di_i : StrictMono I:= P.law.pick.grow_i.comp P.history.growsA
lemma di_k : StrictMono Kq:= P.law.pick.grow_k.comp P.history.growsB
lemma whole_infinity : Tendsto (fun r=> (P.run.ir (I r)).val) atTop atTop:= P.run.ir_grows.tendsto_atTop.comp P.di_i.tendsto_atTop
lemma stair_infinity : StrictMono δ:= P.run.uv_grows.comp (P.di_k)
lemma helmet (r): (P.run.ir (I r)).val^5 ≤ δ r:= P.history.gate r
lemma pays_at (s:ℕ) : ∀ᶠ t in atTop,(P.run.voyage (I t)).kick ≤ Kq t ∧ s≤δ t:= (P.history.finance s).mono fun r p=>⟨p.depth,p.enters⟩

abbrev barePrescription(n:ℕ):ℝ:=if h:∃ r:ℕ,δ r=n then
 let r:= Classical.choose h
 (((P.run.voyage (I r)).X n).gram n).beta
 else P.par.x
-- only asserted on path; witnesses P convenience
lemma scheduled (r):P.barePrescription (δ r)=(((P.run.voyage (I r)).X (δ r)).gram (δ r)).beta:=by
 let e : ∃ i:ℕ, δ i = δ r:= ⟨r,rfl⟩; unfold barePrescription; rw [dif_pos e]; dsimp only; exact congr_arg (fun n=> (((P.run.voyage (I n)).X (δ r)).gram (δ r)).beta) (P.stair_infinity.injective (Classical.choose_spec e))
lemma input_bare (r) (z:Orbit (Journey.side P.run (I r) (δ r))):
 denZ (((P.run.voyage (I r)).X (δ r)).gram (δ r)) P.par.U ((P.run.voyage (I r)).CapeT (δ r)) z=
      Vale.capP (K:=P.par.K) P.par.U (P.barePrescription (δ r)) (P.run.meter.a (δ r)) z.1:= by rw [P.scheduled]; exact P.bare_density (I r) (Kq r) z

lemma evolves_to_schwinger (F:P.Test) (s:ℕ):
 Tendsto (fun r : ℕ=> Journey.sharp P.run P.large s (I r) (Kq r) F.val) atTop (𝓝 (P.E s F.val)):=by
 let Kt:= P.calibration
 obtain ⟨T,h⟩:=findsBay Kt F
 obtain ⟨c,p⟩:= Journey.valuation P.run P.large h
 let v:= |c|+1; have htP : pay F.val v:= fun i j=> (p i j).trans ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)); have hp:0<v:= lt_add_of_le_of_pos (abs_nonneg c) zero_lt_one
 obtain ⟨C,hC,H⟩:=P.history.implements s T
 apply Metric.tendsto_nhds.mpr
 intro ε e
 filter_upwards [H (ε/2/v) (div_pos (half_pos e) hp)] with r Hq
 rw [dist_eq_norm]; apply lt_of_le_of_lt (Hq F.val h v htP).2.2.2.2.1 _
 rw [div_mul_cancel₀ _ hp.ne']; exact half_lt_self e

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
