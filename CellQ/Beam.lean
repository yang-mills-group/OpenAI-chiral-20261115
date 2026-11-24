import CellQ.Unison
import CellQ.Dial
import Prism.Sums
import CellQ.Circuit
import Taffeta.Quote
import YM.SU5.FiniteGaugeData.Pannier.Sketch
set_option autoImplicit false
set_option maxHeartbeats 800000
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
open Ione Beau Haro Cascade Fief VolumeRate
open Roots Buffered Dyad Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
namespace Kona
open Drift Grain Graph
open CF.Neon
variable {I:Type}[LinearOrder I][Fintype I]{m B:Side}
local notation "Sα"=>mid m B
local notation "QK"=>Mew.Key (PairKey I)
local notation "Pk"=>PairKey I
variable {f:QK→ℂ}{r b:ℝ}
lemma tip_costK (h:1≤r)(g:QK→ℂ)(hp:River (fun y:QK=>g ((r:ℂ) • y)))(w:∀ i∈hill Pk, ‖g ((r:ℂ) • i)‖ ≤ b)(s:List Pk): ‖tipI g s‖≤ r⁻¹^s.length*b:=by
 let c:= (r:ℂ); have hr:0<r:=zero_lt_one.trans_le h; have hc:0<‖c‖:=by unfold c; simpa only [Complex.norm_real,Real.norm_of_nonneg hr.le] using hr
 let f(y:QK):=g (c • y); have hx: g= fun y=>f (Grain.dilate c⁻¹ y):=by funext y; unfold f Grain.dilate; rw [←mul_smul,mul_inv_cancel₀ (norm_pos_iff.mp hc),one_smul]
 let A:=r⁻¹; have hA:‖c⁻¹‖=A:=by unfold A c; simp only [norm_inv,Complex.norm_real,Real.norm_of_nonneg hr.le]
 rw [hx,tip_dial (by rw [hA]; exact inv_le_one_of_one_le₀ h) hp,norm_smul,norm_pow,hA]; exact mul_le_mul_of_nonneg_left (lance_bound hp s w 0 Mew.roots) (pow_nonneg (inv_pos.mpr hr).le _)

variable {K:Teller SU.group}{Rp:Patch}{L1:ChartRatio SU.group} {V:Grace K Rp L1}{e h:ℝ}{U:Grasp V.U B e}{G:Scree.Loom (mid m B)}
variable (T:Log I (mid m B))(o:I→ Site (mid m B))(R:GramM (mid m B))(h a b:ℝ) (L0:Side)(F:Bool→ArcΦ)(H:Clinic o T 1 h a b R L0 F)
private def varied (T:Log I (mid m B))(r:ℝ):Log I (mid m B):=⟨fun z=>T.earn ((r:ℂ) • z),fun z=> T.wake ((r:ℂ) • z)⟩
private lemma pulse_grain {E:Type*}[AddCommGroup E][Module ℂ E]{g:Mew.Key (PairKey I)→E}{D:Finset I}(h:Grain D g)(r:ℝ):Grain D (fun z=>g ((r:ℂ) • z)):=by
 let f(a b:Bool):ℂ:= if a=b then (r:ℂ) else 0
 convert! h.precomp f using 1; funext i; apply congrArg g; funext z; rcases z with ⟨z,k|k⟩ <;> simp [f,Drift.fiber,Drift.entry]
include H
lemma tip_beamK (V:Grace K Rp L1) {U:Grasp V.U B e}{G:Scree.Loom (mid m B)}{r C:ℝ}(p:1≤r)(z:Orbit (mid m B))(l:List Pk)(Y:∀ u∈hill Pk,‖Scree.beamZ (mid m B) (Graph.recX U (markedB T R ((r:ℂ) • u)) G z)‖≤ C): -- should mapped beamZ norm assumption, not vector
    ‖beamZ (mid m B) (Complex.exp (-R.v) • season_Y (Gℓ:=G) (X:=R) (U:=U) V T l z)‖ ≤ r⁻¹ ^l.length*C:=by
 let f(w:QK):=dSign (U:=U) (X:=R) (Gℓ:=G) V T w z
 let L:Phys (mid m B)→L[ℂ] ℂ:= Complex.exp (-R.v) • innerSL ℂ (mateK (mid m B))
 let K':=L ∘ f
 let S:= varied T r
 have he: River f:=allC V o T z H.age.1 H.age.2
 have hp: River (fun w=> K' ((r:ℂ) • w)):= sc_V (show River (fun w=>dSign V S (U:=U) (X:=R) (Gℓ:=G) w z) from allC V o S z (fun i v=>pulse_grain (H.age.1 i v) r) fun i v=>pulse_grain (H.age.2 i v) r) L
 have hW: ‖tipI K' l‖ ≤ _ := tip_costK p K' hp (b:=C) (fun i h=>by specialize Y i h; unfold Graph.recX at Y; unfold Scree.beamZ at Y; rw [inner_smul_right] at Y; exact Y) l -- Y wrong
 suffices beamZ (mid m B) _=tipI K' l by rw [this]; exact hW
 rw [(show tipI K' l=L (tipI f l) from sim_H he L l roots)]
 unfold L beamZ; rw [inner_smul_right]; rfl

end Kona
end YM.CF.Py.Rate
end
