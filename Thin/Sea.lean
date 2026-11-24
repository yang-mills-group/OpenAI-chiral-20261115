import YM.SU5.Fineness.Pleated
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 150000
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
open Eire Girt
open VolumeRate
variable {d:ℝ} {m n N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
variable {A C' Pay h ρ f ff ag Cg x β β' : ℝ} {D : Treaty J q A C' Pay h ρ} {c:Estimate}
variable {w:Location (R:=R) B m n} {p p' : BudgetPoint}
namespace Pitching
namespace Focus.Shop
lemma offsets_exp_th {E:Corr (mid m B)} {F:Corr (mid n B)}{v u u':ℂ}{β ε:ℝ}{g:SpaceM}(L:Launch p p' w U q J.d E F β ε v u g)(L':Launch p p' w U q J.d E F β ε v u' g){N0:ℕ}(t:Location.Request V U W J q w N0 x p p') : Complex.exp u=Complex.exp u':=by
 let V0:Orbit (mid m B):=(1,Classical.arbitrary _); let M:=w.output; let S:=w.coarse; have he : flags p.threshold V0.1=∅:=UVNext.CouplingReset.flags_one _; let P:= V.L.path (w.lag+1); let b:=β+Location.movement V w-ε
 have hv:= congrArg (fun x=> inner ℂ (changeM (m:=m) U (S V0) M.M) x) ((L.wear V0 (clear_identity _)).trans (L'.wear V0 (clear_identity _)).symm)
 let hp:= J.gran.trans t.rocket.size; let hg:= (t.rocket.paid.paid V0).shrink J.hr.le
 change inner ℂ _ (denZ (construct p P K.top.clip M b E u) U S V0)= inner ℂ _ (denZ (construct p P K.top.clip M b E u') U S V0) at hv
 rw [sea_read (m:=m) U P K.top.clip S M E u b V0 he hp hg, sea_read (m:=m) U P K.top.clip S M E u' b V0 he hp hg] at hv
 simp_rw [Complex.exp_add,Complex.exp_sub] at hv
 -- simp cancellations via mul_right_inj' etc
 -- simp [div_left_inj',...]
 simpa [div_eq_mul_inv, Complex.exp_ne_zero] using hv
end Focus.Shop
end Pitching
end YM.CF.Py.Rate
