import Taffeta.Silk
import Rods.Sport
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
open Roots Buffered LocalLimit LocalLimit.Papal Dyad Dyad.Keeping Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
open Buffered Advance Afterglow YM.CF.Pannier.Chancel
namespace Decaf
variable (n:Side)(k:Axis)(s:ℤ)
abbrev shade:Compass.staff n:=⟨tagMove k s n,Compass.allFlips (Signed.mirror k) rfl⟩
lemma ratio_one:Compass.taxK (shade n k s)=1:=by
 change (if Compass.tariffX (Signed.mirror k) then (-1:ℝ) else 1)=_
 rw [Compass.tax_m]; rfl
abbrev center (o:Site n):Site n:=Compass.orbitT (shade n k s) o
lemma monoShade (x:Site (More n)): boxA (tagMove k s n) x = (plane k s).anon n x:=by
 rw [sitA]; change affine (Signed.mirror k) ((assembly n).embed ((wrap n) (s • step k))) x=_; rw [(assembly n).embed_wrap (s • step k)]; rfl -- need unfold tag b type + ? multiplication cast
lemma placing (o:Site n): Cube.node (center n k s o)=(plane k s).anon n (Cube.node o):=by
 let r:= (shade n k s)
 change Cube.node (inspire r.val o)= _; rw [node_inspire]; apply (boxA r.val).injective; rw [Equiv.apply_symm_apply,monoShade,fling_there]
lemma leaseA(o:Site n): lease_H (center n k s o) = Salt.actY (tagMove k s n) (lease_H o):=by
 -- $Glow. verify namespace actY
 have h:=congrArg (fun x:Scree.Hub n=>x.val.2) (rapX (tagMove k s n) o 10)
 exact h.symm
lemma fiscal2(o:Site n)(V:BudgetPoint)(a:ℝ)(F:Pane n): tariffB (center n k s o) V a (Spire.flashA (tagMove k s n) F) = tariffB o V a F:= by
 unfold tariffB
 let r:= shade n k s; let G:=r.val; let O:=center n k s o
 rw [leaseA]
 by_cases p:pingS V.threshold (lease_H o) F; swap; · simp only [if_neg p, if_neg (mt (Salt.glowA _ _ (tagMove k s n) _).mp p)]
 rw [if_pos p,if_pos ((Salt.glowA _ _ (tagMove k s n) _).mpr p), ink_raise a r V,ratio_one,one_mul]
 rw [monoShade,placing,fling_there]
lemma cameo_fold(o:Site n)(V:BudgetPoint)(a:ℝ): cameo (center n k s o) V a = reflMark k s (cameo o V a):=by
 funext z
 unfold cameo reflMark; simp only [reflFields,theta_smul,theta_one];
 congr 1 -- star of real
 have e:= fiscal2 n k s o V a (fling k s n z.1)
 rw [with_tag,fling_invol k s z.1] at e
 rw [e]; dsimp; exact Eq.symm (Complex.conj_ofReal _)
#print axioms cameo_fold
end Decaf
end YM.CF.Py.Rate
end
