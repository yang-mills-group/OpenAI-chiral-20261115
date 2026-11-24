import Gingham.Linen.Down
import Gingham.Ruff.Fascinator
import Gingham.Ruff.Diadem
set_option autoImplicit false
set_option quotPrecheck false
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
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

namespace Preparation
open FullBill Window Marks
open Pitching Focus QuadClock
variable {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}(Y:Course P F)

open Gingham.Ruff

local notation "Ω" i:max s:max => cell (Y.ir i) P.block P.R.L s
local notation "XP" i:max k:max s:max => RootBook Y i k s
lemma tasted (s i k:ℕ)(x:s≤Y.uv k) :
    InterestX P.W.C (Ω i s) (XP i k s).J :=
  (((Y.voyage i).X (Y.uv k)).pull.owns s x).taste ▸ ((P.W.arm ..).sound s)

/-- Per regulated course uses (including top for algebra). -/
def Garland (a c:ℝ) (s i k:ℕ):Prop :=
 let N:= Ω i s
 let R:= XP i k s
 Diadem R P.K.j a c P.d ∧ P.U.roundZ≤N.val ∧
   Roof N P.J.k P.J.roomX P.J.n ((Y.voyage i).CapeT s) ∧
   P.J.roomX < P.d

lemma pinning (T:Fascinator P.V P.d)(s i k:ℕ)(x:s≤Y.uv k)(l:T.m≤(Ω i s).val): Garland Y T.a T.cost s i k :=by
 have w:= (Y.voyage i).ownership s
 have v:P.U.roundZ≤(Ω i s).val:= P.J.gran.trans w.size
 refine ⟨?_,v,w.paid,P.J.hr⟩
 let Z:=XP i k s
 have px: InterestX P.W.C (Ω i s) Z.J:= tasted Y s i k x
 have h: Z.J.P.toll P.V.f P.V.g P.V.F1 P.V.F2:= by
   rw [←P.W.h2,←P.W.h4,←P.W.h1,←P.W.h3]
   exact px.leanJ.1
 refine ⟨P.kJ.symm ▸ T.one _ l Z.J.M,T.two _ l Z.J.P h,(P.U.broadness _ v Z.J.M).projection,?_⟩
 intro t b U hJ p hg
 refine ⟨funde_f _ _ _ hJ _ _ (by rw [P.kJ];decide) _ _ (P.V.note.fields_one _ (P.U.needed.trans v)) (hg.shrink P.U.gem),?_⟩

 rw [show princeps _ _= _ from (plume_den Z P.K.j _).2, show princeps _ _= _ from (plume_den Z P.K.j _).2]
 exact peak_f _ (Pec.den_r h) px.ready _ _ _ hJ _

/-- Thus eventually in s, all i,k. -/
def Chaplet : Prop :=
 ∃ a c:ℝ, 0<a ∧ 1≤c ∧ ∀ᶠ s:ℕ in atTop, ∀ (i k:ℕ),
    s ≤ Y.uv k → Garland Y a c s i k


lemma owned_chaplet(f:Fascinated P): Chaplet Y:=by
 obtain ⟨T⟩:= f
 refine ⟨T.a, max T.cost 1,T.pos,le_max_right ..,?_⟩
 filter_upwards [eventually_ge_atTop T.m] with s h i k t
 have x:T.m≤(Y.ir i * P.R.L ^ s).val:=
   le_trans (h.trans (Vale.huge _ (show 2≤P.R.L.val from (by have z:=P.V.tallX; omega)) _)) (Nat.le_mul_of_pos_left _ (Y.ir i).property)
 obtain ⟨p,q⟩:= pinning Y T s i k t (x.trans ((Nat.le_mul_of_pos_right _ two_pos).trans (Nat.le_mul_of_pos_right _ P.block.property)))
 exact ⟨⟨p.lead.books (le_max_left ..),p.silk.books (le_max_left ..),p.pure,p.step⟩,q⟩
#print axioms owned_chaplet
