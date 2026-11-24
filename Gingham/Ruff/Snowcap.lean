import Gingham.Ruff.Starch
import Gingham.Ruff.Chaplet
import YM.SU5.FiniteGaugeData.Tower.Roomer
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

/-- Half-width in gauge lattice units of the block of (125) is 2u=one ruler. -/
abbrev underlay(P:Preparation): Side:=⟨8*P.block.val,Nat.mul_pos (by decide) P.block.property⟩
open CF.Buffered.Afterglow.Tower.SlabMark
lemma underlay_val(P:Preparation): ruler P.block=(2:ℤ)*(underlay P).val:=by
 change (16:ℤ)*P.block.val=(2:ℤ)*(Nat.cast (8*P.block.val))
 push_cast; ring
local notation "tx"=>hat P.R.L P.x
open CF.Linen

/-- All payments for use of the new kernels from Chaplet and Plumage at actual incidence
 budgets. Prices a,c,μ,d fixed independently of cover exponent E and core multiplier l. -/
structure GlendaleInst (a c μ E:ℝ)(d l s i k:ℕ):Prop where
  boot : Location.Boot ((tx) s) (XP i k s).p
  quills : Quills (frosting (XP i k s).F) (XP i k s).p P.h
    (μ*(1+((XP i k s).p.B:ℝ))^d * (Linen.stiffness P.R.L ((tx) s)))
  zeroSlip : (XP i k s).slip=0
  worn : Garland Y a c s i k
  width : 2*(underlay P).val < (Ω i s).val
  tag : Tagbill a E (underlay P) l P.J.n (XP i k s).p.B
  angular : Briefly (XP i k s).p P.J.n P.d ((Y.voyage i).CapeT s)



def Glendale :=
  ∃ a c μ:ℝ, 0<a ∧ 1≤c ∧ 1≤μ ∧ ∃d:ℕ,
   ∀E:ℝ, 0≤E → ∀l:ℕ,2≤l→ ∀ᶠ s:ℕ in atTop,
     ∀ i k,s<Y.uv k→ GlendaleInst Y a c μ E d l s i k

lemma temper_g (d:ℝ)(t:0<d): ∀ᶠ s:ℕ in atTop,temp ((tx) s) ≤ d:= -- P omitted
  ((show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).comp
   (turnover P)).eventually (ge_mem_nhds t)

lemma width_g(i s:ℕ)(v:2*(underlay P).val<s):
   2*(underlay P).val < (Ω i s).val:=
  v.trans_le (((Vale.huge _ (show 2≤P.R.L.val from by have z:=P.V.tallX; omega) s).trans
  (Nat.le_mul_of_pos_left _ (Y.ir i).property)).trans
   ((Nat.le_mul_of_pos_right _ two_pos).trans (Nat.le_mul_of_pos_right _ P.block.property)))

set_option maxHeartbeats 700000 in
lemma Glendale_paid (v:Plumage Y)(h:Chaplet Y): Glendale Y:=by
  obtain ⟨μ,u,d,q⟩:=v
  obtain ⟨a,c,m,g,t⟩:=h
  obtain ⟨w,z,x⟩:= Rill.cozy 6 P.dpos
  refine ⟨a,c,μ,m,g,u,d,?_⟩
  intro E he l hl
  have A:=Work.E01.radiusB_tendsto.comp (turnover P)
  have B:= tendsto_natCast_atTop_atTop (R:=ℝ) |>.comp A


  filter_upwards [q,t, temper_g (P:=P) w x.peta, temper_g (P:=P) _ P.J.ht,
    A.eventually_ge_atTop (500*(P.J.n+widthL (underlay P)+10)+cipherK P.J.n+3),
    (Tendsto.const_mul_atTop (show 0<a/16 by positivity) B).eventually_ge_atTop
      (42*E*Fief.tileN l), eventually_gt_atTop (2*(underlay P).val)]
    with s q t m1 m2 b1 b2 b3 i k hi
  specialize q i k hi
  specialize t i k hi.le
  obtain ⟨b,qf,n⟩:= q
  have v:500*(P.J.n+widthL (underlay P)+10)+cipherK P.J.n+3 ≤ (XP i k s).p.B:= le_trans b1 b.B.symm.le
  refine ⟨b,qf,n,t,width_g Y i s b3, ⟨m,he,hl,by omega,b.B.symm ▸ b2⟩, P.dpos,
    ⟨P.J.k, b.threshold.le.trans m2, ?_⟩,
    ⟨z,w,b.threshold.le.trans m1,b.order.symm ▸ x⟩,by omega,by omega⟩
  have rf:= t.2.2.1
  exact {rf with paid:= fun x=>(rf.paid x).shrink P.J.hr.le}

#check Cube.Guard.shrink
#print axioms Glendale_paid
