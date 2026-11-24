import YM.SU5.Exchange.Force.Jets
import Merino.Corolla.Curtain
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Dais
open YM.CF.QuadClock
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew Waxy Roots Rive Oise

variable {I:Type}[LinearOrder I][Fintype I]
variable {N P B n:Side}
variable {L:Side}
variable (G:Ratio (mid N B) (mid P B))
variable (X:GramM (mid N B))(Y:GramM (mid P B))
variable (o:I→Site (mid N B))
local notation "FINE" => mid P B
local notation "GRAFT" => mid N B
local notation "vFine" => Hove.heel G ∘ o


def crown {T:Type*}[Add T][Zero T](b:T)(E:Key I→T)(z:Key I):=
  b+if z∈hill I then E z else 0

lemma crowned {T:Type*}[Add T][Zero T](b:T)(E:Key I→T)(z:Key I)(p:z∈hill I):
 crown b E z=b+E z:=by unfold crown; rw [if_pos p]



variable (dMain:Key I→RegBudget (Scree.mid P B))(K:Key I→ForceBudget (Scree.mid P B)){m u:ℕ}
variable {ρ w g h:ℝ} {y:I→ Sour.Firing (Scree.mid P B)}

-- Coupon charges fine arrays w,wovenV w plus the baseline
lemma latched (f:Corolla.Fit Y vFine L w m y h dMain K)
 (d:GapN o X.p.B L.val u) (cost:0≤w)(fee:w≤g)
 (fee':Corolla.wovenV w m≤g)(v:Y.slip=0)
 (paid:Arc_r Y h ρ ρ ρ):
 OrbitPulse G X Y h (ρ+g) g L o (crown Y.F dMain) (crown Y.K K)
    (fun _=>0) (fun _=>w) u:=by
 let H:= crown Y.F dMain; let F:=crown Y.K K
 have plus: ρ ≤ ρ+g:=le_add_of_nonneg_right (cost.trans fee)
 have l:=f.plans
 have v0:H 0=Y.F ∧ F 0=Y.K:=by
    unfold H F
    rw [crowned _ _ _ roots,crowned _ _ _ roots,l.roll.1,l.roll.2,add_zero,add_zero];exact ⟨rfl,rfl⟩
 have hF(i): νTip H i=νTip dMain i:=by
    funext x y; refine (lace_C [i] (f:=fun z=> H z x y) (g:=fun z=>Y.F x y+ dMain z x y) ?_ roots).trans ((tip_A (zeroR _) (river_all (fun z=>dMain z x y) (l.varE _ _)) [i]).trans ?_)
    · exact fun z v=> by dsimp only [H]; rw [crowned _ _ _ v]; rfl
    rw [proper,zero_add]
 have hE(i): emberTip F i=emberTip K i:=by
    funext x y; refine (lace_C [i] (f:=fun z=> F z x y) (g:=fun z=>Y.K x y+ K z x y) ?_ roots).trans ((tip_A (zeroR _) (river_all (fun z=>K z x y) (l.varF _ _)) [i]).trans ?_)
    · exact fun z v=> by dsimp only [F]; rw [crowned _ _ _ v]; rfl
    rw [proper,zero_add]
 change OrbitPulse G X Y h _ _ _ _ H F _ _ _
 refine ⟨?_,d,fun i=> ?_,fun i=> (hF i) |>.symm ▸ f.label i,fun i x u=>?_,fun i x u=>?_⟩
 · constructor
   · exact ⟨v0.1,v.symm,v0.2⟩
   · intro i; refine ⟨fun c a b t x=>?_,fun _ _ _ _ _=>rfl,fun x=> ⟨(dub_V (zeroR (Y.F i x)) (river_all (fun z=>dMain z i x) (l.varE _ _))).cong (fun c a=>?_), zeroR _⟩⟩
     · dsimp only; unfold H
       rw [crowned _ _ _ a,crowned _ _ _ t,Pi.add_apply,Pi.add_apply]
       exact congrArg (Y.F i + ·) (l.col i c b x)
     change H c i x= _
     unfold H; rw [crowned _ _ _ a]; rfl
   · intro i; refine ⟨fun c a b t x=>?_,fun x=> (dub_V (zeroR (Y.K i x)) (river_all (fun z=>K z i x) (l.varF _ _))).cong (fun c a=>?_)⟩
     · dsimp only; unfold F; rw [crowned _ _ _ a,crowned _ _ _ t,Pi.add_apply,Pi.add_apply]
       exact congrArg (Y.K i+·) (l.joinF i c b x)
     change F c i x=_
     unfold F; rw [crowned _ _ _ a]; rfl
   intro z; constructor
   · change IncX primeU (H z) Y.p h (ρ+g)
     by_cases t:z∈hill I
     · have body:∀i,‖z i‖≤2:=fun i=>(hill_i.mp t i).trans (by norm_num)
       rw [show H z=Y.F+dMain z from crowned _ _ _ t]
       exact Provides.liftE h Y _ _ (Larch.add_v _ _ _ paid.1 (f.lease z body).1)
           (by linarith only [fee'])
     unfold H crown; rw [if_neg t,add_zero]
     exact Provides.liftE h Y _ _ paid.1 plus
   · change IncX primeU 0 Y.p h (ρ+g)
     rw [←v]; exact Provides.liftE h Y _ _ paid.2 plus
   change Dark primeU (F z) Y.p h (ρ+g)
   by_cases t:z∈hill I
   · have body:∀i,‖z i‖≤2:=fun i=>(hill_i.mp t i).trans (by norm_num)
     rw [show F z=Y.K+K z from crowned _ _ _ t]
     exact Provides.liftQ h Y _ _ (union_F _ paid.3 (f.lease z body).2)
         (by linarith only [fee])
   unfold F crown; rw [if_neg t,add_zero]
   exact Provides.liftQ h Y _ _ paid.3 plus
 · refine ⟨⟨cost,fee⟩,?_,?_,?_⟩<;> simpa using cost.trans fee
 · rw [hF i,v0.1]
   unfold H; rw [crowned _ _ _ (realKey_mem i x u),(l.head i (x:ℂ)).1,Complex.coe_smul]
 · rw [hE i,v0.2]
   unfold F; rw [crowned _ _ _ (realKey_mem i x u),(l.head i (x:ℂ)).2,Complex.coe_smul]
