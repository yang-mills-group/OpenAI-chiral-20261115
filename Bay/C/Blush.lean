import Bay.C.Garb
import SatinThinScroll
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Bay.C
open QuadClock
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




section
variable {I: Type}[Fintype I][LinearOrder I]
variable {N P B:Side}
 {X:GramM (mid N B)} {Y:GramM (mid P B)} {G:Ratio (mid N B) (mid P B)}
 {σ:I→Site (mid N B)} {L:Side}
 {E:Key I→RegBudget (mid P B)}{F:Key I→ ForceBudget (mid P B)}
 {b g r h A:ℝ}{M:ℕ}

abbrev CropE (Y:GramM (mid P B))(E:Key I→RegBudget (mid P B))(z:Key I) := Y.F + dampE E z
abbrev CropF (Y:GramM (mid P B))(F:Key I→ForceBudget (mid P B))(z:Key I) := Y.K + dampE F z
local notation "Λh"=>Key I
local notation "Yo"=> CropE Y E
local notation "Yy"=> CropF Y F

lemma blush
 (y:Receives Y.p L.val (Cube.node ∘ Hove.heel G ∘ σ) E F h A)(a0:0≤A)
 (street:Y.slip=0)(p:Arc_r Y h r r r)
 (e:A≤g)(h0:r+A ≤ b)
 (m:GapN σ X.p.B L.val M):
 OrbitPulse G X Y h b g L σ Yo Yy 0 (fun _=>A) M ∧ ∀i, νTip Yo i=νTip E i ∧ emberTip Yy i=emberTip F i:=by
 obtain ⟨_,_,l,j,u⟩:=y
 let E':= dampE E; let F':= dampE F; have he(z:Λh)(u:z∈hill I): E' z = E z∧ F' z= F z:= ⟨if_pos u,if_pos u⟩
 let H(z:Λh):= Y.F+E' z; let H'(z:Λh):= Y.K+F' z
 have v0:H 0=Y.F ∧ H' 0=Y.K:=by unfold H H'; rw [(he _ roots).1,(he _ roots).2,l.roll.1,l.roll.2]; simp
 have hF(i): νTip H i=νTip E i:=by
    funext x y; refine (lace_C [i] (f:=fun z=> H z x y) (g:=fun z=>Y.F x y+ E z x y) ?_ roots).trans ((tip_A (zeroR _) (river_all (fun z=>E z x y) (l.varE _ _)) [i]).trans ?_); · exact fun z v=> by dsimp only [H]; rw [(he z v).1]; rfl
    rw [proper,zero_add]
 have hE(i): emberTip H' i=emberTip F i:=by
    funext x y; refine (lace_C [i] (f:=fun z=> H' z x y) (g:=fun z=>Y.K x y+ F z x y) ?_ roots).trans ((tip_A (zeroR _) (river_all (fun z=>F z x y) (l.varF _ _)) [i]).trans ?_); · exact fun z v=> by dsimp only [H']; rw [(he z v).2]; rfl
    rw [proper,zero_add]
 have hb :r≤b:=(le_add_of_nonneg_right a0).trans h0
 have hu(v:Key I)(t:v∈hill I):∀i,‖v i‖ ≤2 := fun i=>((hill_i.mp t) i).trans (by norm_num)
 have hx : 0≤g:= a0.trans e
 refine ⟨⟨?_,m,fun i=> ?_,fun i=> (hF i).symm ▸ (j i).axon,fun i x u=>?_, fun i x u=>?_⟩,fun i=>⟨hF i,hE i⟩⟩
 · constructor
   · exact ⟨v0.1,street.symm,v0.2⟩
   · intro i; refine ⟨fun c a b t x=>?_,fun c a b t x=>rfl,fun x=> ⟨(dub_V (zeroR (Y.F i x)) (river_all (fun z=>E z i x) (l.varE _ _))).cong (fun c a=>?_), zeroR _⟩⟩
     · change (Y.F+ E' c) _=(Y.F+E' b) _; rw [(he c a).1,(he b t).1,Pi.add_apply,Pi.add_apply]; exact congrArg (Y.F i + ·) (l.col i c b x)
     change (Y.F+E' c) i x= _; rw [(he c a).1]; rfl
   · intro i; refine ⟨fun c a b t x=>?_,fun x=> (dub_V (zeroR (Y.K i x)) (river_all (fun z=> F z i x) (l.varF _ _))).cong (fun c a=>?_)⟩
     · change (Y.K+ F' c) _=(Y.K+F' b) _; rw [(he c a).2,(he b t).2,Pi.add_apply,Pi.add_apply]; exact congrArg (Y.K i+·) (l.joinF i c b x)
     change (Y.K+F' c) i x=_; rw [(he c a).2]; rfl
   intro z; constructor
   · by_cases t:z∈hill I; · change IncX primeU (Y.F+ E' z) Y.p h b; rw [(he z t).1]; exact Provides.liftE h Y _ _ (Larch.add_v _ _ _ p.1 (u z (hu z t)).1) h0
     change IncX _ (Y.F+ E' z) _ _ _; rw [show E' z=0 from if_neg t,add_zero]; exact Provides.liftE h Y _ _ p.1 hb
   · change IncX primeU 0 Y.p h b; rw [←street]; exact Provides.liftE h Y _ _ p.2 hb
   by_cases t:z∈hill I; · change Dark primeU (Y.K+ F' z) Y.p h b; rw [(he z t).2]; exact Provides.liftQ h Y _ _ (union_F _ p.3 (u z (hu z t)).2) h0
   change Dark _ (Y.K+ F' z) _ _ _; rw [show F' z=0 from if_neg t,add_zero]; exact Provides.liftQ h Y _ _ p.3 hb
 · change Sized_J A g _ _ 0
   exact ⟨⟨a0,e⟩, by simp; exact hx,by simp; exact hx,by simp; exact hx⟩
 · have he0:=realKey_mem i x u; change Y.F+E' _= H 0+_ • νTip H i; rw [(he _ he0).1,hF i,v0.1,(l.head i (x:ℂ)).1, Complex.coe_smul]
 · have he0:=realKey_mem i x u; change Y.K+F' _= H' 0+_ • emberTip H' i; rw [(he _ he0).2,hE i,v0.2,(l.head i (x:ℂ)).2,Complex.coe_smul]
