import GaugeFieldConstruction.Jung
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 55000
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
open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Eire Girt
open VolumeRate
namespace Pitching
open Vow Bake Larch
namespace Focus
open Neon
open Mew Vow Rive Roots
open scoped YM.CF.Mew
namespace CoeffArc
section
open Py.Riant Larch
variable {I:Type}[LinearOrder I][Fintype I]{N B:Side}{a h w ε:ℝ} {Y:GramM (mid N B)}
variable (V:Finset I→ RegBudget (mid N B))(U:Finset I→ForceBudget (mid N B)) (x:I→Seat (mid N B))(hq:Y.slip=0)(v:0<h)(u:0≤w)(pe:0≤ ε)(e:IncX primeU Y.F Y.p h a)(p: Dark primeU Y.K Y.p h a)(pH:a+w≤ ε)(sv:Journal1 Y.p v x V U (5/4) 1 w)(z:Y.p.supportExponent=1)(T:Y.p.power=2)
include hq v u pe e p pH sv z T
local notation "Eχ"=> Flank_P x V Y.F
local notation "Fχ"=> Flank_K x U Y.K
lemma Cat_P : Call_H (Y:=Y) h Eχ (0:Key I→RegBudget (mid N B)) Fχ x ε ε ε:=by
 have he(z:Key I)(h:z∈hill I): Eχ z= Y.F+ WritV x V z:=by unfold Flank_P CurtainP; rw [if_pos h]
 have hu(z:Key I)(h:z∈hill I): Fχ z= Y.K+WritV x U z:=by unfold Flank_K CurtainK; rw [if_pos h]
 let X:=SecX (KeyUp Y.p) v.le (mid N B); let K:= SecK Y.p v.le (mid N B)
 have hp:Y.p.supportExponent ≤ 5/4:=by rw [z]; norm_num
 have hf(t:Key I): ShelfK X (CurtainP x V t) Y.p.B Y.p.supportExponent w∧ ShelfK K (CurtainK x U t) Y.p.B Y.p.supportExponent w:=by
    unfold CurtainP CurtainK; split
    · next h'=>
       exact ⟨Shelf_roll _ (SB_eval (X:=X) sv.fil t (hill_i.mp h')) hp,Shelf_roll _ (SB_eval K sv.high t (hill_i.mp h')) hp⟩
    exact ⟨Shelf_sal _ (Shelf_zero _ (fun _ _ _=>rfl)) u, Shelf_sal _ (Shelf_zero _ (fun _ _ _=>rfl)) u⟩
 constructor
 · rw [he 0 roots,hu 0 roots,ArcU_value,ArcU_value,sv.root.1,sv.root.2,add_zero,add_zero,hq]; exact ⟨rfl,rfl,rfl⟩
 · intro i; refine ⟨fun z v' u h g=>?_,fun _ _ _ _ _=>rfl,fun U'=>?_⟩ -- tune
   · funext A; dsimp only; rw [he z v',he u h]; simp only [Pi.add_apply]; congr 1; exact (W_silk _ _ sv.rite i A trivial).1 z v' u h g
   refine ⟨?_,zeroR _⟩; apply River.cong (dub_V (zeroR (Y.F i U')) ((W_silk _ _ sv.rite i U' trivial).2)); intro j h; exact congrFun (congrFun (he j h) i) U'
 · intro i; refine ⟨fun z w g h v'=>?_,fun u=>?_⟩
   · funext u; dsimp only; rw [hu z w,hu g h]; simp only [Pi.add_apply]; congr 1; exact (W_silk _ _ sv.right i u trivial).1 z w g h v'
   apply River.cong (dub_V (zeroR (Y.K i u)) ((W_silk _ _ sv.right i u trivial).2)); intro j h; exact congrFun (congrFun (hu j h) i) u
 intro j; let A:=thawE _ v.le (hf j).1 T; let V':=thawK _ v.le (hf j).2
 have t:= add_v _ _ _ e A; have g:= union_F _ p V'; have hx:(IncX primeU (0: RegBudget (mid N B)) Y.p h ε):=by
    refine ⟨⟨0,fun i=> Vale.rinse ..,fun i=>?_⟩,fun i s=>s.elim⟩; exact le_trans (b:=0) (le_of_eq (Finset.sum_eq_zero fun i v=>by split; simp [BudgetPoint.mass]; rfl)) pe -- tune
 refine ⟨?_,hx,?_⟩; · obtain ⟨T,h,f⟩:= t.weight; exact ⟨⟨T,h,fun i=>(f i).trans pH⟩,fun i p=>p.elim⟩
 obtain ⟨T,h,f⟩:= g.weight; exact ⟨⟨T,h,fun i=>(f i).trans pH⟩,fun i p=>p.elim⟩
omit hq v u pe e p pH sv z T
lemma tip_X (F: RegBudget (mid N B))(i:I): νTip (Flank_P x V F) i= V {i}:=by
 funext j y; let A(t:Finset I):=V t j y; let G:= Fluid x A; have hp:Set.EqOn (fun z=>Flank_P x V F z j y) (fun z=>F j y+G z) (hill I):=by
    intro u h; dsimp only; unfold Flank_P CurtainP; rw [if_pos h]; simp only [Pi.add_apply,WritV,Finset.sum_apply]; rfl
 have ht:River G:= (tip_bank _ (fun v z=> Mew.pine v z • A v) (fun i _=>lift_b i _)).1
 change tipI _ [i]= _; rw [show tipI _ [i]=tipI _ [i] from (lace_C [i] hp roots),tip_A (zeroR _) ht,proper,zero_add]; exact (Fluid_p x A (s:=[i]) (by simp [ψS])).trans (congrArg A (by simp))
lemma Arena_shift {C:Scree.Hub (mid N B)→ℝ}{S:RegBudget (mid N B)} {P:BudgetPoint}{q:Seat (mid N B)} {m a:ℝ}(p:ArenaC P S q C w h a)(v:m≤w): ArenaC P S q C m h a:=⟨p.fits,(sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right v (Nat.cast_nonneg _))) (p.paid i))).trans p.bill,p.paid,p.off⟩
lemma Arena_book {C:Scree.Hub (mid N B)→ℝ}{S:RegBudget (mid N B)} {P:BudgetPoint}{q:Seat (mid N B)} {a:ℝ}(p:ArenaC P S q C w h a)(v:0 ≤h) : ShelfK (SecX (KeyUp P) v (mid N B)) S P.B w a:=⟨C,p.fits,fun i=> (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun j _ _=>mul_nonneg (Real.exp_pos _).le (p.paid _))).trans p.bill⟩ -- unused I.F.Resolve
end
end CoeffArc
end Focus
end Pitching
end YM.CF.Py.Rate
end
