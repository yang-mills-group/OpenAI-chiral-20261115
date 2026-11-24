import GaugeFieldConstruction.«ProustΘ3»
import GaugeFieldConstruction.Barrera4
import GaugeFieldConstruction.Photon3
import GaugeFieldConstruction.Sommar
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 100000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Ivey
open Sault Leaf Sour
open Ladder3 Drapes Tenant Palot Rue Iona
attribute [local instance] loreM loreN
variable {n: Side}{I α β γ G:Type}[LinearOrder I][Fintype I][Fintype α][Fintype β][Fintype γ]
-- old bank
namespace ShoreQ
open Tuner
namespace Argos
open XGarden.MastTin
set_option linter.unusedTactic false
open Rio Iona Isle Py Ione Urn Broc Levier Salt
section
open XGarden XGarden.Shield SliceRoof Nacre
open Rio Iona Isle Py Ione Urn Broc Levier Salt Haro
variable {n:Side}(V:Sweep n) {d a c a' b t:ℝ}(k:ℕ)(R:Loom n)(F:Elm n Unit d a c)(H:Elm n Unit d a' b)
variable (p:pure_Rim F)(y:groupShape F)(u:Roof n t d k R)(s:groupShape H)(v:0<d)(Y:Orbit n)(l:Injective (priorP Y.2))
local notation "G"=> orbit4 V
local notation "A"=> actY V
local notation "Ω"=> arm4 V
noncomputable def xv3 : Equiv.Perm (Support (More n)):= Equiv.finsetCongr (boxA V).symm
noncomputable def vsp3 :Equiv.Perm (SP3 n):= Equiv.optionCongr (xv3 V)
noncomputable def vps3:Equiv.Perm (L3 n):= Equiv.prodCongr (vsp3 V) (vsp3 V)
lemma xv3_apply (x:Support (More n)) : xv3 V x=actY V x:=rfl
local notation "sa"=> (boxA V).symm
lemma wCTurn (x:Seat n):Pach (sa x)=actY V (Pach x):=by unfold Pach; rw [←walkA]; unfold actY; rw [map_singleton]; rfl -- tune local binder
variable (o:Seat n)
lemma vup_p (z:SP3 n): vsp3 V z=actX3 V z:=by cases z<;>rfl
lemma vup (z:L3 n): vps3 V z=upX3 V z:=Prod.ext (vup_p V z.1) (vup_p V z.2)
lemma zone_M3 (z:L3 n): orbit4 V (pack3 k o z)= pack3 k ((boxA V).symm o) (upX3 V z):=by
 apply Subtype.ext; apply Prod.ext; exact (stamp4 V).center _
 rw[z_spec]; have ht(x:SP3 n):actY V (limbM k x)=limbM k (actX3 V x):=by rcases x with _|x; exact map_empty _; exact (walkA V _ _).symm
 change actY V (Pach o∪ (limbM k z.1 ∪ limbM k z.2))= Pach (sa o) ∪ _; rw[wCTurn]; unfold actY; simp only [Finset.map_union]; exact congrArg (fun i=> actY V (Pach o)∪i) (congrArg₂ (·∪·) (ht _) (ht _)) -- tune Port R
lemma tripΩ (z:L3 n): warmMode (sa o) (upX3 V z) ↔ warmMode o z:=by
 have hx(x:SP3 n): imply3 (sa o) (actX3 V x) ↔ imply3 o x:=by
    rcases x with _|p; exact Iff.rfl
    change ¬Disjoint _ (actY V p) ↔ ¬Disjoint _ _; rw [wCTurn,joint_m]
 exact and_congr (hx z.1) (hx z.2)
open XGarden.MastTin Thera Nacre Hest
variable (P:BudgetPoint)(Z Z':Paper n)(x:L3 n)
include y p l u v
abbrev ShiftL (P P':Paper n)(x:Pane n): Prop:= αLines P' (flashA V x)= steerZ (launchZ V) V.charge (detX V.s) (αLines P x)
variable (g:ShiftL V Z Z' Y.1)
local notation "Hp"=> ArchQ F R k t
local notation "O"=> MealD H R k t
local notation "Yp"=> twistW' V Y
-- raw issue scope.l.Glyph
include g
lemma PoseT3 (S:Support (More n)):
 lotR3 V ((ArchQ F R k t P o x Z).issue S Y)=(ArchQ F R k t P ((boxA V).symm o) (vps3 V x) Z').issue (actY V S) (twistW' V Y):=by
 rw[vup]; unfold ArchQ; dsimp only
 have hv: Disjoint (Pach ((boxA V).symm o)) (actY V S) ∧ warmMode ((boxA V).symm o) (upX3 V x) ↔ Disjoint (Pach o) S∧ warmMode o x:=and_congr (by rw [wCTurn,joint_m]) (tripΩ V o x)
 by_cases h:Disjoint (Pach o) S ∧ warmMode o x; · simp only[if_pos (hv.mpr h),if_pos h]; rw [show αLines Z' Yp.1= _ from g]; exact Riderq3 F R k t S Y u v x V p y l (αLines Z Y.1)
 rw [if_neg h,if_neg (mt hv.mp h)]; exact map_zero _ -- tune map_zero binder arg. macro dot.
omit g y p
include s
lemma pave_q3 (x i:Support (More n)) : (MealD H R k t).issue (xv3 V i) (actY V x) (twistW' V Y)= suit_Y V ((MealD H R k t).issue i x Y):=by
 let U:= launchZ V; let q:= V.charge; let r:=detX V.s; let F':= uplift H R k x i t Y
 change boat (uplift H R k _ (actY V i) t (flashA V _,bun V Y.2))= paintR q r U (boat F'); rw[sailR]; rw[show uplift H R k (actY V x) (actY V i) t (flashA V _,bun V Y.2)= realR V true F' from lift_move u v V l s]; rfl
omit l s
lemma pave_q0 (x:Support (More n))(i:Ids n):(MealD H R k t).issue x ∅ (Y.1,i)= (MealD H R k t).issue x ∅ Y:= congrArg boat ((lift_empty (T:=i) (F:=H) (U:=Y) (S:=x) u v).symm)
lemma aptP0 (j:Ids n) :(ArchQ F R k t P o x Z).issue ∅ (Y.1,j)=(ArchQ F R k t P o x Z).issue ∅ Y:=by
 unfold ArchQ; dsimp only; split_ifs
 · have h(w:Support (More n)): Elev F R k t ∅ Y w= Elev F R k t ∅ (Y.1,j) w:=by unfold Elev χH gainH giftH; rw [lift_empty (T:=j) (F:=F) (U:=Y) (S:=w) u v]
   change wax (αLines Z Y.1) _ _= _; rw [← funext h]
 rfl
omit u v
lemma vWhite (D:Support (More n)):Sector univ false ((ArchQ F R k t P o x Z).issue D Y):=by
 let f:= Elev F R k t D Y
 have ht(i:LeanV (Single n))(p:SP3 n): Sector univ true (pinMode f p i):=by
    rcases p with _|p; exact Sector.up _ (mem_univ _); exact Fock.Sector.sumS _ _ (fun j _=> (Fock.Sector.down _ (mem_univ _)).scale _)
 change Sector _ _ (((if Disjoint (Pach o) D ∧ warmMode o x then _ else 0):Orbit n→ FC (Dwell n)) Y); split; swap; · exact Fock.Sector.zero _
 change Sector _ _ (wax (αLines Z Y.1) x f); unfold wax; apply Sector.sumS; intro i _; apply Sector.scale; rcases i with _|⟨i,j,y⟩; · change Sector _ _ (if τPure x then 1 else 0); split; exact Sector.one; exact Sector.zero _
 exact (ht _ _).mul (ht (!i,y) _) -- tune
#print axioms tripΩ
#print axioms pave_q3
#print axioms PoseT3
#print axioms vWhite
end
end Argos
end ShoreQ
end Ivey
end YM.CF.Scree.Ing
end
