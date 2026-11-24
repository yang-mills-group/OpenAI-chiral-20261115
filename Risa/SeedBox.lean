import Risa.Warehouse
import Rods.Sport
import YM.SU5.Regis.Visitations
import Risa.Hosted
import CellQ.Delight
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask
open BProof CF.Refrain _root_.YM.Gleam.Luster.Risa
open _root_.YM.CF.Lamour.Bridge.Celeste Clock Afterglow Journey
set_option linter.unusedVariables false
variable {n:Side}{I:Type}[Fintype I] (p:BudgetPoint)(y a d:ℝ)(n₀:Bool)(v:Bool→Seat n)(t:Bool→Signed)
abbrev routeOne (r:I→ Bool→Seat n)(s:I→Bool→Signed):Prop:=Route r s v t
abbrev sampleZ (r:I→Bool→Seat n)(s:I→Bool→Signed)(V:Pane n):ℂ:=↑(∑ i:I,a*(raiseX SU.group p y n₀ V (s i) (r i)-d))
structure Seed (I:Type)[Fintype I](p:BudgetPoint)(y a d:ℝ)(n₀:Bool)(v:Bool→Seat n)(t:Bool→Signed) where
 S: Finset (Seat n)
 spa:I→Bool→Seat n
 ort:I→Bool→Signed
 lawful:Route spa ort v t
 inside(i:I)(b:Bool): spa i b∈S
 distinct(b:Bool) : Injective fun i=>spa i b
 covers : AtSupport false S (CalendarQ' (sampleZ p y a d n₀ spa ort))
variable {p y a d n₀ v t}
abbrev Sway(F:Seed I p y a d n₀ v t):=CalendarQ' (sampleZ p y a d n₀ F.spa F.ort)
variable {σ:Axis}{q:ℤ}
lemma mirrorS (F:Seed I p y a d n₀ v t): let s:=Signed.mirror σ; let T:= (wrap (More n) (2 • (q • step σ)))
 (reflMark σ q (Sway F))=(CalendarQ' (sampleZ p y a d n₀ (fun i j=>affine s T (F.spa i j)) (fun i j=> s *F.ort i j))) :=by
 intro k T; funext i
 unfold reflMark Sway CalendarQ' sampleZ
 rw [theta_smul,theta_one,Complex.star_def,Complex.conj_ofReal,show (reflFields σ q i).1= fling σ q _ i.1 from rfl,fling_eq]
 unfold raiseX; simp_rw [solic_pull]; rfl -- tune
noncomputable def flipS (σ:Axis)(q:ℤ)(F:Seed I p y a d n₀ v t): Seed I p y a d n₀ v t where
 S:=hyphen σ q F.S
 spa:= fun i j=> (plane σ q).anon n (F.spa i j)
 ort:=fun i j=> Signed.mirror σ* F.ort i j
 lawful:=curried F.spa F.ort v t F.lawful (Signed.mirror σ) _
 inside:=fun i j=>mem_image_of_mem _ (F.inside i j)
 distinct:=fun b i j g=>F.distinct b ((Sport.anon_inj ..) g)
 covers:=by -- abbrevation pricing
    let X:=F.covers.refl σ q
    change AtSupport false (hyphen σ q F.S) (reflMark σ q (Sway F)) at X; rw [mirrorS (σ:=σ) (q:=q) F] at X -- need change
    exact X
variable {m:Side}(K:Calibration)
def bandSeat {v:Bool→Seat (K.c m)}: Sport K m (K.c m) (Seed I p y a d n₀ v t) where
 place:= Seed.S
 pose:=Sway
 mirror:= fun i z=> flipS i (Heat.gaugeShift K.B z)
 castM:=fun _ z=>z
 stage:=fun i _ F h=>F.covers.mono h
 charge:=fun i z F _=> (mirrorS (σ:=i) (q:=Heat.gaugeShift K.B z) F).symm
 town:=fun _ _ _=>rfl
-- transform sport film into array. general for n with match.
private lemma filmG {T:Type} (V: T→Mark n)(L:List T)(x:Fields n)(z:Fin L.length→ℂ)(h:∀ i,V (L.get i) x=z i • 1):(L.map V).prod x=(∏ i,z i) •1:=by
 induction L with
 | nil=> simp -- tune
 | cons i l ih=>
    rw [List.map_cons,List.prod_cons,Pi.mul_apply, ih (fun j:Fin l.length=>z j.succ) ?_]
    swap; · exact fun j=>h j.succ
    rw [show ∏ j, z j=z 0 *∏ j:Fin l.length, z j.succ from Fin.prod_univ_succ z,show V i x=z 0 • 1 from h 0,Algebra.smul_mul_assoc,one_mul,smul_smul]
open Sport in
lemma scale_Sport {v:Bool→ Seat (K.c m)}(L:List (Seed I p y a d n₀ v t))(h:race (bandSeat K) L): let r:=fun (x:Fin L.length × I)=> (L.get x.1).spa x.2; let s:=fun (x:Fin L.length × I)=> (L.get x.1).ort x.2; Route r s v t ∧ (∀b:Bool,Injective fun i:Fin L.length × I=>r i b) ∧ ∀x:Fields (K.c m),
 film (bandSeat K) L x = (↑(∏ j:Fin L.length, mealSeat SU.group p y r s n₀ a d j x.1):ℂ) • 1 :=by
 intro r s; refine ⟨fun i=>(L.get i.1).lawful _, fun b=> ?_, fun x=>?_⟩
 · intro i j q; let v(p:Fin L.length):= L.get p
   change (v i.1).spa i.2 b=(v j.1).spa j.2 b at q
   have d(u w:Fin L.length)(t:u<w):Disjoint (v u).S (v w).S:=h.rel_get_of_lt t
   have ht:i.1=j.1:=by
      by_contra! p; rcases lt_or_gt_of_ne p with p|p
      · exact disjoint_left.mp (d _ _ p) ((v _).inside i.2 b) (q.symm ▸ (v j.1).inside j.2 b)
      exact disjoint_left.mp (d _ _ p) ((v _).inside j.2 b) (q ▸ (v i.1).inside i.2 b)
   rw [ht] at q; exact Prod.ext ht ((v _).distinct b q)
 rw [Complex.ofReal_prod]; exact filmG _ L x _ (fun i=>rfl)
#print axioms scale_Sport
#print axioms bandSeat
end Papal
end LocalLimit
end Rate
end YM.CF.Py
