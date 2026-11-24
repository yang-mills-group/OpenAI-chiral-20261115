import GaugeFieldConstruction.PaidReading
import GaugeFieldConstruction.VestaΩ
import GaugeFieldConstruction.Lythe
import GaugeFieldConstruction.Virago
import GaugeFieldConstruction.Postmark
import GaugeFieldConstruction.Harries
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 24000
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
open scoped ComplexOrder
variable {N:Side}{K : Teller SU.group}{R:Patch}{L:ChartRatio SU.group}
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
open YM.Gleam
open BProof.PricePort Gleam.clocks

namespace Papal
open scoped YM.CF.Mew
open Fock.Flux Girt TableF TableF.Lenten.Layout Gleam.Guide CF.XGarden CF.XGarden.MastTin ArtCart Zpress ScopeU Buffered
open FrameP
variable (s i k:ℕ)
open Window
namespace FrameP
variable {x v:ℝ}{m:ℕ}{S: Support (More N)}{A:Pane N→FC (Single N)}
lemma pressSector {F:FC (Single N)}(h:pressedF (onPage N S) m v F): Fock.Sector (onPage N S) false F:=by
 obtain ⟨w,h,v,rfl⟩:=h; clear v; let X:=onPage N S
 have hl (y:Creduct (Single N))(e:y.2∈X): Fock.Sector X true (RootBay y):=by
    rcases y with ⟨b|b,y⟩; · change Fock.Sector X true (create _); rw [create_put]; exact Fock.Sector.up _ e
    change Fock.Sector X true (Fock.remove _); rw [remove_take]; exact Fock.Sector.down _ e
 have hv (l:List (Creduct (Single N)))(e:∀ i∈l,i.2∈X): Fock.Sector X (decide (Odd l.length)) (rollC RootBay l):=by
    induction l with
    | nil=> exact Fock.Sector.one
    | cons i l ih=>
       let p:Bool:= decide (Odd l.length)
       have h:= ((hl i (e i (by simp))).mul (ih (fun i v=> e i (List.mem_cons_of_mem _ v))))
       have he:Odd (i::l).length↔ ¬Odd l.length:=by simp only [List.length_cons, Nat.odd_add]; simp
       have hp:true.xor p=decide (Odd (i::l).length):=by
          unfold p; by_cases t:Odd l.length; · rw [decide_eq_true t,decide_eq_false (fun e=>he.mp e t)]; rfl
          rw [decide_eq_false t,decide_eq_true (he.mpr t)]; rfl
       exact hp ▸ h
 induction w with
 | nil=> exact Fock.Sector.zero false
 | cons i l ih=>
    obtain ⟨p,_,v⟩:= h i (by simp)
    have t:=hv i.2 v; have hx:¬Odd i.2.length:= Nat.not_odd_iff_even.mpr p; rw [decide_eq_false hx] at t; exact (Fock.Sector.scale t _).add (ih (fun i p=>h i (List.mem_cons_of_mem _ p))) -- tune

def spunA (i:Axis)(s:ℤ)(A:Pane N→FC (Single N)): Pane N→ FC (Single N) := fun x=> theta (carR i s N) (A (fling i s N x))
lemma UprightR(p:Upright N S v m A)(i:Axis)(s:ℤ):Upright N (S.image ((plane i s).anon N)) v m (spunA i s A):=by
 let q:=plane i s; let R:=carR i s N
 refine ⟨Girt.pole_w (fun x:Pane N=> A (fling i s N x)) (theta R) (theta_cont R) (Girt.snap p.face (fling_cont ..).measurable), fun y V=>?_,fun x=> Lifted.turn_press i s (p.holds _)⟩ -- tune Env
 unfold spunA; rw [show fling i s N (Lattice.gauge V y)= _ from van q V y, p.gauge]; exact theta_twist_right _ _ _ (congrArg Subtype.val (Lifted.gaugeSquare i s N V)) (pressSector (p.holds _)) -- tune
open Guide
local notation "N'"=> count Y s i
variable {f F : Pane (count Y s i) → FC (Single (count Y s i))} {H Q:Support (More (count Y s i))}{B:Bool}
-- no translation loss in these claims; keep **affine** ability of any part.
def LongBand (s i k:ℕ)(A A': Pane (count Y s i)→FC (Single (count Y s i)))(S S':Support (More (count Y s i)))(c:Bool):Prop:=
    ∀ (q:Signed)(p:Site (More (count Y s i))), ∃ (q':Signed)(b:Site (More (count Y s i))),
     signX S' q⁻¹ p=signX S q'⁻¹ b ∧ MapΦ Y s i k q p A'=costχ c ∘ MapΦ Y s i k q' b A
lemma BandStart : LongBand Y s i k F F H H false:=fun z r=>⟨z,r,rfl,rfl⟩
lemma BandSheet (h:LongBand Y s i k F f H Q B): SlideBand Y s i k F f H Q B:=fun z=>h z 0
lemma mixχ (b:Bool)(x:ℂ): star (costχ b x)=costχ (!b) x:=by cases b; rfl; change star (star _)=_; rw [star_star]; rfl
lemma BandMirror (h:LongBand Y s i k F f H Q B)(Z:Kea.Pad P.K.j (count Y s i))(j:Axis)(b:ℤ): LongBand Y s i k F (spunA j b f) H (Q.image ((plane j b).anon _)) (!B):=by
 intro q u; let T:=Signed.mirror j; let x:=wrap (More N') (2 • (b • step j)); let v: Signed:= (q⁻¹*T)⁻¹; let K:=affine q⁻¹ u x
 obtain ⟨t,d,g,k'⟩:=h v K
 have he: signX (Q.image ((plane j b).anon _)) q⁻¹ u=signX Q v⁻¹ K:=by
    unfold signX v; rw [image_image,inv_inv]; refine congrArg (fun p=>Q.image p) ?_; funext y; change affine q⁻¹ u (affine T x y)=_; simp [K,affine,Signed.act_mul,add_assoc] -- tune
 have hy (W:Pane N'): Lattice.pull T x (Lattice.pull q⁻¹ u W)= Lattice.pull v⁻¹ K W:=by unfold K v; rw [inv_inv, Lattice.pull_pull] -- tune
 refine ⟨t,d,he.trans g,?_⟩; funext y
 unfold MapΦ spunA; rw [fling_eq, hy]; change Ωturn Y s i k (theta _ _) = _; rw [θφV Y s i k Z]
 change star ((MapΦ Y s i k v K f) y)=_; rw [k']; exact mixχ _ _
#print axioms BandMirror
end FrameP
end Papal
end LocalLimit
end Rate
end YM.CF.Py
end
