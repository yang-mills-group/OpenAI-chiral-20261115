import YM.CF.Salt.Tract
import YM.CF.Salt.Rider
import YM.CF.Stake.Loom
import YM.CF.Salt.Stone
import YM.CF.Salt.Piers
import YM.CF.Haro.Tacit
import YM.CF.Salt.Milk
import YM.CF.Salt.Desk
import YM.CF.Plume.Wager
import YM.CF.Haro.Silk
import YM.CF.Salt.Felt
import YM.CF.Tye.Wheel
import YM.CF.Salt.Dial
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 21000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Salt
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker Classical
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake Scion Levier Hive Nacre Tye Skye RG Pressure Next.SectorChange Planned.AtomRegular Girt Spire
open Eire Skye Levier Scion Urn Pastry Rill Kennel Pec
open Eire Girt Tulip Spire Proa RG Pressure Stilo Scree Palot Tye Cour Broc Hive Hake
open Esti Forge AnalyticBridge.Annulus1AD Ac AnalyticBridge.GaussianFieldAlignment Tensor Locations Push.SectorMeasure.Oriented
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure Slate Atala
variable {P N B:Side}{G:Ratio (mid N B) (mid P B)}(S:StepData (Domain N B) (Domain P B))(x:ℝ)(t:S.ratio=ratio G)(s:Sweep (mid N B))(A:Stores S)(V:Pane (mid P B))(X:Support (Domain P B))
local notation "ζ"=> shiftFaces s.s (S.ratio.embed (Facet.pasta s))
local notation "T"=> reSweep G s
open Lich Lich.Muster Stake Tarn Forge Hake Laic
variable (i:Words S)(r k:ℕ){Y: Tube SU.group S}{Z:ℝ}(C:Muster G S x Z Y)
local notation "Λ"=> luckP G S s r
open Eire
variable (W:Ride S)(K:Troupe S r (Words S))(V':Config SU.group (Domain P B))(β d b':ℝ)(Y':Tube SU.group S)(g:Site (Domain N B)→SU.group.El)
local notation "fQ"=> luckP G S s r
local notation "Zz"=> K.image (fieldT S r G s)
local notation "ZQ"=> reSweep G s
lemma wicks :(Zz).toLeft= K.toLeft.image (luckP G S s r):=by
 ext i; obtain ⟨i,rfl⟩:=(luckP G S s r).surjective i; rw [mem_toLeft]; change fieldT S r G s (Sum.inl i)∈ _↔ _; simp only [mem_image,(luckP G S s r).injective.eq_iff,(fieldT S r G s).injective.eq_iff,exists_eq_right,mem_toLeft]
lemma ticks :(Zz).toRight.toLeft= K.toRight.toLeft.image (rave (reSweep G s)):=by ext i; obtain ⟨i,rfl⟩:=(rave (reSweep G s)).surjective i; rw [mem_toLeft,mem_toRight]; change fieldT S r G s (Sum.inr (Sum.inl i))∈ _↔_; simp only [mem_image,(rave (reSweep G s)).injective.eq_iff,(fieldT S r G s).injective.eq_iff,exists_eq_right,mem_toLeft,mem_toRight]
lemma horns : (Zz).toRight.toRight=K.toRight.toRight.image (rock s).symm:=by ext i; obtain ⟨i,rfl⟩:=(rock s).symm.surjective i; rw [mem_toRight,mem_toRight]; change fieldT S r G s (Sum.inr (Sum.inr i))∈ _↔_; simp only [mem_image,(rock (S:=S) s).symm.injective.eq_iff,(fieldT S r G s).injective.eq_iff,exists_eq_right,mem_toRight]
local notation "Ρ"=> K.toRight.toLeft.toRight
lemma honour : (Zz).toRight.toLeft.toRight= (K.toRight.toLeft.toRight).image (fanZ T):=by ext i; obtain ⟨i,rfl⟩:=(fanZ T).surjective i; rw [mem_toRight,ticks]; change rave T (Sum.inr i)∈_↔_; simp only [mem_image,(fanZ T).injective.eq_iff,(rave T).injective.eq_iff,exists_eq_right,mem_toRight]
lemma dateV(F:Finset (Force (mid P B))) : rendL (F.image (fanZ (reSweep G s)))=actY T (rendL F):=by
 ext i; rw [actY,mem_map_equiv]; simp only [rendL,mem_biUnion,exists_mem_image]; refine exists_congr fun i=> and_congr_right fun h=> Finset.mem_map_equiv
lemma honour_P : penn S Zz=airport s (penn S K):=by rw [penn,wicks, bone_t]
lemma groveL : Set.PairwiseDisjoint (((Zz).toRight.toLeft.toRight):Set _) (fun i:Force (mid P B)=> i.val.1.val.2) ↔ Set.PairwiseDisjoint (Ρ:Set _) (fun i:Force (mid P B)=>i.val.1.val.2):=by
 rw [honour]; constructor
 · rintro p a ha b hb u; have hp:= @p (fanZ T a) (mem_image_of_mem (fanZ T) (show a∈ Ρ from ha)) (fanZ T b) (mem_image_of_mem (fanZ T) (show b∈ Ρ from hb)) ((fanZ T).injective.ne u); exact (lay_o T a.val.1.val.2 b.val.1.val.2).mp hp
 rintro v x p y t s; obtain ⟨u,w,rfl⟩:=mem_image.mp (show x∈_ from p); obtain ⟨a,q,rfl⟩:=mem_image.mp (show y∈ _ from t); exact (lay_o _ _ _).2 (@v u w a q (fun e=>s (congr_arg _ e))) -- shadows s
variable (M: Monk SU.group S)(q:Chi)
include t
lemma shore_v(u:(rot s (Eire.trot S M (cusp (penn S K) x M.V))).sent x Y' q d k β= flashA (reSweep G s) ((Eire.trot S M (cusp (penn S K) x M.V)).sent x Y' q d k β)) : capG S (flags (temp x) (rot s M).V) (chillB (rot s M)) b' Zz (quill (chart s) W) ↔ capG S (flags (temp x) M.V) (chillB M) b' K W:=by
 let N':=Eire.trot S M (cusp (penn S K) x M.V); let Q':=rot s N'; have hv:Eire.trot S (rot s M) (airport s N'.key)= rot s N':= wiseT ..; have hh: brushK (penn S Zz) (chillB (rot s M)) b'= brushK Q'.key (chillB Q') b':=by
    unfold Q'; rw [←hv,honour_P]; rfl -- possible rw failure
 have he: brushK (penn S Zz) (chillB (rot s M)) b'= actY T (brushK (penn S K) (chillB M) b'):=by rw [hh,←stampedB Q' Y' x q d k β,show Q'.sent _ _ _ _ _ _ =_ from u,show Q'.key= _ from thereZ .., brine S t s, show brushK N'.key (N'.sent _ _ _ _ _ _) _= brushK (penn S K) _ _ from stampedB ..]; rfl -- tune goal
 have hx(X Z: Support (Domain N B)):actY s X=actY s Z↔ X=Z:=(shelf s).injective.eq_iff; unfold capG; rw [pose_t,bayV, sit_k, flagsA,show _∩_= _ from (show (flags (temp x) M.V).map _∩ (Stilo.bay W).map _=actY s (flags (temp x) M.V∩bay W) from (map_inter ..).symm)]
 rw [show (penn S Zz).flags=actY s (penn S K).flags from ?_,hx,wicks,pure_a]; unfold Eire.earn; dsimp only; simp only [honour,dateV,he]; -- groveL rew prep
 refine and_congr_right fun _=> and_congr_left fun _ => and_congr ((shelf T).injective.eq_iff) ?_; simpa only [honour] using (groveL (G:=G) S s r K) -- tune
 rw [honour_P,actY,←sit_k]; rfl
end YM.CF.Salt
#print axioms YM.CF.Salt.shore_v
