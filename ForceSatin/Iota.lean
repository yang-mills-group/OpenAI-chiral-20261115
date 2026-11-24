import ForceSatin.Wallet
import YM.CF.Continuum.Current
import YM.SU5.Celeste.Banquet
set_option autoImplicit false
set_option maxHeartbeats 520000
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

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x
open CF.Lamour CF.Lamour.Bridge.Celeste Afterglow Journey
open Loaves Satin Tapestry Six
local notation "⚝" => Lamour.alleyR
-- wallet: entirely on real-profile families before paying any rotations or other Motion
open Window Lifted
-- ACTUAL stencil IA.4; LEAN's current defined with no sign on first spin; here verify. keep all signed-grid Wind to telescope.
variable (K:Calibration)(T:Ballad.Lead.Clan) (x:Cover) (N: Side)
abbrev stip : ℂ:=1/16
def censusF : Buffered.Family K:= stip • ∑ i∈ Window.colors T, creation K x 0 i * removal K x 2 i
lemma censusF_phys (m:Side)(U:Fields (K.c m)):
    censusF K T x m U= stip • ∑ i∈ Window.colors T, put ((wrap (K.c m) x,0),i)*takeF ((wrap (K.c m) x,2),i) := by
 unfold censusF; simp_rw [Pi.smul_apply,Finset.sum_apply,Pi.mul_apply]; apply congrArg (stip • ·); apply Finset.sum_congr rfl; intro i _; change create _* Fock.remove _=_; unfold Fock.remove; rw [basisC,basisC,map_smul,map_smul,star_smul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,create_put,create_put,smul_smul,show star (Lifted.winding (K.c m) x)=_ from fee_real _, show Lifted.winding (K.c m) x*_= _ from fee_one _, one_smul]; rfl -- fee multiplication annotation spelling
lemma censusF_current (m:Side)(U:Fields (K.c m)) : censusF K T x m U= stip • dg (Window.jOp (K.c m) T (wrap (K.c m) x) 0 2):=by rw [censusF_phys]; exact congrArg (stip • ·) (Window.current_words T (wrap (K.c m) x) 0 2 U.1).symm
lemma wake_lane (S:Finset (Skye.Seat N))(s:Site N)(hs:node s∈S) (u:SpinIdx)(i:SU.Slot)(b:Bool): Street S 1 1 ((if b then takeF else put) ((s,u),i)):=by -- tweak syntax
 let V:Tulip.Single N:= ((s,u),i); let X:=basisKet V; have ht:withinM (modesIn N {node s}) X:= within_basis _ _ ((modes_at ..).mpr (Finset.mem_singleton_self _))
 have hz:‖X‖=1:=by simp [basisKet,X]
 have he:= Street.leg b _ hs X ht; rw [hz] at he; cases b <;> simpa [X,V,Fock.creed] using he
lemma wake_sum {N:Side}{U:Type*} (S:Finset U)(F: U→FC (Single N))(R: Finset (Skye.Seat N))(m:ℕ)(h:∀ i∈S,Street R m 1 (F i)): Street R m S.card (∑ i∈ S,F i):=by
 induction S using Finset.induction_on with
 | empty=>
    rw [Finset.sum_empty]; simpa using Street.enlarge (S:=R) le_rfl (Nat.zero_le m) (Street.scale 0 Street.one) -- S binder
 | @insert i L e ih=> rw [sum_insert e,card_insert_of_notMem e,Nat.cast_add_one, add_comm (↑L.card:ℝ)]; exact Street.add (h i (mem_insert_self ..)) (ih (fun i v=>h _ (mem_insert_of_mem v)))
lemma wakePurse : Wallet K (censusF K T x) {nodeC x} 2 1:=by
 let S: Finset Cover:={nodeC x}; refine ⟨.smul _ (InTest.sum _ _ (fun i _=> InTest.mul (b:=true) (c:=true) (.creator i (by decide) (mem_singleton_self _)) (.remover i (by decide) (mem_singleton_self _)))),?_,?_,?_⟩
 · intro m i k; rw [censusF_phys,censusF_phys]
 · intro i h U; rw [censusF_current,censusF_current, twist_scalar,dg_cov, jOp_gauge]
 intro m; let N:= K.c m; let o:=wrap N x; let W:= Satin.region {nodeC x} N
 rw [censusF_phys]; refine Street.enlarge ?_ le_rfl (Street.scale _ (wake_sum _ _ _ 2 fun i _=>?_));
 swap; · have hz:node o∈W:= by rw [node_of]; exact Finset.mem_image_of_mem _ (Finset.mem_singleton_self _)
         rw [←(mul_one (1:ℝ))]; exact (wake_lane _ _ _ hz 0 i false).mul (wake_lane _ _ _ hz 2 i true)
 simp only [Window.colors_card]; have he:‖stip‖=1/16:=by norm_num [stip, Complex.norm_ofNat]
 rw [he]; unfold Window.dimf; split <;> norm_num

-- Mirror test kits, allowed concatenations at ANY (poly p)-diameter layout. coverage statement on `pencil_custody`. A marked-root test tuple with degree bounded independently of s.
structure Auditor where
 whereAt : Cover
 clan : Ballad.Lead.Clan
 prior : List (Axis×ℤ)
abbrev seamTick (p: Axis × ℤ) := (Buffered.plane p.1 p.2).motion
def auditorMark (a:Auditor) : Buffered.Family K:= a.prior.foldl (fun v z=> Tower.mirror K z.1 z.2 v) (censusF K a.clan a.whereAt)
def auditorSite (a:Auditor): Cover:= a.prior.foldl (fun x v=> seamTick v x) (nodeC a.whereAt)
lemma mirrorGood (a:Auditor): Wallet K (auditorMark K a) {auditorSite a} 2 1:=by
 let P(L:List (Axis×ℤ))(F:Buffered.Family K):= List.foldl (fun v z=> Tower.mirror K z.1 z.2 v) F L
 have he(L:List (Axis×ℤ))(F:Buffered.Family K)(v:Cover)(p:Wallet K F {v} 2 1): Wallet K (P L F) {L.foldl (fun x z=> seamTick z x) v} 2 1:=by induction L generalizing F v with
 | nil=> exact p
 | cons z L ih=> exact ih _ _ (by rw [←(show Tower.reflectedBox z.1 z.2 {v}={_} from image_singleton ..)]; exact p.flipFront z.1 z.2)
 exact he a.prior _ _ (wakePurse K a.clan a.whereAt)
def audition (a:List Auditor) := (a.map (auditorMark K)).prod
lemma audition_paid (a:List Auditor)(S:Finset Cover)(h:∀ i∈a,auditorSite i∈S): Wallet K (audition K a) S (2*a.length) 1 := by induction a with
 | nil=> simpa [audition] using Wallet.one K S
 | cons i L ih=> rw [audition,List.map_cons,List.prod_cons,List.length_cons,mul_add,mul_one, add_comm]; exact (by simpa [audition] using (((mirrorGood K i).augment (singleton_subset_iff.mpr (h _ List.mem_cons_self)) le_rfl le_rfl).times (ih (fun i v=> h i (List.mem_cons_of_mem _ v)))))
def stature (L:List Auditor):=(L.map auditorSite).toFinset
lemma audition_height (a:List Auditor): Wallet K (audition K a) (stature a) (2*a.length) 1:= audition_paid K a _ (fun i h=> List.mem_toFinset.mpr (List.mem_map.mpr ⟨i,h,rfl⟩))
def voter (L:List Auditor):Dome K:=⟨audition K L,Tapestry.broadCompile K _ (audition_height K L).exam.widen⟩
theorem audited (L:List Auditor): PureMatter K (voter K L) ∧ voter K L∈ enclave K := ⟨(audition_height K L).purity,(enclave_spec K).mpr (audition_height K L).gauge⟩

variable {H:Real.exp 1≤P.x}{b C:ℝ}(z0:0<b)(q':CF.Papyrus.Franc.postage 4 b)
variable (p0:∀ᶠ s:ℕ in atTop,∀ i k:ℕ,(Y.voyage i).kick≤k→ s≤ Y.uv k→ TiltWorld Y s i k b C)
variable {u v:ℕ→ℕ}{I E}(U:Universal Y H u v I E)
include z0 q' p0 U
theorem wage_census (m I':ℕ) : ∀ᶠ s:ℕ in atTop,∀ (F:List Auditor), F.length ≤ m → WidthBudget (stature F) (budgetWidth (ℶ s) I') → (∃ L:List Wine, audition (tent Y H) F=dek (tent Y H) L) ∧
   ∀ L:List Wine, audition (tent Y H) F=dek (tent Y H) L → ‖E s (audition (tent Y H) F)-tallyW L‖ ≤ wane (ℶ s):=by
 filter_upwards [wiseFunds Y z0 q' p0 U (2*m) I',(turnover P).eventually_ge_atTop 1] with s p h F e w
 exact p _ _ ((audition_height _ F).augment (Finset.Subset.refl _) (Nat.mul_le_mul_left _ e) (Real.one_le_rpow h (by norm_num [micr]))) w
#print axioms wage_census
#print axioms audited
end Papal
end LocalLimit
end Rate
end YM.CF.Py
