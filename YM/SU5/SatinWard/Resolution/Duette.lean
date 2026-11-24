import YM.SU5.SatinWard.Resolution.Journal
import YM.SU5.SatinWard.Resolution.Synod
import YM.SU5.SatinWard.Resolution.Achilles
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 3200
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
open MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
open Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
open scoped ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
open Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus QuadClock Ione Vow Swell
open _root_.Zephyr.Chern
universe uΩ


open Papal CF.Papyrus.Franc.SatinForce CF.Pannier.Chancel Checkers

open CF.Papyrus.Franc.Loaves
-- CP3 package. PUBLIC, no topology/order changes
open Moon
open Horizons FoliageP BareProgram Moonlit Moonlit.SwitchC
open _root_.YM.Regis.Head.Brecht _root_.YM.Regis.Circuit _root_.YM.Regis.Circuit.SpringDay
open SlabMark VelourBoard Papal.SkyTax Cygnet VelourWiggle
open YM.Stationary (Gaia)
open SwitchC.Garland SwitchC.Garland.Terrace SwitchC.Garland.Terrace.Juniper
open Abacus CheckerFlag SlopeCharge Maxwell
open scoped RealInnerProductSpace ContDiff
namespace Fame
variable {P:Spine}{K:P.Register}{b C:ℝ}{t σ}{W:ℕ→ HorizonLens→ HorizonLens→ℝ}{β:ℕ→ℝ}
variable (T: CouncilGrant P K b C t σ W β)(H:PublicKernel P σ W)(F D: PlaqAxes)
open BProof Pressure
open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
namespace Regulator
local notation "Ω" s:max=> hat P.par.R.L P.par.x s
open CasaF.Signboard CF.Tap SignSlot ShapeLab Emu
abbrev plusSpin:= {i:SpinIdx// i∈plusHalf}
abbrev minusSpin:= {i:SpinIdx// i∉plusHalf}
abbrev seniorKid:= plusSpin × SU.Slot
abbrev juniorKid:= minusSpin × SU.Slot
abbrev principalKid:= seniorKid × juniorKid
noncomputable abbrev Kp(x:Cover) (i: seniorKid): Bite:= ⟨x,i.1.val,i.2,false⟩
noncomputable abbrev Kg(x:Cover)(i:juniorKid): Bite:= ⟨x,i.1.val,i.2,true⟩
def verseKid (x:Cover)(i:principalKid): Horizon:=⟨[Kp x i.1,Kg x i.2],[],[],[]⟩
local notation "EndC"=> Op SU.Slot
abbrev ordinaryW (s:Axis)(A:EndC)(i:principalKid):ℂ:= (petal s⊗ₖ A) (i.1.1.val,i.1.2) (i.2.1.val,i.2.2)
noncomputable def lessonZ (s:Axis)(A:EndC)(x:Cover): Tab principalKid:=⟨verseKid x,univ,ordinaryW s A⟩
-- `g` = old plain width cost.R_w
variable (j:Axis)(x y:Cover)(A:EndC) {s:ℕ}
local notation "V⚕"=> lessonZ j A x
lemma kidPrice(i:principalKid)(t z:ℝ): LoPrice (verseKid x i) t z {nodeC x} 2:= ⟨by
    intro m a; simp only [verseKid,List.mem_cons,List.not_mem_nil,or_false] at a; rcases a with rfl | rfl -- fix subst m
    · exact ⟨mem_singleton_self (nodeC x) -- type mem nodeC
             ,⟨fun _=> i.1.1.property,fun _=>rfl⟩⟩
    exact ⟨mem_singleton_self (nodeC x), ⟨by simp,fun e=> (i.2.1.property e).elim⟩⟩ , rfl, le_rfl, by simp [verseKid], by simp [verseKid],by simp [verseKid],by simp [verseKid],by simp [verseKid],by simp [verseKid]⟩
lemma singer_credit (t z:ℝ):SwitchC.ticket {nodeC x} t z 2 (V⚕):=fun i _=> kidPrice x i t z
local notation "Ki"=>SpinIdx × SU.Slot
local notation "Σg"=> (univ:Finset (SpinIdx× SU.Slot))
local notation "Uρ"=> (Σg.filter fun i=> i.1∈plusHalf)
local notation "Wρ"=> (Σg.filter fun i=> i.1∉plusHalf)
abbrev upKid (i:seniorKid): SpinIdx × SU.Slot := (i.1.val,i.2)
abbrev dnKid (i:juniorKid): SpinIdx × SU.Slot := (i.1.val,i.2)
lemma upSum {M: Type*}[AddCommMonoid M](F:Ki→ M): ∑ i:seniorKid,F (upKid i)= ∑ i∈ Uρ,F i:=by
 apply Finset.sum_bij (fun i _=> upKid i)
 · intro _ _; exact mem_filter.mpr ⟨mem_univ _, (Subtype.property _)⟩
 · intro i _ j _ e; exact Prod.ext (Subtype.ext (congrArg Prod.fst e)) (congrArg (Prod.snd (α:=SpinIdx)) e)
 · intro i h; exact ⟨(⟨i.1,(mem_filter.mp h).2⟩,i.2),mem_univ _,rfl⟩
 exact fun _ _=> rfl
lemma dnSum {M: Type*}[AddCommMonoid M](F:Ki→ M): ∑ i:juniorKid,F (dnKid i)= ∑ i∈ Wρ,F i:=by
 apply Finset.sum_bij (fun i _=> dnKid i)
 · intro i _; exact mem_filter.mpr ⟨mem_univ _, i.1.property⟩
 · intro i _ j _ e; exact Prod.ext (Subtype.ext (congrArg Prod.fst e)) (congrArg (Prod.snd (α:=SpinIdx)) e)
 · intro i h; exact ⟨(⟨i.1,(mem_filter.mp h).2⟩,i.2),mem_univ _,rfl⟩
 exact fun _ _=> rfl
variable (z:ℝ)(J:Calibration)
local notation "Pa"=> P.calibration
lemma frosted (i:principalKid): Frost z J (verseKid x i)= creation J x i.1.1.val i.1.2 * removal J x i.2.1.val i.2.2:=by -- no mask/spin only
 rw [Frost,show Buffered.scalar J _=1 from ?_,one_mul,show (verseKid x i).song= [Kp x i.1,Kg x i.2] from rfl,plot_cons]; congr 1
 · funext i U; simp [Kp,plotN,chartP,vix]; rfl
 · funext i U; simp [Kg,plotN,chartP,vix]; rfl
 funext i U; unfold Buffered.scalar; simp [bakeFlag, bakedC,softP,verseKid] -- verse etc.
lemma velvety : (lessonZ j A x).cookP z J= gardenFlower J x j A:=by
 unfold Tab.cookP lessonZ drier; rw [gardenForm]; let Flag₁(i k:Ki):= (petal j⊗ₖ A) i k • (creation J x i.1 i.2 * removal J x k.1 k.2); change (∑ i:principalKid, ordinaryW j A i • Frost z J (verseKid x i))= (∑ i∈ Uρ,∑ k∈ Wρ,Flag₁ i k); rw [← upSum]; simp_rw [frosted, ←dnSum] -- `C` type k.Semi
 rw [Fintype.sum_prod_type]
lemma f_cost : (V⚕).terms=(lessonZ j A 0).terms:=rfl
lemma kid_axis_accepted (g:∀ t:SU.E, Commute A (matter t).val) : Tab.holds J z V⚕:=by unfold Tab.holds; rw [velvety]; exact fun n=> gardenPrice j A g _
-- open Loaves -- Advance lookup Rune algebra
lemma spinPrice₀ (a b c d:Bite)(M:Bite→Bite→ℂ):runes M [a,b,c,d]=M a b*M c d - M a c*M b d+ M a d*M b c:=by
 simp [runes,spinC,Fock.offer,beside,claps,picks,cites,besideX,Fock.cval,extendsU]; ring -- same simp as twoPair
noncomputable abbrev costSong (X:Cover)(i:juniorKid)(j:seniorKid):ℂ:= if i.2=j.2 then tradeW i.1 j.1 X else 0
-- earlier at x. Centered comparison cost.Scalar Π.Nullable at 0.Yes.
noncomputable abbrev price₀(i:principalKid):ℂ:=costSong 0 i.2 i.1
noncomputable abbrev price₂ (Z:Cover)(i j:principalKid):ℂ:= costSong (-Z) j.2 i.1*(-costSong Z i.2 j.1)
include H
lemma tuneX (i:seniorKid)(k:juniorKid): WickP (Kp x i) (Kg y k)=costSong (y-x) k i∧ WickP (Kg y k) (Kp x i)= -costSong (y-x) k i:= H.W_particle _ _ rfl rfl k.1.property i.1.property -- order?
open _root_.YM.Regis.Resonance
lemma song_cap2 (i:principalKid)(d:ℝ): Picker.colorWage (W s) d z (verseKid x i)=price₀ i:=by simp [Picker.colorWage,verseKid,H.Wick,twoPair,Lull.priceW,Lull.candle,Lull.candles,(tuneX H x x i.1 i.2).1,price₀] -- tuneX missing arguments adapted
lemma song_quad (i k:principalKid)(d:ℝ):Picker.colorWage (W s) d z (coupler (verseKid x i) (verseKid y k))=price₀ i*price₀ k+price₂ (x-y) i k:=by
 have hi (x y:Cover)(i j:seniorKid): WickP (Kp x i) (Kp y j)=0:=H.W_like _ _ rfl
 have hh (x y:Cover)(i j:juniorKid): WickP (Kg x i) (Kg y j)=0:= H.W_like _ _ rfl
 simp [Picker.colorWage, verseKid,coupler,Lull.priceW,Lull.candles,Lull.candle,H.Wick,spinPrice₀,hi,(tuneX H x x i.1 i.2).1, (tuneX H y y k.1 k.2).1,price₂,price₀,(tuneX H x y i.1 k.2).1,(tuneX H y x k.1 i.2).2] -- error `.. rfl`
noncomputable def reading₀(j:Axis)(A:EndC) :ℂ:= ∑ i:principalKid, ordinaryW j A i*price₀ i
noncomputable def duet (j:Axis)(A:EndC)(k:Axis)(B:EndC)(Z:Cover):ℂ:=∑ i:principalKid, ∑ m:principalKid, ordinaryW j A i * ordinaryW k B m * price₂ Z i m
variable (B:EndC)(k:Axis)(h':ℝ)
local notation "κ"=>Picker.colorWage (W s) h' z
lemma arRos : (V⚕).issues h' (W s) z=reading₀ j A:=by unfold Tab.issues lessonZ; simp_rw [song_cap2 H]; rfl
lemma duetLaw : (mulT V⚕ (lessonZ k B y)).issues h' (W s) z = duet j A k B (x-y)+ reading₀ j A * reading₀ k B:=by
 let U:= ordinaryW j A; let V:=ordinaryW k B; unfold Tab.issues mulT lessonZ; rw [sum_product]
 change (∑ i:principalKid,∑ k:principalKid,U i * V k * κ (coupler (verseKid x i) (verseKid y k))) = _
 unfold duet reading₀; simp_rw [song_quad H] -- `simp` add_assoc loops remove
 rw [sum_mul,← sum_add_distrib]; apply sum_congr rfl; intro i _; rw [mul_sum,←sum_add_distrib]; apply sum_congr rfl; intro m _; unfold U V; ring
#print axioms duetLaw
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
