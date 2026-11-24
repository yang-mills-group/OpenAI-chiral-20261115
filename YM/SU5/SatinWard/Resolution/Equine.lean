import YM.SU5.SatinWard.Resolution.TipToe
set_option autoImplicit false
set_option linter.unusedSimpArgs false
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
open LampD Quire LitCurrent AuroraX
namespace LampRead
attribute [local irreducible] bandWidthD
open Next.Rank Next.Rank.Spindle _root_.YM.Regis.Circuit.SpringDay.Spring
local notation "U"=> headlight -- fully qualify
abbrev ZonePlot (k:ℕ):= landSheet k × landSheet k
abbrev PollX(k:ℕ):= ZonePlot k × principalKid
abbrev concern{k:ℕ}(i:PollX k):glassPair k:= ((i.1.1,upKid i.2.1),(i.1.2,dnKid i.2.2))
lemma polled {k:ℕ}(i:PollX k): plusLayer (concern i):= ⟨i.2.1.1.property,i.2.2.1.property⟩
local notation "I"=> _root_.Zephyr.Chern.IS
local notation "Λ"=> SpinIdx × SU.Slot
lemma layoutPoll {J:Type*}[AddCommMonoid J](k:ℕ)(F:glassPair k→ J)(q:∀ i, ¬ plusLayer i→ F i=0) : ∑ i:glassPair k,F i=∑ i:PollX k, F (concern i):=by
 let W:=univ.filter (@plusLayer k); have h:∑ i: PollX k, F (concern i)=∑ i∈W, F i:=by
    refine sum_bij (fun i _=>concern i) (fun i _=>mem_filter.mpr ⟨mem_univ _,polled i⟩) ?_ (fun j e=>?_) (fun i _=>rfl)
    · intro i _ j _ e; apply Prod.ext; · exact Prod.ext (congrArg (fun i:glassPair k=>i.1.1) e) (congrArg (fun i:glassPair k=>i.2.1) e)
      exact Prod.ext (Prod.ext (Subtype.ext (congrArg (fun i:glassPair k=>i.1.2.1) e)) (congrArg (fun i:glassPair k=>i.1.2.2) e)) (Prod.ext (Subtype.ext (congrArg (fun i:glassPair k=>i.2.2.1) e)) (congrArg (fun i:glassPair k=>i.2.2.2) e)) -- alignment
    have h:= (mem_filter.mp e).2; exact ⟨((j.1.1,j.2.1),( ⟨⟨j.1.2.1,h.1⟩,j.1.2.2⟩,⟨⟨j.2.2.1,h.2⟩,j.2.2.2⟩)),mem_univ _,rfl⟩
 rw [h]; symm; exact sum_subset (subset_univ W) fun i _ t=> q i (fun a=>t (mem_filter.mpr ⟨mem_univ _,a⟩)) -- rw h expects RHS, orientation.
variable {k:ℕ}(X Y:Cover)(Wκ:DozeTrack k)(Vκ:hungerCap k Wκ)
noncomputable abbrev Comb (L:DozeTrack k)(u: PollX k):ℂ:= L.2 (concern u)
lemma feeQuota(L:DozeTrack k)(u:hungerCap k L):(∑ i:PollX k, ‖Comb L i‖) ≤ dietTotal k L:=by
 unfold dietTotal; rw [layoutPoll (J:=ℝ) k _ (fun i e=>by rw [u i e,norm_zero])]; exact le_add_of_nonneg_left (norm_nonneg _)
variable (a:Axis)(G:Op SU.Slot) {s:ℕ} (b χ:ℝ)
local notation "Πv" zeta:max => (Picker.colorWage (W s) b χ zeta)
local notation "Kλ"=>LampD.headlight k Wκ X
local notation "Jκ"=>lessonZ a G Y
noncomputable def marketZero (L:PollX k)(x:Cover):=costSong ((x+L.1.2.val)-(x+L.1.1.val)) L.2.2 L.2.1
noncomputable def billMono (L:DozeTrack k)(x:Cover):ℂ:=L.1+(∑ i:PollX k,L.2 (concern i)*marketZero i x)
include H
open _root_.YM.Regis.Resonance
lemma hatShadow (l:PollX k) : Picker.colorWage (W s) b χ (trackRoad k X (some (concern l)))= marketZero l X:=by
 rw [trackRoad,if_pos (polled l)]; let x:=X+l.1.1.val; let y:=X+l.1.2.val; change Picker.colorWage (W s) b χ (LampD.commuter [Kp x l.2.1, Kg y l.2.2]) = _; simp [Picker.colorWage,LampD.commuter,H.Wick,twoPair,Lull.priceW,Lull.candle,Lull.candles,(tuneX H x y l.2.1 l.2.2).1]; rfl -- inspect
lemma hatNone (k:ℕ): Picker.colorWage (W s) b χ (trackRoad k X none)=1:=by change Picker.colorWage _ _ _ (LampD.commuter [])=_; simp [Picker.colorWage,Lull.priceW,Lull.candle,Lull.candles, LampD.commuter,H.Wick,runes,Fock.claps, spinC,cites,picks,beside,Fock.offer, Fock.cval] -- fin?
include Vκ in
lemma salary_beam : (LampD.headlight k Wκ X).issues b (W s) χ=billMono Wκ X:=by
 unfold Tab.issues LampD.headlight; rw [Fintype.sum_option]; unfold billMono; rw [layoutPoll k _ (fun i u=>?_)] -- layout sum RHS? look.
 swap; · change Wκ.2 i *_=_; rw [Vκ i u,zero_mul]
 change (Wκ.1*Πv (trackRoad k X none))+(∑ i:PollX k,Wκ.2 _*Πv (trackRoad k X (some (concern i))))=_; simp_rw [hatShadow H X b χ]; rw [hatNone H X b χ k,mul_one]
noncomputable abbrev inkPair (i:PollX k)(j:principalKid):ℂ:= costSong (Y-(X+i.1.1.val)) j.2 i.2.1 *(-costSong (X+i.1.2.val-Y) i.2.2 j.1)
lemma songPoll (i:PollX k)(j:principalKid): Picker.colorWage (W s) b χ (coupler (trackRoad k X (some (concern i))) (verseKid Y j))= marketZero i X * price₀ j+ inkPair X Y i j:=by
 rw [trackRoad,if_pos (polled i)]; let x:= X+i.1.1.val; let y:=X+i.1.2.val; change Picker.colorWage (W s) b χ (LampD.commuter [Kp x i.2.1,Kg y i.2.2,Kp Y j.1,Kg Y j.2])= _; have hi (x y:Cover)(i j:seniorKid): WickP (Kp x i) (Kp y j)=0:=H.W_like _ _ rfl; simp [Picker.colorWage,Lull.priceW,Lull.candle,Lull.candles,H.Wick,LampD.commuter,spinPrice₀,hi,(tuneX H x y i.2.1 i.2.2).1,(tuneX H Y Y j.1 j.2).1,(tuneX H x Y i.2.1 j.2).1,(tuneX H Y y j.1 i.2.2).2]; simp only [marketZero,costSong, ite_mul,zero_mul]; rfl -- semicolon := definition? hpay.
lemma noPoll (j:principalKid) : Picker.colorWage (W s) b χ (coupler (trackRoad k X none) (verseKid Y j))=price₀ j:= song_cap2 H Y χ j b -- order
local notation "x*" i:max=> Wκ.2 (concern i)
local notation "y*" i:max=> ordinaryW a G i
noncomputable def billDuet(k:ℕ)(L:DozeTrack k)(x y:Cover):ℂ:=∑ i:PollX k,∑ j:principalKid,L.2 (concern i)*ordinaryW a G j*inkPair x y i j
include Vκ
lemma dualCounter : (mulT (LampD.headlight k Wκ X) (lessonZ a G Y)).issues b (W s) χ = billDuet a G k Wκ X Y + billMono Wκ X*reading₀ a G:=by
 unfold Tab.issues; rw [mulT,sum_product]; change (∑ i:NeedleCab k,∑ j:principalKid,_)= _; rw [Fintype.sum_option]; rw [layoutPoll k _ (fun i u=> sum_eq_zero fun j _=>?_)] -- shape
 swap; · change Wκ.2 i*_*_=0; rw [Vκ i u,zero_mul,zero_mul]
 change (∑ j:principalKid,Wκ.1* (y* j)*Πv (coupler (trackRoad k X none) (verseKid Y j)))+(∑ i:PollX k,∑ j:principalKid,(x* i)*(y* j)*Πv (coupler (trackRoad k X (some (concern i))) (verseKid Y j)))=_; simp_rw [noPoll H X Y b χ,songPoll H X Y b χ]; unfold billMono billDuet reading₀; rw [add_mul,mul_sum,sum_mul,add_left_comm]; congr 1
 · exact sum_congr rfl fun i _=> mul_assoc ..
 rw [←sum_add_distrib]; refine sum_congr rfl fun i _=>?_ ; rw [mul_sum,←sum_add_distrib]; apply sum_congr rfl fun j _=>?_ ; ring
#print axioms dualCounter
end LampRead
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
