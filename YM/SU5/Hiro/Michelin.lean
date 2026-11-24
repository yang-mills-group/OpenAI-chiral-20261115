import YM.SU5.Hiro.MenuBoard
import YM.SU5.Aria.SatinRails
import YM.SU5.Circuit.Dream
set_option autoImplicit false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia) -- tune
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Prototype
open Spine Lamour Bridge.Celeste Glimpse Morn Spine.RadiusF Ballad
open CF.Velvet CF.Pannier.Chancel Altitude
/-! # The phase, with full coupling visibility. cp16 application.
Estimate not that of separate-G-singlet component test or of beta-charge
non-vanishing in the Callan-Symanzik sense; PRICE nonfactorization for THIS
interpretation of registered observables, ruling out gauge freezing on the
indicated physical supports. See the construction notes.
-/
private lemma climbs(p:ℕ→ℕ):∃ f:ℕ→ℕ,p≤f∧StrictMono f:=by
 let f : ℕ→ℕ:= Nat.rec (p 0) (fun i v=>max (p (i+1)) (v+1)); exact ⟨f,fun i=> by cases i; exact le_rfl; exact le_max_left .., strictMono_nat_of_lt_succ (fun i=> show f i < max _ (f i + 1) from (Nat.lt_succ_self _).trans_le (le_max_right ..)) ⟩
lemma supplyR (P:Spine){U:P.Register}{S:Supplier}{e v:ℝ}(K:uniform P U S e v){r:ℕ→ℕ}(p:StrictMono r)(h:∀ i,0<r i):∃ f:ℕ→ℕ,∀ c:ℕ→ℕ,f≤c→ P.Estimable c r h (fun i=>P.eReadL (c i)) ∧ ∀ᵐ x∂ P.pillars 3,∀ j:Axis, P.Estimable c r h (fun i=>P.singleState j (c i) (P.otherSpectrum 3 j x)) :=by
 obtain ⟨u,G⟩:= pulls pairMood pairMood goldF goldF r (P.rangeClasp ∘ r) 0 (fun i=>holdingK i (h i)) (tip r) K (fun i=> readyTip r i (h i)); refine ⟨u,fun c t=>?_⟩; obtain ⟨v,z⟩:= G c t; exact ⟨P.confirms p.tendsto_atTop h _ (fun i=>P.eInvariant (c i)) v,z.mono fun x w a=>P.confirms p.tendsto_atTop h _ (fun i=>P.oracleInvariant a x (c i)) (w a)⟩
local notation "X"=> YM.basis 3
set_option maxHeartbeats 1000000 in
theorem twilight_tradition (L M D:ℝ)(Y:Supplier)(hx:0<M)(u:0<D) (z:ℕ→ℕ): ∃ (P:Spine)(K:P.Register), uniform P K Y L M ∧ ∃ (r:ℕ→ℕ), z≤r ∧
 ∃ (c:ℕ→ℕ), ∃ B:Launch P c r, P.Estimable c r B.unitSize (fun i=>P.eReadL (c i)) ∧ P.Captive goldF goldF bluePin 0 clearB_pos c tinyBill X (fun i f=>P.E (c i) f.val) ∧ roughUV P c r keyV ∧ ∃ (α t₁:ℝ),0<α∧ 0<t₁∧t₁<D ∧ ∃ R: Glimpse.Voyage P.par.block P.calibration.ℓ 4 α (RadiusF.next P.calibration.ℓ),
     ∀ᶠ i:ℕ in atTop, ∃ x:P.Spectrum0 3, P.party 3 K x ∧ (∀ j:Axis,P.Estimable c r B.unitSize (fun i=>P.singleState j (c i) (P.otherSpectrum 3 j x))) ∧ (∀ j:Axis,P.Captive goldF goldF bluePin 0 clearB_pos c tinyBill X (fun i f=>P.singleState j (c i) (P.otherSpectrum 3 j x) f)) ∧ readyUV P c r x keyV ∧ P.funds i (P.otherSpectrum 3 3 x) R t₁ ∧
       ∃ J: P.Ellis 3 x,P.LowerDeck x K J ∧
       ∀ z:SU.Slot, P.Intact K i R.toGaze x z t₁∧ P.Royal i ((P.otherSpectrum 3 3) x) R (family z) t₁ ∧ P.Passage x c r K z ∧ P.Bands x (family z) c r ∧ P.Portrait x (family z) c r:=by
 obtain ⟨P,K,T⟩:=installation Y L M hx; obtain ⟨r,f,W⟩:= outing T keyV keyV_positive z; obtain ⟨c,w⟩:= W; obtain ⟨c₀,v,w₀⟩:= climbs c; let H:= (w c₀ w₀ v).1
 obtain ⟨c₁,q⟩:= auras T (tagColors goldF goldF bluePin 0 clearB_pos) (ballotK tinyBill clearBill) (ballot_pos tinyB_pos clearB_pos); obtain ⟨h₀,Q⟩:= supplyR P T H.eager H.unitSize; obtain ⟨s,V,l⟩:= climbs fun i=>max (c₁ i) (max (h₀ i) (c i))
 have he:Tendsto tinyBill atTop atTop:=tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:=(1:ℝ))); obtain ⟨R,p⟩:=q s fun i=>(le_max_left ..).trans (V i); obtain ⟨rS,a,xA⟩:=w s l fun i=> (le_max_right ..|>.trans (le_max_right ..)).trans (V i); obtain ⟨m,m'⟩:=Q s fun i=>(le_max_left ..|>.trans (le_max_right ..)).trans (V i)
 have hp:Tendsto (fun i=> riseX (tinyBill i) (bluePin i-(0:ℕ→ Cover) i)) atTop (𝓝 X):=by
    refine tendsto_const_nhds.congr fun k=>?_; rw [Pi.zero_apply,sub_zero]; ext i; rw [basis_eq]; change _=((bluePin k i:ℤ):ℝ)/_; by_cases p:i= (3:Axis)<;>simp [bluePin,tinyBill,p]; field_simp
 have h':Tendsto (fun i=> tinyBill i^8/clearBill i) atTop (𝓝 0):= by
    apply (tendsto_inv_atTop_zero.comp he).congr; intro i; have h:= tinyB_pos i; change _⁻¹=_^8/_^9; field_simp
 have hy: X≠0:=norm_pos_iff.mp (basis_norm (3:Axis) ▸ one_pos); obtain ⟨α,t,H₁,tA,tB,Y',A,Z⟩:= violet_simultaneous T u
 refine ⟨P,K,T,r,f,s,rS,m,P.gilded goldF goldF bluePin 0 clearB_pos s tinyB_pos he hp hy h' (P.coverRise goldF goldF bluePin 0 clearB_pos s R),a,α,t,H₁,tA,tB,Y', ?_⟩
 filter_upwards [Z] with i v; obtain ⟨x,W,b,h,l⟩:=v _ (p.and (m'.and xA)); obtain ⟨J⟩:= P.ellisP 3 x K; refine ⟨x,b,W.2.1,fun j=>P.gilded goldF goldF bluePin 0 clearB_pos s tinyB_pos he hp hy h' (P.coverRose j goldF goldF bluePin 0 clearB_pos s x W.1),W.2.2,h,J,Spine.final_issues K J b,fun z=>?_⟩; have hx:=fertile (Window.family z) rS W.2.2 keyV_go (b.2.1.accepted 3); exact ⟨(l z).1,(l z).2, voyaged rS W.2.2 keyV_go K z,hx, Spine.portrayer J rS W.2.2 hx⟩
end Prototype
/- for contiguous output, include estimates & applications types -/
#check @Spine.Estimable.spends
#print axioms Spine.Estimable.spends
#check @Spine.Nuptials
#print axioms Spine.Nuptials
#check @Spine.priceV
#print axioms Spine.priceV
#check @Hiro.prices_dice
#print axioms Hiro.prices_dice
#check @Hiro.diced
#print axioms Hiro.diced
#check @Papal.chicory
#print axioms Papal.chicory
#check @Spine.condorM
#print axioms Spine.condorM
#check @Hiro.layoverMenu
#print axioms Hiro.layoverMenu
#check @Spine.jade_flat
#print axioms Spine.jade_flat
#check @Spine.theater_disjoint
#print axioms Spine.theater_disjoint
#check @Spine.PrepCost.reaches
#print axioms Spine.PrepCost.reaches
#check @Spine.servedAt
#print axioms Spine.servedAt
#check @Spine.actual_connected
#print axioms Spine.actual_connected
#check @Spine.proper_message
#print axioms Spine.proper_message
#check @Spine.centroid_empty
#print axioms Spine.centroid_empty
#check @Spine.supper_money
#print axioms Spine.supper_money
#check @Spine.supper_law
#print axioms Spine.supper_law
#check @Prototype.twilight_tradition
#print axioms Prototype.twilight_tradition
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
