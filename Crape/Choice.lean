import Nankin.Bern
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option maxRecDepth 6000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
set_option linter.style.longLine false
open Regis.Head Regis.Head.Brecht
namespace Prototype
open Spine Lamour Bridge.Celeste Glimpse Morn Spine.RadiusF Ballad
open CF.Velvet CF.Pannier.Chancel Altitude
private lemma climbing(p:ℕ→ℕ):∃ f:ℕ→ℕ,p≤f∧StrictMono f:=by
 let f : ℕ→ℕ:= Nat.rec (p 0) (fun i v=>max (p (i+1)) (v+1)); exact ⟨f,fun i=> by cases i; exact le_rfl; exact le_max_left .., strictMono_nat_of_lt_succ (fun i=> show f i < max _ (f i + 1) from (Nat.lt_succ_self _).trans_le (le_max_right ..)) ⟩
local notation "X"=> YM.basis 3

set_option maxHeartbeats 1800000
private theorem twilightA {L M:ℝ}{Y:Supplier} (P:Spine)(K:P.Register)(Dhome:P.Spectrum0 3 → Prop)(Dprice:∀ᵐ t∂P.pillars 3,Dhome t) (T:uniform P K Y L M) (D:ℝ)(u:0<D) (z:ℕ→ℕ): ∃ (r:ℕ→ℕ), z≤r ∧
 ∃ (c:ℕ→ℕ), ∃ B:Launch P c r, P.Estimable c r B.unitSize (fun i=>P.eReadL (c i)) ∧ P.Captive goldF goldF bluePin 0 clearB_pos c tinyBill X (fun i f=>P.E (c i) f.val) ∧ roughUV P c r keyV ∧ ∃ (α t₁:ℝ),0<α∧ 0<t₁∧t₁<D ∧ ∃ R: Glimpse.Voyage P.par.block P.calibration.ℓ 4 α (RadiusF.next P.calibration.ℓ),
     ∀ᶠ i:ℕ in atTop, ∃ x:P.Spectrum0 3, Dhome x ∧ P.party 3 K x ∧ (∀ j:Axis,P.Estimable c r B.unitSize (fun i=>P.singleState j (c i) (P.otherSpectrum 3 j x))) ∧ (∀ j:Axis,P.Captive goldF goldF bluePin 0 clearB_pos c tinyBill X (fun i f=>P.singleState j (c i) (P.otherSpectrum 3 j x) f)) ∧ readyUV P c r x keyV ∧ P.funds i (P.otherSpectrum 3 3 x) R t₁ ∧
       ∃ J: P.Ellis 3 x,P.LowerDeck x K J ∧
       ∀ z:SU.Slot, P.Intact K i R.toGaze x z t₁∧ P.Royal i ((P.otherSpectrum 3 3) x) R (family z) t₁ ∧ P.Passage x c r K z ∧ P.Bands x (family z) c r ∧ P.Portrait x (family z) c r:=by
 obtain ⟨r,f,W⟩:= outing T keyV keyV_positive z; obtain ⟨c,w⟩:= W; obtain ⟨c₀,v,w₀⟩:= climbing c; let H:= (w c₀ w₀ v).1
 obtain ⟨c₁,q⟩:= auras T (tagColors goldF goldF bluePin 0 clearB_pos) (ballotK tinyBill clearBill) (ballot_pos tinyB_pos clearB_pos); obtain ⟨h₀,Q⟩:= supplyR P T H.eager H.unitSize; obtain ⟨s,V,l⟩:= climbing fun i=>max (c₁ i) (max (h₀ i) (c i))
 have he:Tendsto tinyBill atTop atTop:=tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x:=(1:ℝ))); obtain ⟨R,p⟩:=q s fun i=>(le_max_left ..).trans (V i); obtain ⟨rS,a,xA⟩:=w s l fun i=> (le_max_right ..|>.trans (le_max_right ..)).trans (V i); obtain ⟨m,m'⟩:=Q s fun i=>(le_max_left ..|>.trans (le_max_right ..)).trans (V i)
 have hp:Tendsto (fun i=> riseX (tinyBill i) (bluePin i-(0:ℕ→ Cover) i)) atTop (𝓝 X):=by
    refine tendsto_const_nhds.congr fun k=>?_; rw [Pi.zero_apply,sub_zero]; ext i; rw [basis_eq]; change _=((bluePin k i:ℤ):ℝ)/_; by_cases p:i= (3:Axis)<;>simp [bluePin,tinyBill,p]; field_simp
 have h':Tendsto (fun i=> tinyBill i^8/clearBill i) atTop (𝓝 0):= by
    apply (tendsto_inv_atTop_zero.comp he).congr; intro i; have h:= tinyB_pos i; change _⁻¹=_^8/_^9; field_simp
 have hy: X≠0:=norm_pos_iff.mp (basis_norm (3:Axis) ▸ one_pos); obtain ⟨α,t,H₁,tA,tB,Y',A,Z⟩:= violet_simultaneous T u
 refine ⟨r,f,s,rS,m,P.gilded goldF goldF bluePin 0 clearB_pos s tinyB_pos he hp hy h' (P.coverRise goldF goldF bluePin 0 clearB_pos s R),a,α,t,H₁,tA,tB,Y', ?_⟩
 filter_upwards [Z] with i v; obtain ⟨x,Bh,b,h,l⟩:=v _ (Dprice.and (p.and (m'.and xA))); obtain ⟨Q0,W⟩:=Bh; obtain ⟨J⟩:= P.ellisP 3 x K; refine ⟨x,Q0,b,W.2.1,fun j=>P.gilded goldF goldF bluePin 0 clearB_pos s tinyB_pos he hp hy h' (P.coverRose j goldF goldF bluePin 0 clearB_pos s x W.1),W.2.2,h,J,Spine.final_issues K J b,fun z=>?_⟩; have hx:=fertile (Window.family z) rS W.2.2 keyV_go (b.2.1.accepted 3); exact ⟨(l z).1,(l z).2, voyaged rS W.2.2 keyV_go K z,hx, Spine.portrayer J rS W.2.2 hx⟩


theorem electorAE {L M:ℝ} {Y:Supplier} (P:Spine)(K:P.Register) (Dhome:P.Spectrum0 3 → Prop)(Dprice:∀ᵐ t∂P.pillars 3,Dhome t)(T: uniform P K Y L M)(z:ℕ→ℕ):∃ r≥z, ∃ c, ∃ x:P.Spectrum0 3,Dhome x ∧ ∃ J:P.Ellis 3 x,Experiment P K c r x J:=by
 obtain ⟨r,t,c,B,_,_,_,α,a,_,_,_,R,W⟩ :=twilightA P K Dhome Dprice T 1 zero_lt_one z
 obtain ⟨n,x,h,b,_,_,v,u,k,G,Z⟩:= W.exists
 exact ⟨r,t,c,x,h,k,B,v,b,G,footway x k K b⟩
#print axioms electorAE
end Prototype
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
