import VerifiedSatinWidthAndUVNovember4
import YM.SU5.Voyager.Canyon

/-!
# Binding the Satin supply for the Six

* `install_for_Six` (version of `installation` retaining physical
  hypotheses on the SAME `P.run`).
* `summit_on` (version of `Prototype.summit` accepting the supplied
  `uniform` `P`).
* `Spine.SixElection` (only phase and UV hypotheses needed, no probe
  specific decisions); `elect_for_Six`.

No strengthening of the coupling-existence quantifier to a prescribed
value of `P.par.x`. Run, register and character are fixed, not e.g.
re-picked at each probe scale.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

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

namespace Spine

/-- Additional flags on a uniform supply. The `run` is the one whose
readings we use. See `uniform` (`Diva/Tailor.lean`) for the other flags,
including `SeasonCert` on `R.exhibition`. -/
structure Roster (P : Spine) : Prop where
  usable : ∃ z, Usable (D:=P.par.δ) P.par.V P.par.W P.par.J P.par.N0 z P.par.delay P.run.meter
  prepared (i k : ℕ) : (((P.run.voyage i).X k).Prepared P.par.P P.par.delay)
  loom (i k : ℕ) : Advance.LoomLaw ((P.run.voyage i).CapeT k)
      (YM.SU5.FiniteGaugeData.Audit1102.lawRadius (VolumeCape.Dream.plot P.width).C)

/-- The selection and UV hypotheses we'll use from `Prototype.summit`.
Can be used on that very character (assemble from its three fields).
`x` here is the `Spectrum0` argument; the axis-hour carrier in axis 3 uses
**exactly** `P.otherSpectrum 3 3 x`. -/
structure SixElection (P : Spine) (K : P.Register) (x : P.Spectrum0 3) (c r : ℕ → ℕ) : Prop where
  launch : Launch P c r
  ready : readyUV P c r x keyV
  choose : P.party 3 K x

namespace SixElection
variable {P : Spine} {R : P.Register} {x : P.Spectrum0 3} {c r : ℕ → ℕ} (h : SixElection P R x c r)
include h

lemma star_carrier : P.lodestarHere 3 (P.otherSpectrum 3 3 x) := h.choose.2.1.accepted 3

def ellis (_h : SixElection P R x c r) : P.Ellis 3 x := Classical.choice (P.ellisP 3 x R)
lemma deck : P.LowerDeck x R h.ellis := final_issues R h.ellis h.choose
lemma summit : P.Summit x := footway x h.ellis R h.choose

end SixElection
end Spine

open CF.Velvet CF.Pannier.Chancel

/-- `Tailor.installation`, preserving the other certificates on the run. -/
theorem install_for_Six (X:Supplier)(e u:ℝ)(p:0<u) :
    ∃ (P:Spine) (R:P.Register), uniform P R X e u ∧ P.Roster :=by
  obtain ⟨x,c,q⟩:= Papal.audit_weather 4 (by decide)
  obtain ⟨Λ,l,Z,v,pL,S,Q,A0,K,H,Y,U,Pr,Lo,k,d,w,C,t,a,k',I,E,L,B,T',t',W,A⟩:=
      Papal.elite_attic e (min x u) (lt_min c p) X
  let V:= W.univ_; obtain ⟨G⟩:= extend_ground Y H V
  let P:Spine:=⟨Λ,l,Y,H,a,k',I,E,V,G⟩
  obtain ⟨x',v₀⟩:=q Λ.d Λ.dpos.le (pL.trans (min_le_left ..))
  exact ⟨P,⟨(L,B,T',t'),W⟩,⟨⟨K,v,pL.trans (min_le_right ..),A, ⟨k,d,w,Z,C,t,Q,S⟩,
        x', (Λ.kJ.symm ▸ v₀: Procurement Λ.K.j x' Λ.d)⟩, A0⟩,
      ⟨U,Pr,Lo⟩⟩

/- The next two proofs reproduce `twilight_tradition` (`Hiro/Michelin`)
and `summit` (`Voyager/Canyon`) starting *immediately after* the call to
`installation`, to allow keeping the same run, register & parameters,
e.g. supplied by `install_for_Six` (but no `Roster` needed here). -/

set_option linter.style.longLine false
open Regis.Head Regis.Head.Brecht
namespace Prototype
open Spine Lamour Bridge.Celeste Glimpse Morn Spine.RadiusF Ballad
open CF.Velvet CF.Pannier.Chancel Altitude
private lemma climbing(p:ℕ→ℕ):∃ f:ℕ→ℕ,p≤f∧StrictMono f:=by
 let f : ℕ→ℕ:= Nat.rec (p 0) (fun i v=>max (p (i+1)) (v+1)); exact ⟨f,fun i=> by cases i; exact le_rfl; exact le_max_left .., strictMono_nat_of_lt_succ (fun i=> show f i < max _ (f i + 1) from (Nat.lt_succ_self _).trans_le (le_max_right ..)) ⟩
local notation "X"=> YM.basis 3

set_option maxHeartbeats 1800000
private theorem twilight_on {L M:ℝ}{Y:Supplier} (P:Spine)(K:P.Register) (T:uniform P K Y L M) (D:ℝ)(u:0<D) (z:ℕ→ℕ): ∃ (r:ℕ→ℕ), z≤r ∧
 ∃ (c:ℕ→ℕ), ∃ B:Launch P c r, P.Estimable c r B.unitSize (fun i=>P.eReadL (c i)) ∧ P.Captive goldF goldF bluePin 0 clearB_pos c tinyBill X (fun i f=>P.E (c i) f.val) ∧ roughUV P c r keyV ∧ ∃ (α t₁:ℝ),0<α∧ 0<t₁∧t₁<D ∧ ∃ R: Glimpse.Voyage P.par.block P.calibration.ℓ 4 α (RadiusF.next P.calibration.ℓ),
     ∀ᶠ i:ℕ in atTop, ∃ x:P.Spectrum0 3, P.party 3 K x ∧ (∀ j:Axis,P.Estimable c r B.unitSize (fun i=>P.singleState j (c i) (P.otherSpectrum 3 j x))) ∧ (∀ j:Axis,P.Captive goldF goldF bluePin 0 clearB_pos c tinyBill X (fun i f=>P.singleState j (c i) (P.otherSpectrum 3 j x) f)) ∧ readyUV P c r x keyV ∧ P.funds i (P.otherSpectrum 3 3 x) R t₁ ∧
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
 filter_upwards [Z] with i v; obtain ⟨x,W,b,h,l⟩:=v _ (p.and (m'.and xA)); obtain ⟨J⟩:= P.ellisP 3 x K; refine ⟨x,b,W.2.1,fun j=>P.gilded goldF goldF bluePin 0 clearB_pos s tinyB_pos he hp hy h' (P.coverRose j goldF goldF bluePin 0 clearB_pos s x W.1),W.2.2,h,J,Spine.final_issues K J b,fun z=>?_⟩; have hx:=fertile (Window.family z) rS W.2.2 keyV_go (b.2.1.accepted 3); exact ⟨(l z).1,(l z).2, voyaged rS W.2.2 keyV_go K z,hx, Spine.portrayer J rS W.2.2 hx⟩

/-- `summit` on a supplied `P`. -/
theorem summit_on {L M:ℝ}{Y:Supplier} (P:Spine)(K:P.Register) (T:uniform P K Y L M) (D:ℝ)(u:0<D) (z:ℕ→ℕ): ∃ (r:ℕ→ℕ), z≤r ∧
 ∃ (c:ℕ→ℕ), ∃ B:Launch P c r, P.Estimable c r B.unitSize (fun i=>P.eReadL (c i)) ∧ P.Captive goldF goldF bluePin 0 clearB_pos c tinyBill X (fun i f=>P.E (c i) f.val) ∧ roughUV P c r keyV ∧ ∃ (α t₁:ℝ),0<α∧ 0<t₁∧t₁<D ∧ ∃ R: Glimpse.Voyage P.par.block P.calibration.ℓ 4 α (RadiusF.next P.calibration.ℓ),
     ∀ᶠ i:ℕ in atTop, ∃ x:P.Spectrum0 3, P.party 3 K x ∧ (∀ j:Axis,P.Estimable c r B.unitSize (fun i=>P.singleState j (c i) (P.otherSpectrum 3 j x))) ∧ (∀ j:Axis,P.Captive goldF goldF bluePin 0 clearB_pos c tinyBill X (fun i f=>P.singleState j (c i) (P.otherSpectrum 3 j x) f)) ∧ readyUV P c r x keyV ∧ P.funds i (P.otherSpectrum 3 3 x) R t₁ ∧
       ∃ J: P.Ellis 3 x,P.LowerDeck x K J ∧ Summit x ∧ (∀ᶠ m:ℕ in atTop, ∀ z:SU.Slot, P.SailV x (family z) (c m) (r m)) ∧
       ∀ z:SU.Slot, P.Intact K i R.toGaze x z t₁∧ P.Royal i ((P.otherSpectrum 3 3) x) R (family z) t₁ ∧ P.Passage x c r K z ∧ P.Bands x (family z) c r ∧ P.Portrait x (family z) c r:=by

 obtain ⟨r,t,c,B,q,U₀,U,α,t₁,pα,pt₁,h₁,R,W⟩:= twilight_on P K T D u z
 refine ⟨r,t,c,B,q,U₀,U,α,t₁,pα,pt₁,h₁,R,?_⟩; filter_upwards [W] with i h; obtain ⟨x,h,h',e,d,r',J,w,W'⟩:= h; refine ⟨x,h,h',e,d,r',J,w, footway x J K h, eventually_all.mpr ?_,W'⟩
 intro i; exact market_mink P x (family i) c r J B.unitSize (W' i).2.2.2.2
end Prototype

/-- Suffices to take **one** phase, initially. -/
theorem elect_for_Six {L M:ℝ} {Y:Supplier} (P:Spine) (K:P.Register) (T:uniform P K Y L M)
    (z:ℕ→ℕ) : ∃ r≥z, ∃ c, ∃ (x:P.Spectrum0 3), P.SixElection K x c r := by
  obtain ⟨r,t,c,B,_,_,_,α,a,_,_,_,R,W⟩ := Prototype.summit_on P K T 1 zero_lt_one z
  obtain ⟨i,x,h,_,_,d,_⟩ := W.exists
  exact ⟨r,t,c,x,B,d,h⟩

#print axioms elect_for_Six
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
