import YM.SU5.SatinWard.Resolution.PavilionY
import YM.SU5.SatinWard.Resolution.Broadie
import YM.SU5.SatinWard.Resolution.Waive
import YM.SU5.SatinWard.Resolution.Belfry
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 700000
set_option maxRecDepth 8000
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
open BProof Pressure
namespace Regulator

open _root_.YM.Gleam.Luster.Almanac Grade
open Papal.SkyTax
open _root_.YM.Regis.Head
open _root_.YM.Gleam.Luster.Almanac Grade
open _root_.YM.CF.Py.Rate.LocalLimit.Preparation _root_.YM.CF.Py.Rate.LocalLimit.Preparation.Tabletop Shrine Ione.Clock Moto
variable (P:Spine)
local notation "W★"=>P.calibration
local notation "Ω★"=>P.run.meter
open Preparation.Yoke Spine.Gingham Spine.Gingham.Diary
open ShapeLab ResolutionFrame Shrine 
open SatinWard
variable {m n:ℕ}(td Pay Γ kC:ℝ)(Tξ:Hove.Grant P.par.K.j 2)(Z V F W:ℝ→ℝ)
variable {f:ℕ→ℕ}(p:Tendsto f atTop atTop)
open Harmonic RecruitW LitCurrent LitCurrent.Chamber
open CasaF
abbrev PitchZ:= Coords Wage4×Coords Wage4×Coords Wage3
variable (η:Type)[Fintype η]{f0 q v j:ℕ}{b a φ H A:ℝ}
local notation "Dc"=> LitCurrent.Chamber.Division
local notation "J⌂"=> P.jump128
local notation "τv" v:max i:max k:max=> eraτ P.run v i k j a φ
local notation "Y₀"=> P.run
local notation "Cc"=> yardF (spinFrame 3)
local notation "Cs"=> yardF cloverFrame
local notation "R$" c:max=>Rearward P η j c H A a b φ
variable (Zμ: Rearward P η j f0 H A a b φ)
local notation "πv" i:max=>P.nomadic i
local notation "κv" i:max=> P.engine i
-- arithmetic.Later store C* & direction count. Dossier recorded valuations along whole path. For comparison outputs choose register orientation W boundary ONCE, respect paths by subselections.
structure Ceremo (P:Spine)(η:Type)[Fintype η](v j f0:ℕ)(a b φ H A:ℝ)(D:Dc) (Z:ℕ→ℕ) (p:Visit→ Cover→Family P.calibration)(x:PitchZ) :Prop where
 anchor : ∃ (E:(n:ℕ)→eraτ P.run v (P.nomadic (Z n)) (P.engine (Z n)) j a φ) (F:ℕ→ Visit→ Cover→ Family P.calibration)(W:ℕ→PitchZ),
   Tendsto W atTop (𝓝 x) ∧ Broadside P.run P.large v (P.nomadic∘Z) (P.engine∘Z) E D F p ∧
   ∀ n, let i:= P.nomadic (Z n); let k:=P.engine (Z n); Satin.PairIdx P.run v i k ∧ MaskPoint P.run j v i k a b∧ Lockreef P η f0 v i k H A D (E n) (W n).1 (W n).2.1 (W n).2.2
-- stable under further refinement. necessary chronology
namespace Ceremo
variable {p:Visit→ Cover→Family P.calibration}{x:PitchZ}{D:Dc}{g:ℕ→ℕ}(u:Ceremo P η v j f0 a b φ H A D g p x)
include u
lemma persist {k:ℕ→ℕ}(v':Tendsto k atTop atTop): Ceremo P η v j f0 a b φ H A D (g ∘ k) p x:=by
 obtain ⟨E,F,S,t,h,m⟩:=u.anchor
 refine ⟨⟨fun i=> E (k i),F ∘ k,S∘k,t.comp v',⟨h.valid,fun _=> h.grants _,fun p a=> ?_,fun _ _ _=> h.learns _ _ _⟩,fun _=>m _⟩⟩
 obtain ⟨t,u,⟨C,v,p',q⟩,z⟩:=h.bills p a; exact ⟨fun _=>t _,u,⟨C,v,p',v'.eventually q⟩,fun h p=> v'.eventually (z _ p)⟩
noncomputable abbrev baseZ :ℝ:= max (2*(1+4*(cloverFrame.pulseHidden P.par.R.L (yardF cloverFrame) H A))) (2*(1+4*((spinFrame 3).pulseHidden P.par.R.L (yardF (spinFrame 3)) H A)))
omit u in
lemma bornZ {k i:ℕ}(E:eraτ P.run v i k j a φ)(x:PitchZ)(p:Lockreef P η f0 v i k H A D E x.1 x.2.1 x.2.2): ‖x‖≤ (baseZ (H:=H) (A:=A) P):=by
 rw [Prod.norm_def,Prod.norm_def]; exact (max_le (p.stakeQ.sizeZ.trans (le_max_left ..)) (max_le (p.stakeS.sizeZ.trans (le_max_left ..)) (p.stakeJ.sizeZ.trans (le_max_right ..))))
lemma spentZ : ‖x‖≤(baseZ (H:=H) (A:=A) P):=by obtain ⟨E,F,S,t,h,m⟩:=u.anchor; exact le_of_tendsto t.norm (Eventually.of_forall fun i=>bornZ P η (E i) (S i) (m i).2.2)
lemma earnedZ :∀ u:Visit,Domicile (hourBound P.run v) (p u):=by obtain ⟨E,F,S,t,h,m⟩:=u.anchor; exact h.valid
end Ceremo
open Ceremo
include Zμ p
lemma attended (D:Dc) (u:f0 ≤ v)(e:0<a): ∃ L:ℕ→ℕ, StrictMono L ∧ ∃ F G, Ceremo P η v j f0 a b φ H A D (f ∘ L) F G:=by
 -- choose Mask+eraτ+receipts were insp.Per rotor.
 let i(u:ℕ):=πv (f u); let k(u:ℕ):=κv (f u)
 let h:∀ᶠ n in atTop, ∃ E:eraτ P.run v (i n) (k n) j a φ, ∃ S:PitchZ, Satin.PairIdx P.run v (i n) (k n) ∧ MaskPoint P.run j v (i n) (k n) a b∧ Roomy (pavilion (nodeC (0:Cover)) (hourBound P.run v)) (side P.run (i n) v) ∧ Lockreef P η f0 v (i n) (k n) H A D E S.1 S.2.1 S.2.2:=by
    filter_upwards [(P.stockGo.comp p).eventually (Zμ.flow v u), (P.stockGo.comp p).eventually (roomyTail P.run P.large v (pavilion (nodeC (0:Cover)) (hourBound P.run v))), p.eventually (marches P (v+1))] with n F T K
    let V':Satin.PairIdx P.run v (i n) (k n):=⟨K.1, (Nat.lt_succ_self v).trans K.2⟩
    obtain ⟨Q,⟨B⟩,t⟩:= F (k n) K; obtain ⟨u,v,w,e⟩:=t D B; exact ⟨B, (u,v,w), V',Q, T,e⟩
 obtain ⟨c,h⟩:=eventually_atTop.mp h; choose E F Y' C' M' V' using fun i:ℕ=> h (c+i) (by omega)
 obtain ⟨G,hG,r,vR,A'⟩:= (isCompact_closedBall (0:PitchZ) (baseZ (H:=H) (A:=A) P)).tendsto_subseq (fun i=> (mem_closedBall.mpr ((dist_zero_right (F i)).trans_le (bornZ P η (E i) (F i) (V' i)))))
 let I:=fun n:ℕ=>c+r n; obtain ⟨L,Z',Yd,U,t⟩:= broad P.run P.large v (i∘I) (k∘I) (fun i=>(Y' (r i)).2) (fun i'=> C' (r i')) (fun i'=> E (r i')) D (fun i'=> M' (r i')) e
 refine ⟨I∘ L,?_ , Yd,G,⟨⟨fun i'=> E (r (L i')),Z',F ∘r∘ L,A'.comp U.tendsto_atTop,t,fun i=>?_ ⟩⟩⟩ -- constructors issue nested
 · exact (show StrictMono I from fun a b h=> Nat.add_lt_add_left (vR h) _).comp U
 exact ⟨Y' _,C' _,V' _⟩
#print axioms Ceremo.persist -- open
#print axioms attended
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
