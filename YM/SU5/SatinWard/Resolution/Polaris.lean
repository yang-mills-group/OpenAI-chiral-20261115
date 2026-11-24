import YM.SU5.SatinWard.Resolution.Wand
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

open Worth Pays BProof Aria Casting MacroGrid Selected OS.Semigroup OS.Semigroup.Marble PSE MarbleFace
namespace Polaris
abbrev skit : Type:= Bool → Vantage
/- pose space. physical payment also in spacelike.CPI.Current.T.M Needs all orientations paid. `Γρ` is lags bought for the query, while `|width|<t` actual admissibility. -/
variable (pv:skit)(ℓ:ℝ)(i:Axis) (x:P.Spectrum0 i)
abbrev Cruise (A B:P.LagOp i x)(pv: skit)(u:ℝ): ℂ:= Marble.hotPair (P.seasons i x) (P.heaven i x) (pv true i-pv false i-2*u)
  (scepter P i x (pv false) u u A) (scepter P i x (pv true) u u B)
abbrev Harbor (A B:P.LagOp i x) (p:skit) (u:ℝ): ℂ:= Marble.seam (P.seasons i x) (P.heaven i x) (p true i-p false i-2*u)
  (scepter P i x (p false) u u A) (scepter P i x (p true) u u B)
abbrev SingleF(A:P.LagOp i x)(p: Vantage)(u:ℝ):ℂ:= Marble.whisper (P.heaven i x) (scepter P i x p u u A)
abbrev straight(T:ℝ)(p:skit):Prop:= 2*T < p true i-p false i
abbrev broadV(T:ℝ)(p:skit):Prop:= ∀ k:Axis,2*T < |p false k-p true k|
variable (A:Bool→P.Apron) (e: Vantage)(c:Bool→ℂ)(l r:ℝ) (b:Bool)
def Unchained (T:ℝ): Prop:= ∀ (k:Bool)(i:Axis), |e i|+(A k).realWidth P i≤ T
local notation "Φ" => fun i:Bool=> pv i-e
-- for all charts and lags. rotation-frame ops still.
variable (u:A true=A true) {v:ℕ}(t:∀ i,(A i).s=v) (y:Bool→ Cover) (Y:P.laysM ∘P.vtile v ∘ y=fun i=>pv i-e) (hu:Unchained P A e ℓ)
local notation "Eu"=> P.ManyF i x
local notation "N"=> P.seasons i x
local notation "Ω"=> P.heaven i x
local notation "ℛ"=> P.locate i x
local notation "R₀" b:max=> P.tableau i x (pv b-e) ((A b).engine P i x)
local notation "d₀" b:max=> (A b).realWidth P i
local notation "De" b:max => c b • (annoFace P i x (A b).s e (A b)) -- scalar site
local notation "Xa" b:max=> scepter P i x (pv b) ℓ ℓ (De b)
variable (f:straight i ℓ pv)(g:broadV ℓ pv)
include hu
lemma chain_qual (h:2*ℓ < pv (!b) i-pv b i) : P.Turnstile i A [b,!b] (fun i=>pv i-e):=by
 let x:= hu b i; have y:=hu (!b) i; refine List.pairwise_pair.mpr (?_); change pv b i-e i +(A b).realWidth P i< pv (!b) i-e i- (A (!b)).realWidth P i; linarith only [x,y,abs_nonneg (e i),h]
include g in
lemma broad_hull : P.Plenum A [false,true] (fun i=>pv i-e):=by
 refine ⟨fun k=>?_⟩; rcases le_total (pv false k-pv true k) 0 with w|w
 · refine ⟨_,List.Perm.refl _,chain_qual P pv ℓ k A e false hu ?_⟩; change 2*ℓ<pv true k-_ ; rw [←neg_sub,←abs_of_nonpos w]; exact g k
 refine ⟨_,both_perm true,chain_qual P pv ℓ k A e true hu ?_⟩; change 2*ℓ<pv false k-_; rw [←abs_of_nonneg w]; exact g k
local notation "v?"=> (fun i:Bool=> pv i-e)
omit hu
lemma celebrity : (Xa b)= c b • (N).sand (R₀ b) (ℓ-e i-d₀ b) (ℓ+e i-d₀ b):=by
 unfold scepter annoFace base hang; simp only [Pi.smul_apply,P.locate_smul,P.locate_sum,P.locate_sand,P.reprise_table]; rw [sub_eq_add_neg (pv b)]
lemma heard1 (b:Bool): c b * P.memorial i x A [b] (fun i=>pv i-e)= SingleF P i x (De b) (pv b) ℓ:=by
 unfold SingleF; rw [celebrity]; rw [MarbleFace.mem_one,show Marble.whisper Ω (c b • (N).sand (R₀ b) (ℓ-e i-d₀ b) (ℓ+e i-d₀ b))= c b* Marble.whisper Ω ((N).sand (R₀ b) (ℓ-e i-d₀ b) (ℓ+e i-d₀ b)) from inner_smul_right .., Marble.missed (N) Ω (imMemo ..)]
include f hu
lemma heard2: (c false*c true) * P.memorial i x A [false,true] (fun i=>pv i-e)= Cruise P i x (De false) (De true) pv ℓ:=by
 let b:=false; let A' := Xa b; let B:= Xa true; let V:skit:= v?; let Q:= pv true i-pv false i-2*ℓ; unfold Cruise; rw [show [false,true]=[false,!false] from rfl,mem_pair,celebrity,celebrity]
 let a0:= (R₀ b); let b0:=(R₀ true); let L(i'):=(ℓ-e i-d₀ i'); let R(i'):=(ℓ+e i-d₀ i'); let M₀:= P.porchY i A V true-P.resignY i A V false; let U:=c b; let W:=c true
 have ht:M₀= R b+Q+L true:=by unfold M₀ porchY resignY Apron.time_panel Apron.time_edge; change pv true i-e i-(A true).realWidth P i-(pv b i-e i+(A b).realWidth P i)=_; unfold R L Q b; ring
 change (U*W) * hotPair (N) Ω M₀ a0 b0= hotPair (N) Ω Q (U • (N).sand a0 (L b) (R b)) (W • (N).sand b0 (L true) (R true))
 rw [ht,← Marble.outsidePair (N) Ω Q (imMemo ..) (L b) (R b) (L true) (R true) a0 b0 (by linarith only [hu b i,neg_le_abs (e i)] : 0≤R b) (by linarith only [hu true i,le_abs_self (e i)] : 0≤ L true) (sub_nonneg.mpr (show 2*ℓ ≤ pv true i-pv false i from f.le))]; unfold hotPair Marble.whisper; rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]; simp only [smul_apply, inner_smul_right]; ring
variable (j: Axis)(x₁:P.Spectrum0 j)(J:P.Ellis j x₁)
local notation "jψ"=> P.advocate j x₁ i
local notation "PV" b:max=> (c b • P.chartAll (y b) (A b).F)
local notation "Xv" b:max=> c b • annoFace P i (P.advocate j x₁ i) (A b).s e (A b)
local notation "v₀"=> P.singleState j v x₁
include Y hu J t
include g in
lemma markerPair : Cruise P i (P.advocate j x₁ i) (Xv false) (Xv true) pv ℓ=(P.singleState j v x₁ ((PV false) * (PV true))):=by
 have h₁:P.Turnstile i A [false,true] (P.laysM ∘ P.vtile v ∘ y):=Y.symm ▸ chain_qual P pv ℓ i A e false hu f
 let W(b:Bool):= P.chartAll (y b) (A b).F; let h(b:Bool): (A b).full P v=(A b).F:=by unfold Apron.full; rw [t,Nat.sub_self]; rfl
 let turn:= P.entirely_now j x₁ A [false,true] J i (P.vtile v ∘ y) h₁ (Y.symm ▸ broad_hull P pv ℓ A e hu g)
 rw [←heard2 P pv ℓ i (P.advocate j x₁ i) A e c hu f]; rw [← Y,←turn, P.turn_purchase i _ A y v [false,true] h₁ (fun i _=>(t i).le), show P.fullScroll v _ _ [false,true]=W false*W true from ?_, P.single_agrees]; change _=v₀ ((_:ℂ) • W false * ((_:ℂ) • W true)); rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,map_smul,map_smul]; rw [mul_assoc]; rfl -- order tuning
 unfold fullScroll; simp only [List.map_cons,List.prod_cons,List.prod_nil,List.map_nil,h,mul_one]; rfl
omit f hu
lemma markerOne : (P.singleState j v x₁ (PV b))=SingleF P i (P.advocate j x₁ i) (Xv b) (pv b) ℓ:=by
 rw [←heard1 P pv ℓ i (P.advocate j x₁ i) A e c,←Y]; rw [← P.entirely_now j x₁ A [b] J i (P.vtile v ∘ y) (List.pairwise_singleton ..) ⟨fun i=>⟨_,List.Perm.refl _, List.pairwise_singleton ..⟩⟩, P.turn_purchase _ _ _ y v [b] (List.pairwise_singleton ..) (fun i _=>(t i).le),P.single_agrees,map_smul]; change c b * v₀ _=_; apply congrArg (fun u=> c b * v₀ u); unfold fullScroll; have h:(A b).full P v=(A b).F:=by unfold Apron.full; rw [t,Nat.sub_self]; rfl
 simp only [List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one,h]
end Polaris
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
