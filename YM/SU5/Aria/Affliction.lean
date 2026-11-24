import YM.SU5.Aria.Grotto
import YM.SU5.Cheer.Harp
set_option maxHeartbeats 250000
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
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
namespace Spine
open Aria Set
open Cheer (Narrow)
variable (P:Spine)(x:P.Spectrum0 3)(Z:Lead.Clan)(s n:ℕ)
local notation "K"=> P.calibration
local notation "Λ"=> P.par
local notation "R"=> ruler P.par.block
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 (P.advocate 3 x 3)
local notation "Ω"=> P.heaven 3 (P.advocate 3 x 3)
local notation "ω"=> P.colorZero 3 (P.advocate 3 x 3)
local notation "S"=> P.seasons 3 (P.advocate 3 x 3)
local notation "G"=> P.ManyF 3 ξ
local notation "L₀"=>P.leftX Z s n
local notation "L₁"=>P.rightX Z s n
local notation "η"=> P.pairStory Z s n
local notation "p"=> P.stockS Z (P.flash n)
local notation "Σ₀"=> Prod.fst (α:=P.Apron) (β:=Vantage)
local notation "Σ₁"=> Prod.snd (α:=P.Apron) (β:=Vantage)
local notation "Χ" L:max=> P.commonWell 3 x Σ₀ Σ₁ L
variable (J:P.Ellis 3 x)
local notation "κ"=> P.cartage 3 ξ
local notation "u"=> P.palp s
local notation "E"=> (S).E
local notation "F"=>P.crownT Z s n
local notation "Z'"=> P.allowance x Z s n
local notation "Δ"=> P.lucid x Z s n
local notation "a"=>P.markX s
noncomputable def pulse0 := P.parses 3 (P.otherSpectrum 3 3 x) [P.leftX Z s n]
lemma honorPulse : P.pulse0 x Z s n=E a Δ:= (P.entersAt 3 ξ F a).trans (congrArg (fun y:H=> E a (P.wealth 3 ξ y)) (P.seeding x Z s n))
lemma spinP : P.parses 3 ξ [P.rightX Z s n]= κ u (P.pulse0 x Z s n):=by
 rw [P.parsesOne 3 ξ _ (P.rightFare ..)]; let v:= κ; let S':= P.announce 3 F a; let X:= P.tableau 3 ξ; let y:= v u (v (S'.2) (P.wealth 3 ξ ((F).engine P 3 ξ ω)))
 have hh : v (S'.2)=ContinuousLinearMap.id ℂ _:= P.cart_aisle 3 ξ _
 change E _ (X (S'.2+u) _ Ω)=_; unfold X; rw [P.tableMaps]; rw [add_comm S'.2, P.cart_paves,ContinuousLinearMap.comp_apply,show (L₁).1=F from rfl, P.seeding x Z s n, (show κ (S'.2)=_ from hh), P.warm_drive, ContinuousLinearMap.id_apply]; exact congrArg (v u) (honorPulse ..).symm
include J
lemma commons_single (D:P.Apron)(v:Vantage) : Χ [((D,v):P.Model0)]= P.singleState 3 D.s ξ D.F:=by
 let y:P.Model0:=(D,v); let L:=[y]; have he:P.Turnstile (3:Axis) Σ₀ L Σ₁:= List.pairwise_singleton ..; let T:=D.engine P 3 ξ; let f:= D.cardB P 3;
 rw [P.common_cult 3 x _ _ _ J (List.Perm.refl L) he]; unfold memorial; rw [← rector_view (S) Ω _ _ _ (P.heaven_hot 3 ξ) 0]; change inner ℂ Ω (E _ (P.tableau 3 ξ v T Ω))= _; rw [← OS.Semigroup.swing, P.heaven_hot]; rw [P.tableMaps];
 have h(z:G) : inner ℂ Ω (κ v z) = inner ℂ Ω z:= by have ht:= P.inner_pay 3 ξ v Ω z; rw [P.cart_empty] at ht; exact ht -- rewriting deep?
 have hz(y:H): inner ℂ Ω (P.wealth 3 ξ y)= inner ℂ ω y:= by rw [← ContinuousLinearMap.adjoint_inner_left (P.wealth 3 ξ), P.bank_star]; rfl
 rw [h,hz, P.engine_view, P.view_scalar, D.card_price,P.slide_single]
lemma single_pays : (Χ [L₀])= Z'∧ (Χ [L₁])= Z' ∧ (Χ [(P.turnModel 3 L₀)])= star Z':=by
 let S':= Vantage; have h:P.singleState 3 s ξ (P.shifts 3 ((F).u 3:ℤ) (F).F)=Z':= congrArg _ (P.ordained Z s n).2.1; rw [P.slide_single] at h;
 have g(v:Vantage): Χ [((F,v):P.Model0)]=Z':=(P.commons_single x J F v).trans (by rw [(P.ordained Z s n).1,h]);
 have toi (D:P.Apron)(f:Vantage) : Χ [(P.turnModel 3 (D,f))] = star (Χ [((D,f):P.Model0)]) := by
    change Χ [(((D.kiss P 3),mirrorΩ 3 f):P.Model0)]=_; rw [P.commons_single x J,P.commons_single x J]
    let z:=D.s; change P.singleState 3 z ξ (P.reflectTest 3 D.F)=_; exact (congrArg (P.chi 3 ξ) (P.reading_star 3 z D.F).symm).trans (map_star ..)
 exact ⟨g _,g _,(toi _ _).trans (congrArg star (g _))⟩
omit J in
private lemma tenor (X:Hilbert)(S':OS.Semigroup X (3:Axis))(t:ℝ≥0)(W:X.Op)(F':X)(h:∀ u':X,S'.E t (W u')=W (S'.E t u')): inner ℂ (S'.E t F') (W (S'.E t F'))=inner ℂ F' (W (S'.E (t+t) F')):=by rw [S'.swing,h,←ContinuousLinearMap.comp_apply (S'.E t),← S'.time]
lemma doublet_ready : Χ (P.pairStory Z s n)= inner ℂ Δ (κ u (E (a+a) Δ)):=by
 let E₀:=E a; let A:=P.leftX Z s n; let B:=P.rightX Z s n; have he:(Χ (P.pairStory Z s n))=inner ℂ (P.pulse0 x Z s n) (P.parses 3 ξ [B]):=(P.common_cult 3 x Σ₀ Σ₁ _ J (List.Perm.refl η) (P.order_here Z s n 3)).trans (P.common_self 3 ξ _ _ (P.singleCrew Z s n).1.2 (P.singleCrew Z s n).2.2 (P.singleCrew Z s n).1.1 (P.singleCrew Z s n).2.1).symm
 exact he.trans ((congrArg₂ (inner ℂ) (P.honorPulse x Z s n) ((P.spinP x Z s n).trans (congrArg ((κ) u) (P.honorPulse x Z s n)))).trans (tenor G S a (κ u) Δ (P.warm_drive 3 ξ u a)))
omit J
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
