import YM.SU5.SatinWard.Resolution.NeedleY
import YM.SU5.Registration.Ink.RegEu
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
open SatinRegistration Swatch _root_.YM.SatinWFixed _root_.YM.Boundary
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin (Each)
-- unpadded.Time. B on same H, antenna. prove hologram interior Eu.A.Marks. generic strict-off ordering.
variable (v:P.Spectrum0 3)
local notation "Xₐ"=> P.advocate 3 v 3
local notation "H"=> P.ManyF 3 Xₐ
local notation "Ω"=> P.heaven 3 Xₐ
local notation "S"=> P.seasons 3 Xₐ
variable {Vt:Type*}[AddCommGroup Vt][Module ℂ Vt] (B:Carton (P.seasons 3 (P.advocate 3 v 3)) Vt)(W: InkWaves Vt)(Z: WView Vt)(w:InkPort B W Z)(p:B.omega=P.heaven 3 (P.advocate 3 v 3))
variable (A L:P.LagOp 3 (P.advocate 3 v 3))(t j:ℝ)(X Y:Vt)(q:skit)(pt:0<t)
local notation "Tm"=> Real.toNNReal t
variable (F:B.bar t.toNNReal X=A t t)(G:B.bar t.toNNReal Y=L t t)(h: straight 3 t q) -- h clash
local notation "ℓ"=> t
noncomputable abbrev fiat (y:Vantage):E4:= WithLp.toLp 2 y
noncomputable abbrev cameo : Points 2:= WithLp.toLp 2 ![fiat (q false),fiat (q true)]
noncomputable abbrev dot (q:Vantage): Points 1:= WithLp.toLp 2 fun _=> fiat q
private lemma purse₁ {Y1:ℝ≥0→(H).Op} (b: SatinRegistration.Sound S Y1) (pt:0<t)(y:Vantage) (k:ℝ)(F:Y1 Tm=A t t) (hk: k+y 3+t=y 3+t) : P.orbitCut v 3 Y1 (y 3-t) (y 3+t+k) y= scepter P 3 Xₐ y t t A :=by
 have e:=Real.toNNReal_pos.mpr pt; have h₀:k=0:=by linarith only [hk]
 subst k; unfold orbitCut; rw [add_zero,sub_sub_cancel, add_sub_cancel_left]; unfold bothPads; rw [min_self,tsub_self,show (S).E 0=(1:(H).Op) from (S).eZero]; rw [one_mul,mul_one,F] <;> rfl
private lemma runPlus (k j:ℝ)(t₁:k≤j)(t₀:0≤k):Real.toNNReal j-Real.toNNReal k=Real.toNNReal (j-k):=by rw [NNReal.sub_def,Real.coe_toNNReal _ t₀,Real.coe_toNNReal _ (t₀.trans t₁)]
include F p pt w
lemma price_dot (q:Vantage) : SingleF P 3 Xₐ A q t= axisSweep W (fun _:Fin 1=> X) (dot q) := by
 let u(_:Fin 1):=q 3-t; let y(_:Fin 1):=q 3+t+0
 have g: flightTimes (dot q)∈ east 1:=fun _ _ p=> by omega -- strictMono implicit
 let k:=(fun _:Fin 1=> q); have he:qua (dot q)=k:=rfl; have hx:Each 1=[0]:=by decide +kernel
 rw [←P.cut_wick v B W Z w _ (dot q) p g u y ?_]; swap; · rw [he,hx]; refine ⟨fun i _=> ?_,fun a b t w K=>?_⟩; unfold k u y; constructor <;> linarith only [pt]; have e:= congrArg List.length K; simp only [List.length_cons,List.length_append,List.length_nil] at e; omega
 unfold ChartPrice ChartOp; rw [he,hx]; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; unfold k u y; rw [purse₁ P v A _ (B.coherent X) pt q _ F (by rw [zero_add])]
include G h
lemma price_scene : Cruise P 3 Xₐ A L q ℓ=axisSweep W ![X,Y] (cameo q):=by
 let a:=q false; let b:=q true; let y:=cameo q; let m:=a 3; let n:= b 3; let f:Fin 2→ℝ:=![m-ℓ,m+ℓ]; let g:Fin 2→ℝ:=![m+ℓ+0,n+ℓ]; let Q:= qua y; let L₁:=Each 2; have he: m+ℓ+ℓ<n:=by change _<_-_ at h; unfold m n a b; linarith only [h] -- change may fail
 have hq: Q=![a,b]:=by ext1 i; fin_cases i <;> rfl
 have hθ:flightTimes (cameo q)∈east 2:=by
    intro i j k; have x:i=0:=by omega
    have y:j=1:=by omega
    subst i j; change m<n; linarith
 have hx:Each 2=[0,1]:=by decide +kernel
 have uℓ: Dressing 3 (Each 2) (qua (cameo q)) f g:=by
    change Dressing 3 (Each 2) Q _ _; rw [hq,hx]; refine ⟨fun i _=>?_, fun t u w v z=>?_⟩
    · fin_cases i
      · change m-t < m ∧ m < m+ℓ+0; constructor<;>linarith
      · change m+t <n∧ n<n+t; constructor<;>linarith
    have h:= congrArg List.length z; simp only [List.length_cons,List.length_append,List.length_nil] at h; have hw: w=[]:=List.length_eq_zero_iff.mp (by omega); have hv:v=[]:=List.length_eq_zero_iff.mp (by omega); rw [hw,hv] at z; have hy:0=t∧1=u:=by simpa using z
    rw [←hy.1, ←hy.2]; exact add_zero _
 rw [← P.cut_wick v B W Z w _ _ p hθ f g uℓ]; unfold ChartPrice ChartOp; rw [hx, show qua (cameo q)=![a,b] from hq]; simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; change Marble.hotPair S Ω (n-m-2*t) (scepter P 3 Xₐ a t t A) (scepter P 3 Xₐ b t t L)= Marble.whisper Ω (P.orbitCut v 3 (fun p=> B.bar p X) (m-t) (m+t+0) a * P.orbitCut v 3 (fun p=>B.bar p Y) (m+t) (n+t) b)
 rw [purse₁ P v A _ (B.coherent X) pt a _ F (by rw [zero_add]),P.orbitCut_precise v 3 _ (B.coherent Y) _ _ _ Tm (Real.toNNReal_pos.mpr pt) (Real.toNNReal_mono (by change t≤ n-(m+t); linarith only [he])) (le_of_eq (by change Tm=Real.toNNReal (n+t-n); rw [add_sub_cancel_left])), G] -- lambda rw
 rw [show n+t-b 3=t from add_sub_cancel_left n _,tsub_self,show (S).E 0=(1:(H).Op) from (S).eZero,mul_one, show b 3 =n from rfl,runPlus t (n-(m+t)) (by linarith only [he]) pt.le, show n-(m+t)-t=n-m-2*t by ring]; unfold hotPair; rw [mul_assoc] <;> rfl
#print axioms price_dot
#print axioms price_scene
end Polaris
end Regulator
end Fame
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine
