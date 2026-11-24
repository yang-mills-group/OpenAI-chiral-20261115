import YM.Sextet.Stage
import YM.Sextet.Kernel
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000
set_option maxHeartbeats 280000
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

open YM.Sextet.Quadrature
variable (P: Spine)
def tags (t:ℕ) : Cover →+ P.VMark where
  toFun:=P.vtile t
  map_zero':=funext fun _=>notch_zero ..
  map_add' _ _:=funext fun _=>notch_add ..
lemma tags_all (z:P.VMark) : ∀ᶠ t in atTop,∃q,P.tags t q=z := by
  let A:=fun _:Unit=>P.macroBody default 0 0
  filter_upwards [P.vmarks A [()] (fun _=>z)] with i hi
  obtain ⟨r,_,w⟩:=hi
  exact ⟨_,w () List.mem_cons_self⟩
lemma grid_node (i:ℕ) (q:Cover) : P.grid i q = node (P.macroTick i) q :=
  funext fun _=>P.grid_eq ..

section Mist
variable (a:Axis) (x:P.Spectrum0 a) (j:Axis)
local notation "ξ"=>P.advocate a x j
local notation "H'"=> (P.ColorHil j ξ).space
local notation "H"=> (P.ManyF j ξ).space
local notation "π"=> P.enter j ξ
local notation "Φ"=> P.wealth j ξ
local notation "U'"=>P.truck j ξ
local notation "U"=>P.cartage j ξ

def fourStage : Stage Axis (H') (P.VMark) where
  η:=P.macroTick
  loc:=P.laysM
  tag:=P.tags
  «U»:=U'
  pos:=P.macroTick_pos
  shrink:=P.macroTick_null
  labels:=P.grid_node
  eventual:=P.tags_all
  contract:=fun _ _=>(P.truck_norm j ξ ..).le
  operate:=fun z w _=> by rw [P.truck_paves];rfl

-- Bochner convention checks (implicit instances after spelling out the P-types)
example : (inferInstance:NormedSpace ℝ (H'))=NormedSpace.restrictScalars ℝ ℂ (H') := rfl
example : (inferInstance:NormedSpace ℝ (H))=NormedSpace.restrictScalars ℝ ℂ (H) := rfl

lemma vehicle_limit (J:P.Ellis a x)
    (f:Vantage→ H') (g:Continuous f) (b:HasCompactSupport f) :
    Tendsto (fun i=> (P.macroTick i)^4 • ∑ᶠq,U' (P.vtile i q) (f (P.grid i q)))
      atTop (𝓝 (π (∫y, U y (Φ (f y))))) := by
  let S:=P.fourStage a x j
  let G:=fun y:Vantage=> U y (Φ (f y))
  let F:=fun y=> π (G y)
  have u:Continuous G:= P.caravan j ξ id _ continuous_id ((Φ).continuous.comp g)
  have v:Continuous F:= (π).continuous.comp u
  have t:HasCompactSupport F := by
    refine .of_support_subset_isCompact b ?_
    intro y m; refine subset_closure (s:=support f) (fun e=>m ?_)
    unfold F G;rw [e,map_zero,map_zero,map_zero]
  have h:∀ε:ℝ,0<ε→∀ᶠ n in atTop, (J.mistT n).holds fun z=>‖S.loc z‖< ε := by
    intro ε e
    filter_upwards [J.owned ε e] with i hi
    apply (J.mistT i).promotes _ hi
    intro z j
    apply (pi_norm_lt_iff e).mpr
    simpa [VClose,S,fourStage] using j
  have k (y:H') : Tendsto (fun n=> S.mean (J.mistT n) y) atTop (𝓝 (π (Φ y))) := J.shaky j y
  have m(i:ℕ)(q:Cover) : S.U (S.tag i q) (π (Φ (f (node (S.η i) q))))=
      F (node (S.η i) q) := by
    let g:=node (S.η i) q
    have eq:P.laysM (P.vtile i q)=g:= P.grid_node i q
    exact (P.cart_and j ξ (P.vtile i q) (Φ (f g))).trans (by rw [eq])
  rw [←(π).integral_comp_comm]
  refine (S.expand b J.mistT h _ k g v t m).congr ?_
  intro i
  have y:S.load f i=(fun q=> U' (P.vtile i q) (f (P.grid i q))) := by
    funext q; simp only [P.grid_node]; rfl
  change S.fare f i=_
  rw [Stage.fare,y];rfl
end Mist

/- Quadratures in exact length unit at the chosen pose.
Weights `f` here are always **real**. Opposition smear in a reflected-pair test
uses the pullback by third-axis reflection; use before-smears on the opposed mark
as written, i.e., already in the desired poses (no further reversal at the wall).
Functions f must have compact support, and billed centers must allow both widths
on the indicated sides. The grid sum uses the axis-3 directions even at a real wall c
with neither time leg individually a grid length. -/
section Smoothed
variable (x:P.Spectrum0 3) (Z:Lead.Clan) (s n:ℕ) (c:ℝ) (f:Vantage→ℝ)

def fineSense (t:ℕ) :=
    (P.macroTick t)^4 • ∑ᶠ q, (f (P.grid t q):ℂ) • (P.gridWall x Z s n c t q)

def realSense := ∫ y:Vantage, (f y:ℂ) • P.vectorWall x s n Z c y

local notation "ξ"=>P.advocate 3 x 3
local notation "U"=>P.cartage 3 ξ
local notation "E"=> (P.physicalEnergy 3 ξ).E
local notation "W"=>P.wealth 3 ξ

lemma realSense_cont (h:Continuous f) :
    Continuous (fun y:Vantage=> (f y:ℂ) • P.vectorWall x s n Z c y) := by
  have time : Continuous (fun y : Vantage => toWall c (y 3)) :=
    toWallCont.comp (continuous_const.prodMk (continuous_apply (A := fun _ : Axis => ℝ) 3))
  have heat := ((P.seasons 3 ξ).continuousE (P.macroVector x Z s n)).comp time
  have wall := P.caravan 3 ξ (id : Vantage → Vantage) _ continuous_id heat
  unfold vectorWall
  exact (Complex.continuous_ofReal.comp h).smul wall
lemma realSense_support (b:HasCompactSupport f) :
    HasCompactSupport (fun y:Vantage=>(f y:ℂ) • P.vectorWall x s n Z c y) := by
  refine .of_support_subset_isCompact b ?_
  intro y p; refine subset_closure (s:=support f) (fun k=>p ?_)
  change (f y:ℂ) • _ = _
  change f y=0 at k
  rw [k,Complex.ofReal_zero,zero_smul]
lemma realSense_ing (h:Continuous f) (b:HasCompactSupport f) :
    Integrable (fun y:Vantage=> (f y:ℂ) • P.vectorWall x s n Z c y) volume :=
  (P.realSense_cont x Z s n c f h).integrable_of_hasCompactSupport (P.realSense_support x Z s n c f b)

theorem smoothed_motion (J:P.Ellis 3 x) (h:Continuous f) (b:HasCompactSupport f) :
    Tendsto (P.fineSense x Z s n c f) atTop (𝓝 (P.enter 3 ξ (P.realSense x Z s n c f))) := by
  let k:=P.sourceVector x Z s n
  let F:=fun y:Vantage=> (f y:ℂ) • (E (toWall c (y 3)) k)
  have p:Continuous F:= (Complex.continuous_ofReal.comp h).smul
    (((P.physicalEnergy 3 ξ).continuousE _).comp
      (toWallCont.comp (continuous_const.prodMk (continuous_apply _))))
  have q:HasCompactSupport F:= by
    refine .of_support_subset_isCompact b ?_
    intro y a; refine subset_closure (s:=support f) (fun t=>a ?_)
    change f y=0 at t
    unfold F; rw [t,Complex.ofReal_zero,zero_smul]
  have I:=P.vehicle_limit 3 x 3 J F p q
  have i:(fun y=>U y (W (F y)))=(fun y=> (f y:ℂ) • P.vectorWall x s n Z c y):=by
    funext y
    have hv:W (E (toWall c (y 3)) k)=(P.seasons 3 ξ).E _ (P.macroVector x Z s n):=P.bankHeat ..
    unfold F; rw [map_smul,hv,map_smul];rfl
  rw [i] at I
  refine I.congr fun t=>?_ 
  have e:(fun q=>P.truck 3 ξ (P.vtile t q) (F (P.grid t q)))=
     (fun q=> (f (P.grid t q):ℂ) • P.gridWall x Z s n c t q) := by
    funext q;unfold F; rw [map_smul]; rfl
  rw [e]; rfl
end Smoothed
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
