import ZecaMallard
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "ℓ"=> P.calibration.ℓ
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
open QuadClock Again Pressure
variable {s t f r v i k:ℕ}
local notation "Λ"=> P.par
/-! # Buy height and travel together. Keep both actual calibration and rank resolution schedule. -/
open CF.Pannier.Chancel CF.Py.Rate.LocalLimit.Preparation.Yoke
open Worth Pays CF.BProof
open Real (log)
open Aria Casting MacroGrid
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)

local notation "z'"=> Yoke.witnessZ
local notation "κ"=>P.sidesPerTick
local notation "κz"=> (P.sidesPerTick:ℤ)

variable (x : P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (ξ)
local notation "G"=> P.ManyF 3 (ξ)
local notation "Ω"=> P.colorZero 3 ξ
local notation "Γ"=>P.cartage 3 ξ
local notation "Η"=>P.seasons 3 ξ
local notation "π"=>P.wealth 3 ξ
local notation "Πγ"=>P.enter 3 ξ
local notation "ω"=> P.heaven 3 ξ
open Regis.Circuit -- Aster





open SatinNucleus Germ Alliance
variable
 (F:P.Nib 3 (P.advocate 3 x 3)){A C:ℝ}
 {u:ℕ→ℕ}(uf: StrictMono u) (y:ℕ→ℕ×ℕ→ℝ)(z:ℕ→ Coalition)
local notation "c"=>P.rewardK f k
local notation "Y"=> P.cinema x f k u y z uf
local notation "ρ" i:max=> (↑(P.rewardK f k * y i (f,k)):ℂ)
local notation "Lsky"=> Skyways P f k A C c u y


variable {a b:ℝ}
lemma oldFilm
    (h:NibLine P 3 ξ F Y 1) (k1:Lsky) (e:P.NightCop) (d:0<a) (t:0<b):
 Tendsto (fun i=> (ρ i) • P.crop 3 x f (u i) [] a b) atTop (𝓝 (F a b)):=by
 obtain ⟨D,D0⟩:=P.berry_bundle 3 x [] (P.folding x k1 e)
 have order:Tendsto u atTop atTop:=uf.tendsto_atTop
 let o(i:ℕ):=P.granPos f (u i) []
 have o0:Tendsto o atTop (𝓝 0):= (P.granPos_zero []).comp order
 have od:Tendsto (fun i=>o i 3) atTop (𝓝 0):=tendsto_pi_nhds.mp o0 3
 obtain ⟨T,T0⟩:=(P.folding x k1 e).charge 3 [] a b d t

 have e1:= D0.read d t (show Tendsto _ atTop (𝓝 _) from sub_zero a ▸ od.const_sub a) (show Tendsto _ atTop (𝓝 _) from add_zero b ▸ od.const_add b) o0.neg -- passed arg p:0<a-? not unify
 have eD:F a b=D a b:= by
   have hY:Tendsto (fun i=>P.roomy * P.macroStep (u i)) atTop (𝓝 (0:ℝ)):=
    mul_zero (P.roomy:ℝ) ▸ ((P.macroStep_zero.comp order).const_mul (P.roomy:ℝ))
   refine (h.dyeOne d t).unique (((D0.dye a b d t).voters z).congr' ?_)
   filter_upwards [hY.eventually (ge_mem_nhds d),hY.eventually (ge_mem_nhds t)] with i da db
   exact ((P.pleading_coin x 3 f k i (z i) u uf (fun n=>y n (f,k)) a b [] da db).trans
      (sum_congr rfl fun k _=>by simp only [Complex.ofReal_mul,mul_smul])).symm
 rw [neg_zero,P.dazzle_zero] at e1
 have α:T=D a b:=(Glaze_LocalFieldBounds.pops T0).unique e1
 rw [eD,←α]
 exact T0

#check @oldFilm
lemma downRipple
    (h:NibLine P 3 ξ F Y 1) (k1:Lsky) (e:P.NightCop)
    {rent:ℝ}
    (d:0<a) (t:0<b)
    (o:P.rosePad 3 s≤a)(m:P.rosePad 3 s≤b)
    (tm:Odessa 3 (P.roseRoot f s []) s (P.roseWide 3 s) P)
    (ka:k ≤ s)(gr:s < r)
    (rt:Tendsto (fun i=>rateQR f k c (u i) (y i) (s,r)) atTop (𝓝 rent)):
 dist (F a b) ((rent:ℂ) • P.crop 3 x f r [] a b)
       ≤ ‖(rent:ℂ)‖ * (4 * violet P.par s A) / zoomM P.par.R.L^(r-s):=by
 let g:=fun i=>(↑(rateQR f k c (u i) (y i) (s,r)):ℂ)
 have hv:Tendsto g atTop (𝓝 (rent:ℂ)):= Complex.continuous_ofReal.continuousAt.tendsto.comp rt

 have hw:=P.oldFilm x F uf y z h k1 e d t
 apply le_of_tendsto_of_tendsto (hw.dist (hv.smul_const (P.crop 3 x f r [] a b)))
       ((hv.norm.mul_const (4*violet P.par s A)).div_const (zoomM P.par.R.L^(r-s)))
 filter_upwards [uf.tendsto_atTop.eventually (eventually_ge_atTop r)] with i w
 obtain ⟨sc,_,aa,bb,fee⟩:=k1.toEngaged.wages («c»:=c) ka gr w
 exact price_brush_general _ _ _ _ _ _ ((congrArg (fun e:ℝ=>(e:ℂ)) sc).trans (Complex.ofReal_mul ..)) le_rfl

    (P.crop_buy 3 x [] fee (k1.early.le.trans ka) tm e o m).2
#print axioms downRipple
