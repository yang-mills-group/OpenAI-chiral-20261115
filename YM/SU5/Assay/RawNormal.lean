import YM.SU5.Assay.RawLag
import YM.SU5.Assay.Normal
import YM.SU5.Assay.SandCup
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4900
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
open Aria Set OS.Semigroup
variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "K"=> P.calibration
local notation "H"=> P.ColorHil j x
local notation "B"=> P.ManyF j x
local notation "X"=> (P.ColorHil j x).Op
local notation "Y"=> (P.ManyF j x).Op
local notation "Lag"=>ℝ→ℝ→(P.ManyF j x).Op
local notation "S"=> P.seasons j x
local notation "U"=> P.physicalEnergy j x
local notation "ω"=> (P.seasons j x).wax
local notation "W"=> P.cartage j x
local notation "θ"=> P.tableau j x
local notation "E"=> P.enter j x
local notation "R"=> P.wealth j x
local notation "Vac"=> P.colorZero j x
local notation "Ω"=> P.heaven j x
/-!
 Criterion for obtaining *simultaneous* width-and-grid convergence on
 this spectral character. At nonvanishing lags, prior to projection, assume
 **norm** convergence in one aligning chamber of `ColorHil` itself (`truck`
 chart), whose spatial addresses converge in real coordinates. Absolute pose
 can be restored after projection. Not asserting raw *point* convergence for
 moving absolute poses. Raw quadrature smearing (later) will identify such a
 limit on continuous-space inputs with NO projection on the output required.
-/
structure RawNormal (D:ℕ→P.Apron)(g:ℕ→P.VMark)(p:Vantage)(T:P.RawLag j x):Prop where
 fades:P.Fades D
 shift:Tendsto (P.laysM ∘ g) atTop (𝓝 p)
 showAt:∀a>0,∀b>0,Tendsto (fun i=> P.align j x (D i) (g i) a b) atTop (𝓝 (T a b))
variable {P j x}{D A:ℕ→P.Apron}{g:ℕ→P.VMark}{p:Vantage}{T V:P.RawLag j x}{l r a b:ℝ}
local notation "α" t:max=> P.align j x (D t) (g t)
local notation "τ" t:max=> (D t).realWidth P j
namespace RawNormal
variable (h:P.RawNormal j x D g p T)
include h
lemma normal :P.Normal j x D (P.respool j x p T):=by
 refine ⟨h.fades,?_⟩
 intro a u b v
 apply (P.locate_limit j x h.shift.neg (P.reprise_bsot j x (BSOT.fromNorm (h.showAt _ u _ v)))).congr'
 exact Eventually.of_forall fun i=>congrFun (congrFun (P.respool_align j x (D i) (g i)) a) b
lemma credits:(U).Credits 0 T:=Credits.paid (h.fades j) (Eventually.of_forall (fun s=> P.align_credits j x (D s) (g s))) h.showAt
lemma showOn {u v:ℕ→ℝ}(a':0<a)(b':0<b)(q:Tendsto u atTop (𝓝 a))(y:Tendsto v atTop (𝓝 b)):
 Tendsto (fun i=>(α i) (u i) (v i)) atTop (𝓝 (T a b)):=
 Credits.norm_on (h.fades j) (Eventually.of_forall (fun s=> P.align_credits j x (D s) (g s))) h.showAt a' b' q y
-- uniform cost of approximation for all larger lags
lemma merit (q:0<a):
 ∃ d:ℕ→ℝ,(∀s,0≤d s) ∧ Tendsto d atTop (𝓝 0) ∧
  ∀ᶠ s in atTop,∀l≥a,∀r≥a,‖(α s) l r-T l r‖≤d s:=by
 refine ⟨_,fun i=>norm_nonneg _,tendsto_iff_norm_sub_tendsto_zero.mp (h.showAt a q a q), ?_⟩
 filter_upwards [h.fades.one q j] with s u; intro l v r y; have m:= max_lt u q
 exact Credits.sub_pay (P.align_credits j x (D s) (g s)) h.credits m m v y
lemma kiss :P.RawNormal j x (fun s=>(D s).kiss P j) g p (P.rawOther j x T):=by
 refine ⟨h.fades.kiss j,h.shift,fun a u b v=> (h.showAt _ v _ u).star.congr ?_⟩
 intro i;rw [P.align_kiss];rfl
lemma unique (t:P.RawNormal j x D g p V)(u:0<a)(v:0<b): T a b=V a b:=tendsto_nhds_unique (h.showAt _ u _ v) (t.showAt _ u _ v)
lemma viaDiff (w:P.Fades A){d:ℕ→ℝ}(q:Tendsto d atTop (𝓝 0))
 (t:∀a>0,∀b>0,∀ᶠ s in atTop, ‖P.rawBase j x (A s) a b-P.rawBase j x (D s) a b‖≤d s):P.RawNormal j x A g p T:=by
 refine ⟨w,h.shift,fun a u b v=>?_⟩
 let M(i:ℕ):X:=P.align j x (A i) (g i) a b
 have z:Tendsto (fun i=>M i-(α i) a b) atTop (𝓝 (0:X)):=by
   rw [tendsto_iff_norm_sub_tendsto_zero];simp only [sub_zero]
   refine squeeze_zero' (Eventually.of_forall fun i=>norm_nonneg _) ?_ q
   exact (t _ u _ v).mono fun i y=> (P.align_dist ..).trans_le y
 have e:=z.add (h.showAt a u b v)
 simp only [sub_add_cancel,zero_add] at e;exact e
lemma agrees (w:∀a>0,∀b>0,V a b=T a b):P.RawNormal j x D g p V:=by
 refine ⟨h.fades,h.shift,fun a u b v=>?_⟩
 rw [w _ u _ v];exact h.showAt _ u _ v
end RawNormal
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
