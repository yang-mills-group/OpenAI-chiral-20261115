import WakeRoad.MixedMoment
import Gingham.TopperWord
import YM.SU5.Six.PointSpot
import YM.SU5.Voyager.Beloved
import YM.SU5.Macro.Edge
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe
namespace Spine.NativeSeam
open SatinRegistration YM.Velour
variable (P:Spine)(x:P.Spectrum0 3)
local notation "j"=> (3:Axis)
local notation "ξ"=> P.advocate 3 x j
local notation "G"=> P.ManyF j ξ
local notation "S"=> P.seasons j ξ
local notation "Ω"=> P.heaven j ξ
variable (B D:P.Apron)
abbrev native (A:P.Apron):ℂ:= P.singleState 3 A.s x A.F
-- glare and dawn as physical vacuum translations, directed interval gap
lemma one_chit (J:P.Ellis 3 x) : native P x D=inner ℂ Ω (flashY x D j) := by
  exact (P.bodyOne_price x J D (0:Vantage)).symm.trans (singleP j x J (fun _ : Unit=> D) (fun _=>0) ())
lemma local_pair (J:P.Ellis 3 x)(n:ℕ)(d f:Cover)(h:B.s≤n ∧ D.s≤n)
    (gap: ∀ i:Axis, P.gridSpot n d i+B.realWidth P i<P.gridSpot n f i-D.realWidth P i):
    let δ:= P.meshPose n f-P.meshPose n d
    P.singleState 3 n x (P.issuing n B d * P.issuing n D f)=
        inner ℂ (glareY x B j) ((S).E ((δ 3 - (B.realWidth P 3 + D.realWidth P 3)).toNNReal) ((P.cartage 3 ξ δ) (flashY x D j))):=by
    intro δ
    let A:= usher B D; let p:=usher d f; let y:= P.gridSpot n ∘p; let Q:=[false,true]
    have u(k):P.Turnstile k A Q y:=List.pairwise_pair.mpr (gap k)
    have H:P.Plenum A Q y:=⟨fun i=>⟨_,.refl _,u i⟩⟩
    have he : P.fullScroll n A p Q=P.issuing n B d * P.issuing n D f:=by
       change _ * (_ * 1) = _; rw [mul_one]; rfl
    let x':=P.gridSpot n d; let y':=P.gridSpot n f
    have v:A false=B:=rfl
    have w: ∀ i∈Q,(A i).s ≤ n:= fun i _=>by cases i;exact h.1;exact h.2
    have g: δ∈ P.forwardPair B D 3:= by
       change _ < y' 3-x' 3
       specialize gap 3; unfold x' y'; linarith
    have hx:δ=y'-x':=rfl
    rw [← he,P.spot_full x _ _ _ J n w (u 3) H]
    rw [show P.gridSpot n ∘ p= usher x' y' from funext (fun i=>by cases i<;>rfl)]
    exact P.bodyPair_fwd x B D 3 x' y' J g
lemma singleLocal (J:P.Ellis 3 x)(n:ℕ)(d:Cover)(h:B.s≤n): P.singleState j n x (P.issuing n B d)= native P x B:= (P.castAt_price x J B h d).trans (P.bodyOne_price x J B (P.gridSpot n d))
-- profile under fixed seam 0
abbrev ice(B:P.Apron)(p:Vantage):ℝ≥0:= ((-p j-B.realWidth P j:ℝ)).toNNReal
abbrev melt(B:P.Apron)(p:Vantage):ℝ≥0:= (p j-B.realWidth P j:ℝ).toNNReal
abbrev carry:= P.cartage j ξ
abbrev frost(B:P.Apron)(p:Vantage):G:= carry P x p ((S).E (ice P B p) (glareY x B j))
abbrev flush(B:P.Apron)(p:Vantage):G:= carry P x p ((S).E (melt P B p) (flashY x B j))
local notation "W"=>carry P x
local notation "T"=>(S).E
lemma inner_advance (p q:Vantage)(u v:G) : inner ℂ (W p u) (W q v)=inner ℂ u (W (q-p) v):=by
 rw [←ContinuousLinearMap.adjoint_inner_right, P.cart_reverses,←ContinuousLinearMap.comp_apply,←P.cart_paves,neg_add_eq_sub]
lemma frost_payment {p q:Vantage}(t:p j+B.realWidth P j<0)(g:D.realWidth P j<q j):
    inner ℂ (frost P x B p) (flush P x D q) =
        inner ℂ (glareY x B j) (T ((q j-p j-(B.realWidth P j+D.realWidth P j)).toNNReal) (W (q-p) (flashY x D j))):=by
    unfold frost flush
    rw [inner_advance P x,OS.Semigroup.swing,←P.warm_drive,←ContinuousLinearMap.comp_apply,←(S).time] -- order combine? warm drive args
    have h:ice P B p + melt P D q=(q j-p j-(B.realWidth P j+D.realWidth P j)).toNNReal:=by
       unfold ice melt;ext; rw [NNReal.coe_add,Real.coe_toNNReal _ (by linarith : 0≤-p j-B.realWidth P j),Real.coe_toNNReal _ (by linarith),Real.coe_toNNReal _ (by linarith)]; ring
    rw [h]
lemma frost_cont : Continuous (frost P x B):=P.caravan _ _ _ _ continuous_id (((S).continuousE _).comp (continuous_real_toNNReal.comp (by fun_prop)))
lemma flush_cont : Continuous (flush P x D):=P.caravan _ _ _ _ continuous_id (((S).continuousE _).comp (continuous_real_toNNReal.comp (by fun_prop)))
lemma activation_star (n:ℕ)(F:SampleDose)(i:Cover): star (P.activation n F i)=P.activation n F i:=by unfold activation; simp
-- exact Riemann kernel matching for ANY two such apertures & at same fixed tests all refinement
structure SpanSeam (F R:SampleDose):Prop where
    before (p:Vantage)(v:p∈tsupport F.val): p 3+B.realWidth P 3 < 0
    afterX (p:Vantage)(v:p∈tsupport R.val): D.realWidth P 3 < p 3
    credits(p q:Vantage)(w:p∈tsupport F.val)(v:q∈tsupport R.val)(i:Axis): p i+B.realWidth P i<q i-D.realWidth P i
    unitF:F.Normalized
    unitG:R.Normalized
    -- later physical region spacing
abbrev forecast (V:Vantage→G)(F:SampleDose)(n:ℕ):G:= ∑ k∈P.usedGrid n F,P.activation n F k • V (P.meshPose n k)
-- see Gingham/Topper
lemma forecasts (V:Vantage→G)(F:SampleDose)(h:Continuous V): Tendsto (forecast P x V F) atTop (𝓝 (DoseTravel.beam G F V)):=by
 unfold DoseTravel.beam
 refine (MacroGrid.rSum_limit _ P.macroStep_zero (fun p:Vantage=> (F.val p:ℂ) • V p) ((Complex.continuous_ofReal.comp F.smooth.continuous).smul h) P.macroStep_pos (dyed_compact V)).congr (fun n=>?_)
 let f(i:Cover):= (F.val (P.meshPose n i):ℂ) • V (P.meshPose n i)
 have hi(i:Cover)(w:i∉P.usedGrid n F): f i=0:=by
    unfold f; rw [image_eq_zero_of_notMem_tsupport (mt (P.usedPose ..).2 w),Complex.ofReal_zero,zero_smul]
 refine (room_price (P.macroStep n) (P.macroStep_pos n) f _ hi).2.trans ?_
 rw [Finset.smul_sum]
 refine Finset.sum_congr rfl fun i _=>?_ ; unfold f
 rw [show Fintype.card Axis=4 by rfl,← Complex.coe_smul ((P.macroStep n)^4),smul_smul, activation, Complex.ofReal_mul]

lemma grid_exact (F U:SampleDose) (h:SpanSeam P B D F U)(J:P.Ellis 3 x)(n:ℕ)(u:B.s≤n∧D.s≤n):
    P.singleState 3 n x (P.prepared n B F * P.prepared n D U)=inner ℂ (forecast P x (frost P x B) F n) (forecast P x (flush P x D) U n):=by
    unfold prepared forecast
    rw [Finset.sum_mul,map_sum,sum_inner]; refine Finset.sum_congr rfl fun i v => ?_
    rw [Finset.mul_sum,map_sum,inner_sum]; refine Finset.sum_congr rfl fun q g=> ?_
    have e:P.meshPose n i∈tsupport F.val:= (P.usedPose ..).1 v
    have t:P.meshPose n q∈tsupport U.val:= (P.usedPose ..).1 g
    rw [inner_smul_left,← Complex.star_def,activation_star,inner_smul_right, frost_payment P x B D (h.before _ e) (h.afterX _ t)]
    rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,map_smul,map_smul,local_pair P x B D J n i q u (h.credits _ _ e t)]
    rfl
lemma single_exact (F:SampleDose)(J:P.Ellis 3 x)(n:ℕ)(h:B.s ≤ n) :
    P.singleState 3 n x (P.prepared n B F)=(∑ k∈ P.usedGrid n F,P.activation n F k)*native P x B:=by
    unfold prepared; rw [map_sum,Finset.sum_mul]; refine Finset.sum_congr rfl fun i _=>?_ ; rw [map_smul,singleLocal P x B J _ _ h,smul_eq_mul]
#print axioms grid_exact
-- price incomes
lemma activation_one (F:SampleDose)(h:F.Normalized): Tendsto (fun n=> ∑ k∈P.usedGrid n F,P.activation n F k) atTop (𝓝 1):=by
    -- complex rSum
    let q(v:Vantage):ℂ:=F.val v
    have hs: HasCompactSupport q:= F.budget.comp_left (show (↑(0:ℝ):ℂ)=0 from rfl)
    have hp:= MacroGrid.rSum_limit _ P.macroStep_zero q (Complex.continuous_ofReal.comp F.smooth.continuous) P.macroStep_pos hs
    have he:(∫ v,q v)=1:=by unfold q; rw [integral_complex_ofReal,h.2, Complex.ofReal_one]
    rw [he] at hp
    apply hp.congr (fun n=> ?_)
    let f(i:Cover):= q (P.meshPose n i)
    have hi(i:Cover)(w:i∉P.usedGrid n F):f i=0:=by unfold f q; rw [image_eq_zero_of_notMem_tsupport (mt (P.usedPose ..).2 w),Complex.ofReal_zero]
    refine (room_price (P.macroStep n) (P.macroStep_pos n) f _ hi).2.trans ?_
    rw [Finset.smul_sum]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold f q; rw [show Fintype.card Axis=4 from rfl,←Complex.coe_smul,smul_eq_mul,activation,Complex.ofReal_mul]
abbrev gridValues (F U:SampleDose)(n:ℕ): Gingham.Parts:=(P.singleState 3 n x (P.prepared n B F*P.prepared n D U),P.singleState 3 n x (P.prepared n B F),P.singleState 3 n x (P.prepared n D U)) -- Rosette not imported?
abbrev EuCosts (F U:SampleDose): Gingham.Parts:= (inner ℂ (DoseTravel.beam G F (frost P x B)) (DoseTravel.beam G U (flush P x D)),native P x B,native P x D)
lemma seam_income (F U: SampleDose)(J:P.Ellis 3 x)(h:SpanSeam P B D F U): Tendsto (gridValues P x B D F U) atTop (𝓝 (EuCosts P x B D F U)):=by
    have he(A:P.Apron)(F:SampleDose)(t:F.Normalized): Tendsto (fun n=>P.singleState 3 n x (P.prepared n A F)) atTop (𝓝 (native P x A)):=by
       have hp:= (activation_one P F t).mul_const (native P x A); rw [one_mul] at hp; refine hp.congr' ?_; filter_upwards [eventually_ge_atTop A.s] with i h; exact (single_exact P x A F J _ h).symm
    refine (Tendsto.prodMk_nhds ?_ ((he _ F h.unitF).prodMk_nhds (he _ U h.unitG)))
    refine ((forecasts P x _ F (frost_cont P x B)).inner (forecasts P x _ U (flush_cont P x D))).congr' ?_
    filter_upwards [eventually_ge_atTop (B.s+D.s)] with n t; exact (grid_exact P x B D F U h J _ ⟨by omega,by omega⟩).symm
end Spine.NativeSeam
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
