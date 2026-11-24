import SatinThinSquire
import YM.SU5.Regis.Legend
import YM.SU5.Hiro.Ladles
import YM.SU5.Regis.Voyance
import YM.SU5.Celeste.Custodian

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
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "Q"=> P.par.block
local notation "ℓ"=> P.calibration.ℓ
local notation "Ξ"=> household W
open Papal Regis.Head Gleam
/-! # Price of ensemble-of-trips. Exactly composed on printed test level before estimation. -/
open Clock Clock.Hookah Clock.Hookah.Blaze
open Preparation.Yoke Yoke.Travel Regis.Head.Garland
variable (z:PlaqAxes→ℝ) {I U:Type} [Fintype I] [Fintype U] (T:Trip I)(s:ℕ)(b:U→ ℕ)
local notation "xθ"=> hat P.par.R.L P.par.x s
abbrev visitLedger : P.Test:= P.art (household W (T.issued z (xθ))) (Tower.aux_test (T.issues z (xθ) W))
local notation "Ξx"=> P.visitLedger z
lemma bulb_reflect (a:ℤ)(N): (fluent j a (T.issued z xθ)) N = (playback T j a).issued z xθ N:=by
 unfold fluent Trip.issued playback; rw [mapped_at]; funext x; unfold reflMark pension Clock.Hookah.chalkOp reflFields; dsimp only [Prod.map]; rw [theta_smul,theta_one,fling_eq,silk_moves,Complex.star_def,Complex.conj_ofReal]
lemma bulb_right (d:ℕ) : P.halfShift j d (Ξx T s)=Ξx (hopping T (P.stretchO j d)) s:=by
 apply Subtype.ext; let u:= gaugeShift P.par.block (d:ℤ)
 change household P.calibration (traction j u (T.issued z xθ))=household P.calibration ((hopping T (P.stretchO j d)).issued z xθ); unfold traction; have he (a:ℤ)(V:Trip I): fluent j a (V.issued z xθ)=(playback V j a).issued z xθ:=funext fun i=> P.bulb_reflect j z V s a i
 rw [he,he,play_hopping]; rfl
lemma visit_reflect : P.reflectTest j (Ξx T s)= Ξx (playback T j 0) s:= Subtype.ext (congrArg (household W) (funext fun i=> P.bulb_reflect j z T s 0 i))
lemma visit_unit_pair (x y:Cover)(a t:Signed) : Ξx (twinTrip x y a t) s=Ξx (loneTrip x a) s* Ξx (loneTrip y t) s:=by
 apply Subtype.ext; funext i; exact twin_book z ..
lemma visit_stack (A:Trip I) : Ξx (tapeBoth T A) s= Ξx T s * Ξx A s:=by
 apply Subtype.ext; funext i; let n:= P.calibration.c i
 change (tapeBoth T A).issued z xθ n=T.issued z xθ n*A.issued z xθ n
 unfold Trip.issued pension Hookah.chalkOp; funext j; simp only [Pi.mul_apply]; rw [Matrix.smul_mul,one_mul,smul_smul]; unfold Clock.Hookah.Blaze.silk; rw [Fintype.prod_sum_type]; push_cast; rfl
abbrev rover (i:U) := hopping T (P.lineup j b i)
abbrev rover' (i:U):= playback (P.rover j T b i) j 0
abbrev win_stack (i u:U) := tapeBoth (P.rover' j T b i) (P.rover j T b u)
abbrev trickPool := ∑ i:U,P.visitLedger z (P.rover j T b i) s
lemma halfReadL : P.trickPool j z T s b= ∑ i:U, P.halfShift j (b i) (Ξx T s):=by simp_rw [P.bulb_right]; rfl
lemma petty_star : P.reflectTest j (P.trickPool j z T s b)*P.trickPool j z T s b=∑ i:U,∑ k:U, Ξx (P.win_stack j T b i k) s:=by
 simp_rw [trickPool,win_stack,P.visit_stack,rover',← P.visit_reflect]; rw [map_sum (P.reflectTest ..),Fintype.sum_mul_sum]
-- no covariance required? located result
lemma stamp_deck (h:∀ i,Tower.region j 0 P.calibration.ℓ (onFlight P.par.block T.canvasC j (b i))) : ∃ v:P.Vox j s, P.voxTest j s v=P.trickPool j z T s b:=by
 let f:=Ξx T s; let S(i:U):=onFlight P.par.block (T.canvasC) j (b i); let V':=univ.biUnion S; let F:=∑ i,P.halfShift j (b i) f
 have he(i:U): P.halfShift j (b i) f ∈ bay P.calibration V' true:=by rw [Tapestry.locates,P.halfShift_val]; exact (Tower.flow_port _ _ _ (T.issues z xθ P.calibration)).mono (subset_biUnion_of_mem S (mem_univ i))
 refine ⟨P.positiveVox j s V' F ((bay P.calibration V' true).sum_mem fun i _=>he i) ?_,?_⟩; · intro x q; obtain ⟨i,_,t⟩:= mem_biUnion.mp q; exact h i x t
 rw [P.halfReadL]; rfl
lemma stamp_bound (h:∀ i,Tower.region j 0 P.calibration.ℓ (onFlight P.par.block T.canvasC j (b i))) :
    (Fintype.card U:ℝ)^2* (∫ x, ‖P.singleState j s x (Ξx T s)‖^2 ∂(P.pillars j)) ≤ ‖(∑ i:U, ∑ k:U,P.eReadL s (Ξx (P.win_stack j T b i k) s))‖:=by
   let p:=P.visitLedger z T s; let f:=P.trickPool j z T s b; have hv:= P.rosaryV j s f (P.stamp_deck j z T s b h)
   change _ ≤ ‖P.eReadL s _‖ at hv -- tune
   rw [show P.reflectTest j f * f=_ from P.petty_star j z T s b] at hv; simp_rw [map_sum] at hv
   have he(x): (P.singleState j s x) f=(Fintype.card U:ℂ)*P.singleState j s x p:=by
      unfold f; rw [P.halfReadL,map_sum]; let U'(t:ℕ):=P.halfShift j t p; let h:= P.singleState j s x; have h0:∀ i:U,(P.singleState j s x) (P.halfShift j (b i) (Ξx T s))= h p:=by intro i; unfold h; rw [P.single_state,P.halfReads]; rfl
      simp_rw [h0]; simp [h]
   simp_rw [he,norm_mul,mul_pow] at hv; rw [integral_const_mul, show ‖(Fintype.card U:ℂ)‖=(Fintype.card U:ℝ) from (by simp)] at hv; exact hv
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.stamp_bound
