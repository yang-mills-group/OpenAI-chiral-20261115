import SatinFixedContrastNovember4
import YM.SU5.Thin.Rungs
import YM.SU5.Thin.Sifter

set_option autoImplicit false
set_option maxHeartbeats 260000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open YM.Sifter
namespace PadThin
variable (X:Hilbert)(D:OS.Semigroup X (3:Axis))
variable (u:ℕ→Scoop)
private lemma scoopSub {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E] (S:Scoop) (A B:ℕ→E) : S.recipe A-S.recipe B= S.recipe (fun i=> A i-B i):= by unfold Scoop.recipe; simp_rw [smul_sub]; rw [Finset.sum_sub_distrib]
local notation "θ" a:max=> D.E a
variable (F:ℕ → X.Op)(G: X.Op) (p:∀ v:X,Tendsto (fun i=>(Scoop.recipe (u i) fun k=>F (i+k)) v) atTop (𝓝 (G v)))
/-- Cost production then attenuation. The clearance to the beginning/end of
the paid real slab can be kept any fixed strictly positive (doesn't shadow an
intrinsic width). Prove although the width of EACH summand differs and there is
investment at each side. -/
def sent (a b:ℝ≥0)(G:X.Op) := (θ a).comp (G.comp (θ b))
lemma halfNorm (a b:ℝ≥0)(G:X.Op) : ‖sent X D a b G‖ ≤ ‖G‖ := wrap_pay G (θ a) (θ b) (D.shrinks _) (D.shrinks _)
lemma halfStar (a b:ℝ≥0)(G:X.Op) : (sent X D a b G).adjoint=sent X D b a G.adjoint := by
  unfold sent; rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,D.sym,D.sym]; rfl
lemma around (F:ℕ→X.Op)(v:Scoop)(a b:ℝ≥0) : v.recipe (fun k=> sent X D a b (F k))=sent X D a b (v.recipe F) := by
  ext1 z; rw [Scoop.evaluates X]; change v.recipe _=D.E a (v.recipe F (D.E b z)); rw [Scoop.evaluates X]; unfold Scoop.recipe; simp_rw [map_sum,map_smul]; rfl
include p
lemma splits (x y:ℕ→ℝ) (A B:ℝ) (v:Tendsto x atTop (𝓝 A))(z:Tendsto y atTop (𝓝 B)) (q:0<A) (e:0<B) (Z:X) (C:ℝ)(w:∀ i:ℕ,‖F i‖≤C) : Tendsto (fun i:ℕ=>(Scoop.recipe (u i) fun k=> sent X D ((x (i+k)).toNNReal) ((y (i+k)).toNNReal) (F (i+k))) Z) atTop (𝓝 (sent X D A.toNNReal B.toNNReal G Z)) := by
  let a:=A.toNNReal; let b:= B.toNNReal
  let W(x):= Real.toNNReal x
  let R(i):= Scoop.recipe (u i) fun k=> F (i+k); let L(i):=Scoop.recipe (u i) fun k=> sent X D a b (F (i+k))
  let J(i):=Scoop.recipe (u i) fun k=> sent X D (W (x (i+k))) (W (y (i+k))) (F (i+k))
  have hC:0 ≤ C:=(norm_nonneg _).trans (w 0)
  have ht(i:ℕ): L i=sent X D a b (R i):= around ..
  have he:Tendsto (fun i:ℕ=>‖J i-L i‖) atTop (𝓝 0):= by
    have hx:= (steam_contPos D A q).tendsto.comp v; have hy:= (steam_contPos D B e).tendsto.comp z
    apply Metric.tendsto_nhds.mpr
    intro ε q; let t:=ε/(4*(C+1)); have hu:0<t:=by unfold t; positivity
    obtain ⟨s,u'⟩:= eventually_atTop.mp ((Metric.tendsto_nhds.mp hx t hu).and (Metric.tendsto_nhds.mp hy t hu)); filter_upwards [eventually_ge_atTop s] with i hi
    rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
    unfold J L; rw [scoopSub]; refine lt_of_le_of_lt (Scoop.cap _ (M:=t*C+C*t) (fun k hk=>?_)) ?_
    · let Tα (i):=D.E (W (x i)); let Sα (i):=D.E (W (y i)); let G:=F (i+k)
      have hv:=u' (i+k) (by omega); rw [←dist_eq_norm]; exact wrap_est G _ _ _ _ (D.shrinks _) (D.shrinks _) hv.1.le hv.2.le (w _)
    have h': t *(4*(C+1))=ε:=div_mul_cancel₀ _ (by positivity); nlinarith only [hu,q,h',hC]
  have hβ: Tendsto (fun i=> L i Z) atTop (𝓝 (sent X D a b G Z)):= by
    simp_rw [ht]; exact (D.E a).continuous.continuousAt.tendsto.comp (p _)
  refine hβ.congr_dist (squeeze_zero (fun _=>dist_nonneg) ?_ (show Tendsto (fun i=>‖J i-L i‖ * ‖Z‖) atTop (𝓝 0) from by simpa using he.mul_const ‖Z‖)); intro i; rw [dist_comm,dist_eq_norm]; exact (J i-L i).le_opNorm _
end PadThin
open PadThin
section assembly
variable (P:Spine)(x:P.Spectrum0 3) (Z:Lead.Clan) (n:ℕ)(b:ℕ→ℕ) (s t:ℕ)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "H'"=> P.ColorHil 3 ξ
open Sifter
/-- A mixture at each width (integer `t`). Rung upper eligibility and support
control will be real, INTRINSIC, at these actual queries. And remains on all
smears of this symbol, not a determination using a particular comparison
oracle or Hilbert-space interpretation of the marginal prices. -/
structure WageStream (X:Hilbert)(r:ℕ→ℕ)(F:ℕ→X.Op) where
  cost : ℕ→Scoop
  issue : X.Op
  safe : StrictMono r
  bound : ℝ
  uniformOp (i:ℕ) : ‖F i‖≤ bound
  arrival (x:X): Tendsto (fun i:ℕ=>(Scoop.recipe (cost i) fun k=>F (i+k)) x) atTop (𝓝 (issue x))∧
    Tendsto (fun i:ℕ=> (Scoop.recipe (cost i) fun k=>F (i+k)).adjoint x) atTop (𝓝 (issue.adjoint x))
abbrev VoucherOp := WageStream (P.ColorHil 3 ξ) b (fun i:ℕ=>(P.thinString Z (b i) n).engine P 3 ξ)
variable {P}
lemma promises {K:P.Register}{U:Supplier}{L M:ℝ}(u:uniform P K U L M)(h:StrictMono b) : Nonempty (P.VoucherOp x Z n b):= by
  let D(i:ℕ):=(P.thinString Z (b i) n).engine P 3 ξ; obtain ⟨C,q,f⟩:= staticBeam 3 u Z n
  obtain ⟨B,u,H⟩:= Sifter.scoop H' D (P.colorPopulation 3 ξ K) C q fun i=> f _ _; exact ⟨⟨B,u,h,C,fun i=> f _ _, H⟩⟩
-- Bool True late (= unreflected)
variable (P) (j:Axis)
def cardSchedule (f:Bool) := if f then P.thinString Z s n else (P.thinString Z s n).kiss P 3
lemma schedule_width (f:Bool) : (P.cardSchedule Z n s f).realWidth P j= P.probeWidth s n j:= by cases f<;>rfl
lemma schedule_height (f:Bool) : (P.cardSchedule Z n s f).s=s:=by cases f<;>rfl
lemma probeWidth_static : Tendsto (fun s=>P.probeWidth s n j) atTop (𝓝 0):= by
  have h(v k:ℕ): bell (timeMesh P.par) v k=(k:ℝ)*P.macroStep v:=by change (↑(k:ℤ):ℝ)*_= _; norm_cast -- maybe `push_cast`
  refine (show Tendsto (fun s:ℕ=> (P.probeClock n j:ℝ)*P.macroStep s) atTop (𝓝 0) from by simpa using P.macroStep_zero.const_mul (P.probeClock n j:ℝ)).congr fun i=>?_; exact (h _ _).symm
variable (X : P.VoucherOp x Z n b)
namespace VoucherOp
variable {x Z n b P}
-- Expand placements (θ coordinates keep full opposite, masses real). Unit already in price.
def operator (w:Bool) : (P.ColorHil 3 ξ).Op:= if w then X.issue else X.issue.adjoint
lemma pays (w:Bool)(i:ℕ) : ‖(P.cardSchedule Z n (b i) w).engine P 3 ξ‖ ≤ X.bound:= by
  cases w
  · exact (ContinuousLinearMap.adjoint.norm_map _).trans_le (X.uniformOp i) |>.trans' (le_of_eq (congrArg norm (show (P.cardSchedule Z n (b i) false).engine P 3 ξ=((P.thinString Z (b i) n).engine P 3 ξ).adjoint from (Apron.peer P 3 ξ _).symm)))
  exact X.uniformOp i
end VoucherOp
end assembly
#print axioms PadThin.splits
#print axioms promises
#print axioms probeWidth_static
#print axioms VoucherOp.pays
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
