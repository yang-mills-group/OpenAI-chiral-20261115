import SatinFixedContrastNovember4
import YM.SU5.Thin.Layout

set_option autoImplicit false
set_option maxHeartbeats 190000
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
/-!
# Lower-bound track

Don't normalize by read signs after extraction etc. Earn bound from estimated
weakly damped time mark price at this very registration and for every repeat
used. For the reader this means pay the SAME purchases (`Cost price pupil`);
for the product competitor use also THESE new mixtures, all stamps etc.
-/
open DoseBill Sifter VoucherOp Theatre PadThin
namespace StrongStamp
variable (X Y:Hilbert)(t:ℝ≥0)(A:ℕ→X.Op)(C:X.Op)(S:OS.Semigroup X (3:Axis)) (T:OS.Semigroup Y (3:Axis))(D:ℕ→ Scoop)(ω x:X)
private lemma anneal (v:Y)(a:Scoop) : a.recipe (fun _=> v)=v:= by
  unfold Scoop.recipe; rw [← Finset.sum_smul,← Complex.ofReal_sum,a.total,Complex.ofReal_one,one_smul]
lemma squeezeIssue (r:ℕ→ℝ≥0)(F:ℕ→ X)(e: Tendsto (fun i:ℕ=> (Scoop.recipe (D i) (fun k=> A (i+k))) ω) atTop (𝓝 (C ω)))
    (p:∀ i,A i ω= S.E (r i) (F i)) (ε:ℝ)
    (t0:ℝ≥0)(u:t0≤t) (g:∀ᶠ i in atTop,∀ k:ℝ≥0,t0≤ k→ dist (S.E k (F i)) x≤ε): dist (S.E t (C ω)) x ≤ ε := by
 let G(i):= Scoop.recipe (D i) fun k=>A (i+k)
 have H:Tendsto (fun i=>dist (S.E t (G i ω)) x) atTop (𝓝 (dist (S.E t (C ω)) x)):=((S.E t).continuous.continuousAt.tendsto.comp e).dist (tendsto_const_nhds (x:=x))
 refine le_of_tendsto H ?_; obtain ⟨n,t'⟩:= eventually_atTop.1 g; filter_upwards [eventually_ge_atTop n] with i h
 rw [dist_eq_norm,show S.E t (G i ω)-x=(D i).recipe (fun k=> S.E t (A (i+k) ω)-x) from ?_]
 · apply Scoop.cap; intro k e; change ‖S.E t _-x‖≤ _; rw [←dist_eq_norm,p (i+k),← ContinuousLinearMap.comp_apply,← S.time]; exact t' _ (by omega) _ (le_trans u (le_self_add))
 unfold G; rw [Scoop.evaluates]; unfold Scoop.recipe; simp_rw [map_sum,map_smul,smul_sub]; rw [Finset.sum_sub_distrib]; exact congrArg (fun z:X=>(∑ k∈ (D i).take, (((D i).weight k:ℝ):ℂ) • (S.E t (A (i+k) ω))) - z) (anneal X x (D i)).symm -- rw `G` name
lemma normIn (x:X→L[ℂ]Y)(y:Y.Op)(w:‖x‖≤1)(v:‖y‖≤1):‖y.comp x‖≤1:= (ContinuousLinearMap.opNorm_comp_le ..).trans ((mul_le_mul v w (ContinuousLinearMap.opNorm_nonneg _) zero_le_one).trans_eq (one_mul _))
-- reach pure amount. if compress and conjugate by a vacuum-preserving occupation.
lemma localize (w:Y)(α:ℂ)(ε:ℝ)(V:X→L[ℂ]Y)(h:‖V‖≤1)(g:V ω=w)(R:X.Op)(z:Y)(u:z=V (R ω)) (p: dist (R ω) (α • ω)≤ε) : dist z (α • w)≤ε := by
 rw [u,← g,dist_eq_norm,← map_smul,←map_sub]; rw [dist_eq_norm] at p; exact ((V.le_of_opNorm_le h _).trans ((one_mul _).le)).trans p
-- unitary cart in each step already proven; no physical norm-growth allowance

lemma walk (a b:ℝ≥0)(A:X.Op)(v:X)(w:Y)(c:ℂ)(D:Y.Op)(W:(X→L[ℂ]Y))(F:Y.Op)(L:Y.Op)(U:Y→L[ℂ]X)(ε:ℝ)(p:dist (S.E a (A v)) (c • v) ≤ ε)
    (h: W v=w)(h':F w=w)(g:L w=w)(l:U w=v)(t:‖W‖≤1)(e:‖F‖≤1)(z:S.E b v=v)
    (q:D=carries (X:=X) (Y:=Y) (F.comp W) (U.comp L) (sent X S a b A)): dist (D w) (c • w) ≤ ε:=by
  refine localize X Y v w c _ (F.comp W) (normIn X Y _ _ t e) ?_ ((S.E a).comp A) _ ?_ p
  · rw [ContinuousLinearMap.comp_apply,h,h']
  rw [q]; simp only [carries, ContinuousLinearMap.comp_apply,g,l,sent,z]
end StrongStamp
open StrongStamp
namespace VoucherOp
variable {P:Spine}{x:P.Spectrum0 3}{b:ℕ→ℕ}{Z:Lead.Clan}{n:ℕ}(K:P.VoucherOp x Z n b)(F:SampleDose)
local notation "ξ"=> P.otherSpectrum 3 3 x
local notation "H'"=> P.ColorHil 3 ξ
local notation "H"=> P.ManyF 3 ξ
local notation "ω"=>P.colorZero 3 ξ
local notation "ν"=>P.heaven 3 ξ
local notation "σ"=>P.seasons 3 ξ
local notation "μ"=> P.physicalEnergy 3 ξ
local notation "E"=> (P.physicalEnergy 3 ξ).E
local notation "π"=> P.wealth 3 ξ
local notation "τ"=>P.tableau 3 ξ
local notation "R"=> purePrice Z
local notation "ρ"=> (↑(purePrice Z):ℂ)
local notation "B" i:max => P.thinString Z (b i) n
local notation "κ" p:max => P.cartage 3 ξ p

-- use ν' on full H', need h∈ℝ estimator
variable (t:ℝ≥0)(ε:ℝ)
def Weather (P:Spine)(x:P.Spectrum0 3)(t:ℝ≥0)(ε:ℝ)(n:ℕ)(b:ℕ→ℕ):Prop:=∀ Z:Lead.Clan,
  ∀ᶠ i:ℕ in atTop,∀ v:ℝ≥0,t≤v→dist ((P.physicalEnergy 3 (P.otherSpectrum 3 3 x)).E v (P.shard x Z (b i) n)) ((purePrice Z:ℂ) • P.colorZero 3 (P.otherSpectrum 3 3 x))≤ ε*purePrice Z
variable (G:Weather P x t ε n b)(p:Vantage)(lo hi:ℝ){a d:ℝ≥0}(u:t≤a)
include u G
omit u G
private lemma hasHor (z:H') : Tendsto (fun i:ℕ=> (Scoop.recipe (K.cost i) (fun k=> (B (i+k)).engine P 3 ξ)) z) atTop (𝓝 (K.issue z)) := (K.arrival z).1
private lemma nativeHor (s:ℕ): (B s).engine P 3 ξ ω= (μ).E ((B s).realWidth P 3).toNNReal (P.shard x Z (b s) n) := P.born_entry x (B s) (P.thinString_birth Z (b s) n)
include u G
lemma pricedSource : dist (E a (K.issue ω)) (ρ • ω)≤ ε*R := by
  let M:= H'; let C:=fun i:ℕ=> (B i).engine P 3 ξ
  let w:= fun i:ℕ=> ((B i).realWidth P 3).toNNReal
  let U:= fun i:ℕ => P.shard x Z (b i) n
  let q:M:=ω
  let r:M:=ρ • q
  apply squeezeIssue M a C K.issue μ K.cost ω r w U _ _ (ε*R) t u _
  · exact K.hasHor q
  · exact fun i=> nativeHor (P:=P) (b:=b) (n:=n) (x:=x) (Z:=Z) i
  exact G Z
end VoucherOp
#print axioms VoucherOp.pricedSource
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
