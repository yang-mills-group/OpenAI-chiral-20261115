import YM.CF.Py.Costs
import YM.CF.Fixed.LargeRoe
import YM.CF.Fixed.Functional

/-!
# Mantle: comparison with (fixed-x) pressure allowance

This file prepares the application at arbitrary size after choosing Grace and
its work pillars. Applies at EVERY depth of active block (not just at base).
Condition is a coupling & a volume charge. Relies still on *direction-to-
infinity* estimates so it will produce a **space** of eligible pairs (x,M)
at cofinally many pivot x. Does not grant all arbitrarily large M's once x is
high enough. Volume has finite ceiling
in terms of x.
Numerator and denominator use same pressure book. At a pair, handle all
UV horizons of the tower, kernels and subsequent limit separately.
Hermitian is independent of size charge.
-/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor Jet Vol Rel Cascade Fief Yaw Pig Wray Lich.Muster Push.AbsoluteSums Iva Eire Jade
open CF.Fixed CF.Fixed.Extensive CF.Mint RoeWL Graph Girt
variable{N B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d e η z g A B':ℝ} {j k k' m n l j' :ℕ}(V:Grace K R L){x β:ℝ}
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)

abbrev peakZ(L:Side)(x:ℝ):= SectorNext.Remainder.Scales.g SU.group L x * temp x -- definitionally dleaf
local notation "ζ'"=> peakZ R.L
local notation "ε"=> K.top.clip
structure Mantle (m:Side) (F:GramM (Scree.mid m B))(D:Loom (Scree.mid m B)) : Prop where
    born: 100*(1+radiusB x) ≤ (More (mid m B)).val -- Month bound enters staged normalization comparison to force Ω.v weak, not prescribe ceiling; note binder ensure x.
    hill: matchedX x F.beta
    cash: F.funds=K.top.clip
    work: F.path.Bounds F.funds K.top.width K.top.paths V.W.bar
    fund: F.p.threshold=temp x
    rest:U.roundZ ≤ (mid m B).val
    close: InterestX W.C (mid m B) F.J
    mint: LotR F h (peakZ R.L x) (peakZ R.L x)
    due: (F.slip=0) -- redundant
    inc: IncX (fun _=>True) F.F F.p h (peakZ R.L x)
    dark: Dark (fun _=>True) F.K F.p h (peakZ R.L x)
    crown: Roof _ J.k d J.n D
    pole: F.p.threshold≤ J.k

variable {M:Side}{F:GramM (mid M B)}{D:Loom (mid M B)} (X:Mantle (x:=x) V J h M F D)
include V in
lemma warmJ : 1 ≤ K.j:=by have he:= V.L.lobby; have ht:= R.order_cut; omega
namespace Mantle
include X
lemma wall:Girt.Ward F:=ward_m X.work X.mint
lemma sheath: SkinT F D d:= Stop.sage _ _ _ X.crown X.pole
lemma registered: RG.Envelope (denZ F U D):= Girt.sailW F (wall V J h X) W.pearl V.note W.health (warmJ V) J.n D X.crown X.rest
lemma rich : Integrable (denZ F U D) (city (mid M B)):= by have hx:= registered V J h X; exact Integrable.of_bound hx.meas.aestronglyMeasurable _ (Eventually.of_forall hx.cost.choose_spec)
lemma coverR (u:0≤h) : Ledger h (ζ' x) (ζ' x) (levelQ W.C) (cashU W.C) F:= frostQ X.mint u X.close
lemma hermitian_phase (i:Axis) : MirrorCompatible i (rescaleOffset U F D):=by
  apply rescale_reflect i U F D V.note X.crown X.rest (show True from trivial) (warmJ V) X.inc (b:=0) _ X.dark
  · intro y z; rw [flash_reflect,←stir_reflect]; have hq:detX (reflShape i).s=true:=det_t i; have he:=Hive.birds (M:=F.J.M) false W.pearl V.note X.rest (warmJ V) (reflShape i) (pinSpin i) (by rw [hq]; exact mirrorX i) F.J.P X.close.leanJ.1 X.close.ready y z; rw [hq] at he; exact he.symm
  rw [X.due]; exact (show IncX _ _ _ _ 0 from ⟨⟨0,fun i=>Vale.rinse i F.p _,fun i=>by simp [BudgetPoint.mass]⟩, fun s _ T t i V=> (map_zero _).symm⟩) -- infer b.
lemma gramH {I:Type*}(i:Axis)(P':I→ Fixed.Test (mid M B))(hp:∀ i,Fixed.Probe (P' i)): Matrix.IsHermitian (Fixed.gram i (evalNormalized U F D) P'):= gram_hermitian i _ hp (fun f _=> evalNormalized_reflect i U F D (hermitian_phase V J h X i) f)
lemma normalization : Normalized (evalNormalized U F D) ↔ partitionZ F U D≠0:=Fixed.equiv_normalized U F D (rich V J h X)
lemma centered : Complex.exp (-F.v)*partitionZ F U D∈ Set.range ((↑) : ℝ→ℂ):=by
  have Hs:=scaledZ_real 0 U F D (hermitian_phase V J h X 0)
  refine ⟨(scaledZ U F D).re,?_⟩; have hp:(scaledZ U F D).im=0:=by have ht:=congrArg Complex.im Hs; simp only [Complex.star_def, Complex.conj_im] at ht; linarith
  exact Complex.ext (by rfl) hp.symm
end Mantle
section
variable {X':ℕ→ℝ}(t:Tendsto X' atTop atTop)
include t in
lemma stage_peak (L:Side) : Aqua (vast X') (fun i=>peakZ L (X' i)):=by
    have h : Tendsto (fun i=> SectorNext.Remainder.Scales.g SU.group L (X' i)) atTop (𝓝 0) := (sizeK.main L).spine.comp t
    exact (Aqua.fed (vast_temp t) (Gray.thin (vital t) h) (vital t))
variable {H h1 h2:ℝ}
abbrev MantleBudget (T R' H:ℝ):= WidthK (P:=U) K.top.clip.linear (cashU W.C) K.top.paths T R' K.top.clip.direct h H 1
local notation "G_"=> MantleBudget V (W:=W) h -- V?
lemma award(u:1≤h):∃ h1 h2 T,MantleBudget V (W:=W) h h1 h2 T:= RoeWL.issue U W.health (warmJ V) _ _ _ _ h 1 K.top.clip.tail_pos (cash_v _) u
variable {M':ℕ→Side}{F':∀ i, GramM (mid (M' i) B)}{D':∀ i, Loom (mid (M' i) B)}(Y':MantleBudget V (W:=W) h h1 h2 H)(T:∀ i, Mantle V J h (M' i) (x:=X' i) (F' i) (D' i))
-- Width appears only here.
abbrev allowance (x H:ℝ) := H*(x*(temp x)^2)
variable (E' :∀ᶠ i in atTop, ((mid (M' i) B).val:ℝ)^4 ≤ allowance (X' i) H)

local notation "N'P" => (fun i:ℕ=> mid (M' i) B)
include t T E'
lemma sham_window : Wide (C:=cashU W.C) Y' V.W.bar K.top.width (levelQ W.C) (fun i=>peakZ R.L (X' i)) (fun i=>peakZ R.L (X' i)) X' F' := by
    have ht:= vital t; have hx:∀ᶠ i in atTop,((eur N'P i)^4)≤ H* vast X' i:=E'; let S:=eur N'P
    have hV : Gray (vast X') S := by
        refine ⟨H,Y'.heat,1,?_⟩; filter_upwards [hx] with i w; rw [Real.norm_of_nonneg (show 0≤S i from (nPos _).le),pow_one]; exact le_trans (by simpa only [pow_one] using pow_le_pow_right₀ (show 1≤S i by unfold S eur; exact_mod_cast (N'P i).property) (by decide : 1 ≤ 4)) w
    refine ⟨ ⟨by norm_num, by norm_num,t,Eventually.of_forall (fun i=>?_)⟩, E', ?_, ((stage_peak t R.L).through ht hV), ((stage_peak t R.L).shrinks.eventually (ge_mem_nhds (show (0:ℝ)<1 by norm_num)))|>.mono fun i p=>⟨p,p⟩,level_p _,K.top.paths_pos.le, Eventually.of_forall fun i => ⟨(T i).fund,Mantle.coverR V J h (T i) (zero_le_one.trans Y'.rope),(T i).work, le_of_eq (congrArg Clip.linear (T i).cash.symm),le_of_eq (congrArg Clip.direct (T i).cash), hush_h (T i).mint (zero_le_one.trans Y'.rope)⟩⟩
    · exact ⟨(by rw [one_div, inv_mul_eq_div]; exact (T i).hill.1),(T i).hill.2⟩
    apply tendsto_atTop_mono (f:=fun i:ℕ=> (radiusB (X' i):ℝ))
    · intro i; unfold eur; exact_mod_cast (show radiusB (X' i)≤ (N'P i).val from by have he:= (T i).born; change _ ≤ (N'P i).val*2 at he; omega)
    exact tendsto_natCast_atTop_atTop.comp (Work.E01.radiusB_tendsto.comp t)

variable {KX b' vL c' l' b a' D₀ E C0 h0 r:ℝ}{kT d' :ℕ} (P_ : Pic.Span W.pearl KX b' vL c' l' b kT)(Q:Roe.Port P_ D₀ E C0 h0 r d')(hX:C0 ≤ h)
include Q hX

/-- Raw cutoff-dependent specification at the taxed layout for actual magnitude
 (ATP uniform in finite horizons). Offset MUST be cancelled. -/
def specimen (X:Side) (x β h2' c:ℝ):ℝ:=lowerBook X ((Real.sqrt x)⁻¹ /4) (stoutY (More X) β (4*((Real.sqrt x)⁻¹/4)) K.top.clip.direct (temp x) K.top.paths V.W.bar) h2' * c
local notation "cpT" => (b'/(2*Nova.poseX)/2)
include Y' in
lemma wage_window : ∀ᶠ i in atTop, let W:=specimen V (mid (M' i) B) (X' i) (F' i).beta h2 (b'/(2*Nova.poseX)/2); 0<W ∧ W≤ ‖Complex.exp (-(F' i).v)*partitionZ (F' i) U (D' i)‖:=by
    let r:= sham_window V J h t Y' T E'; let c:= cpT; have hc:0<c:=by unfold c; have ht:= Nova.pose_p; have hc:=P_.pos; positivity
    filter_upwards [lower_support P_ Y' r,(RoeWL.costR P_ Y' r D' (Eventually.of_forall fun i=> Mantle.sheath V J h (T i)) Q hX).1, r.path.helm] with i p k q; exact ⟨mul_pos (lowerBook_pos _ _ q.1 q.2.1 _) hc,(mul_le_mul_of_nonneg_right p.1 hc.le).trans k.2.2.2.2.2.2.1⟩

omit t T E'
include Y'
lemma wage_late : ∀ᶠ x in atTop, ∀ (M:Side)(F:GramM (mid M B))(D:Loom (mid M B)),Mantle (x:=x) V J h M F D → ((mid M B).val:ℝ)^4 ≤ allowance x H → let L':= specimen V (mid M B) x F.beta h2 (b'/(2*Nova.poseX)/2); 0<L' ∧ L' ≤ ‖Complex.exp (-F.v)*partitionZ F U D‖:=by
    rw [eventually_atTop]; by_contra! hx
    choose x p M F D K L q using fun i:ℕ=> hx (i:ℝ)
    obtain ⟨i,w⟩:= (wage_window V J h (tendsto_atTop_mono p tendsto_natCast_atTop_atTop) Y' K (Eventually.of_forall L) P_ Q hX).exists
    exact q i w

end
end YM.CF.Py
