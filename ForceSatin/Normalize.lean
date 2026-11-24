import ForceSatin.TiltCost
import SatinThinFund
import Risa.Warehouse
import YM.SU5.FiniteGaugeData.Cuprite.Jersey
set_option autoImplicit false
set_option maxHeartbeats 520000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Papal
local notation "ℶ" => hat P.R.L P.x
local notation "💠" => P.K.j
open CF.Papyrus.Franc Verses CF.Pannier.Chancel Checkers Flint Gleam Gleam.Luster Gleam.Luster.Almanac Grade Graph
local notation "pio"=> P.R.L
open CF.Window CF.Velvet CF.Pannier.Damask

open CF.Papyrus.Franc.SatinForce
open Pannier
local notation "nₛ" s:max i:max => count Y s i
local notation "χf" x:max => parcelF x

/-- the actual period-and-depth enrollment *before* R-indexed checker questions. -/
def TiltWorld (s i k:ℕ)(b C:ℝ) : Prop :=
  let U:=gram Y s i k; let S:=count Y s i; let x:=ℶ s; let δ:=parcelF x
  1 ≤ x ∧ TiltAccount Y s i k b C ∧ (∀ z:Orbit S,tier P.h (U.board z).val≤ Real.exp (δ*sites S)) ∧
    VLine Y s i k δ ∧ pressureLean Y 1 s i k

lemma merit_as_L (x:ℝ) (hx:1≤x) : merit pio x ≤ x^(-(1/4:ℝ)) := by
  let y:=Scales.y G5 pio x; let e:=merit pio x
  have pL:0≤y - x := by
    unfold y Scales.y betaF
    have hh : (1:ℝ)≤(pio).val:= Nat.one_le_cast.mpr P.R.L.property
    have hp:= Gauge.slopeConstant_pos Thera.yet_one
    linarith only [mul_nonneg hp.le (Real.log_nonneg hh)]
  have hp:0<y:=by linarith
  have he:0< e:=merit_pos pio hp
  have hf:e^2=Scales.g G5 pio x:=Real.sq_sqrt (Scales.gauge _ _ hp|>.le)
  have hg:y*e^4=1:=by rw [show 4=2*2 by norm_num, pow_mul,hf]; exact Scales.yg2 _ _ hp
  let d:= x^(-(1/4:ℝ)); have hz:0<x:=zero_lt_one.trans_le hx; have hd:0<d:=by unfold d; positivity
  have hu:x*d^4=1:=by unfold d; rw [←Real.rpow_mul_natCast hz.le]; norm_num; rw [Real.rpow_neg hz.le,Real.rpow_one,mul_inv_cancel₀ hz.ne']
  change e≤d
  apply le_of_pow_le_pow_left₀ (by decide : (4:ℕ)≠0) hd.le ((mul_le_mul_iff_right₀ hz).mp ?_)
  rw [hu]; nlinarith only [hg, mul_nonneg pL (pow_nonneg he.le 4)]

theorem line_by_L (a:ℝ)(h:0<a)(u:Meritorious P) :
    ∀ᶠ s in atTop,∀ i k:ℕ,(Y.voyage i).kick≤ k → s ≤ Y.uv k → VLine Y s i k (a*(ℶ s)^(-(1/4:ℝ))) := by
  filter_upwards [line_merit Y a h u,(turnover P).eventually_ge_atTop 1] with s q v i k g p
  apply (q i k g p).trans'
  apply Real.exp_monotone
  gcongr
  exact merit_as_L _ v

lemma tilt_unmarked (u:Meritorious P) {b C:ℝ} (h:∀ᶠ s in atTop,∀ i k:ℕ,s≤Y.uv k → TiltAccount Y s i k b C) :
    ∀ᶠ s in atTop,∀ i k:ℕ,(Y.voyage i).kick≤ k → s ≤ Y.uv k → TiltWorld Y s i k b C:= by
  filter_upwards [h,line_by_L Y 1 zero_lt_one u, prong_first Y 1,narrowτ P,(turnover P).eventually_ge_atTop 1] with s h hL hG kv hv i k hk hj
  let N:=count Y s i; let U:=gram Y s i k;let x:=ℶ s;let t:= dleaf pio x
  refine ⟨hv,h i k hj,fun z=> ?_,?_,hG i k hj⟩
  · have he := (prices_plot Y s i k hj).2.2.2.2
    have hx: t+t+t ≤ parcelF x:= by linarith only [show 3*t ≤ parcelF x from kv]
    exact (Graph.backstage (zero_le_one.trans P.height) he z).trans (Real.exp_monotone
      (mul_le_mul_of_nonneg_right hx (show 0 ≤ sites N from zero_le_one.trans (sites_pos _))))
  apply (hL i k hk hj).trans'; apply Real.exp_monotone; apply sub_le_sub_left (mul_le_mul_of_nonneg_right ?_ (show 0 ≤ sites N from zero_le_one.trans (sites_pos _)))
  rw [one_mul]; exact Real.rpow_le_rpow_of_exponent_le hv (by norm_num [claimV,ratioV,tauA])


lemma TiltWorld.paid {s i k:ℕ} {b C:ℝ} (T:TiltWorld Y s i k b C) :
    let S := count Y s i; let U := gram Y s i k
    let δ := parcelF (hat pio P.x s)
    Real.exp (Fineness.gaugedBase P.L U.beta (More S) (P.V.L.H (Y.uv k-s))+angleFin U.J.M S 4-δ*sites S) ≤
      ‖Buffered.vac0 P.U U (room Y s i)‖ := by
  intro S U δ
  have h:=T.2.2.2.1
  have hh:angleFin U.J.M S P.K.j=angleFin U.J.M S 4:=by rw [P.kJ]
  rw [←hh]; exact h

/-- Integral of the positive LusterS gauge majorant, divided by the norm of
    the compensated chiral denominator (both *exact*). `d` can price checker
    products before down-root. -/
lemma normalized_integral {s i k:ℕ} (p:s≤Y.uv k) {b C:ℝ} (T:TiltWorld Y s i k b C)
    (d:ℝ) (f:Orbit (count Y s i)→ℝ) (F:AEStronglyMeasurable f (city (count Y s i)))
    (H : ∀ᵐ y ∂city (count Y s i), let N:=count Y s i; let G:=gram Y s i k
      0 ≤ f y ∧ f y ≤ Real.exp (- G.path.inChannels G.funds G.p G.beta y.1 + greyFee Y 1 s i k y.1+
                                    (d+angleFin G.J.M N 4))) :
    let N:=count Y s i; let G:=gram Y s i k; let δ:=parcelF (ℶ s)
    let W := ‖Buffered.vac0 P.U G (room Y s i)‖
    Integrable f (city N) ∧ (∫ y,f y∂city N)/W ≤ Real.exp (d+2*δ*sites N) := by
  intro N G δ L
  let x:= hat pio P.x s; let μ:=city N; let n:=sites N; have hn:0≤n:=zero_le_one.trans (sites_pos _)
  let φ (U:Pane N):=Real.exp (-G.path.inChannels G.funds G.p G.beta U +greyFee Y 1 s i k U)
  let a:=angleFin G.J.M N 4
  let g(y:Orbit N):=φ y.1*Real.exp (d+a)
  let M:=prior SU.group (More N)
  have he:Integrable φ M:=heavy_integrable Y s i k p
  have hM: MeasurePreserving Prod.fst μ M:= measurePreserving_fst
  have hg:Integrable g μ:=(hM.integrable_comp_of_integrable he).mul_const _
  have hh:Integrable f μ:=by
    refine hg.mono F ?_; filter_upwards [H] with y h
    rw [Real.norm_of_nonneg h.1,Real.norm_of_nonneg (show 0≤g y from (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le)]
    exact h.2.trans_eq (Real.exp_add ..)
  let B:=Fineness.gaugedBase P.L G.beta (More N) (P.V.L.H (Y.uv k-s)); let Z:= Real.exp (d+2*δ*n)
  have hk: Real.exp (B+a-δ*n)≤ L:= T.paid Y
  have hf:0<L:=(Real.exp_pos _).trans_le hk
  refine ⟨hh,(div_le_iff₀ hf).mpr ?_⟩
  change _ ≤ Z * L
  apply le_trans (b:=∫ y,g y∂μ)
  · apply integral_mono_ae hh hg; filter_upwards [H] with y h; exact h.2.trans_eq (Real.exp_add ..)
  unfold g; rw [integral_mul_const,usesPrior _ he]
  apply (mul_le_mul_of_nonneg_right (show (∫ U,φ U∂M)≤ Real.exp (B+x^(-yieldA)*n) from T.2.2.2.2) (Real.exp_pos _|>.le)).trans
  apply (mul_le_mul_of_nonneg_left hk (Real.exp_pos _|>.le)).trans'
  rw [← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
  have hj:x^(-yieldA)≤δ:=Real.rpow_le_rpow_of_exponent_le T.1 (by norm_num [yieldA,tauA,claimV,ratioV])
  nlinarith only [mul_le_mul_of_nonneg_right hj hn]

/-- F2 pointwise integrand from the F1/WA.1 receipt. Not claiming
    a measurable choice of lifting gauge. -/
lemma tilt_unmarked_point {s i k:ℕ} {b C:ℝ}(T:TiltWorld Y s i k b C)(y:Orbit (count Y s i)) :
    let N:=count Y s i; let G:=gram Y s i k;let δ:=parcelF (ℶ s);let V:=room Y s i
    let S:= FlatPaneP 4 G.J.M N
    ∃ (p:IsStarProjection S) (l:Seat N→SU.E),let g:=((exactShear 4 G.J.M N (by decide) p).foldC (tailor (tradew N l)))
      (fiber g ((1+b)*180) ∧ condor (spar 4 G.J.M (V y)) C) ∧
      ‖acts (quant (star g.buy)) (mateK N)‖=Real.exp (angleFin G.J.M N 4) ∧ ∀ t:ℝ, |t|≤1 →
        ‖acts (grow (excitation S) t) (acts (quant g.sell) (Graph.recX P.U G V y))‖ ≤
          Real.exp (- G.path.inChannels G.funds G.p G.beta y.1 + greyFee Y 1 s i k y.1 +
            3*δ*sites N - tiltMaskFee N P.K.top.clip G y.1) := by
  intro N G δ V S
  obtain ⟨p,h⟩:= T.2.1; obtain ⟨l,v,w,hz⟩:= h y; refine ⟨p,l,v,w _ (tickB _),fun t ht=>?_⟩
  apply (hz t ht G (δ*sites N) ⟨rfl,rfl,rfl,rfl,rfl⟩ (T.2.2.1 y)).trans_eq (congrArg Real.exp ?_)
  unfold N G δ; ring

abbrev weightedReading (s i k:ℕ)(F: Mark (count Y s i)) (y:Orbit (count Y s i)): ℝ:=
  Real.exp (tiltMaskFee (count Y s i) P.K.top.clip (gram Y s i k) y.1) * ‖rental Y s i k (gram Y s i k) F y‖
lemma tilt_absolute {s i k:ℕ} {b C:ℝ} (p:s≤Y.uv k)(u:(Y.voyage i).kick≤k)(T:TiltWorld Y s i k b C)
    (F: Mark (count Y s i))(hF:RG.Envelope F)(d:ℝ)
    (h : let S:=count Y s i; let M:=(gram Y s i k).J.M; let P:=FlatPaneP 4 M S;
        ∀ (p:IsStarProjection P) (l:Seat S→SU.E) (y:Orbit S),
        ‖((exactShear 4 M S (by decide) p).foldC (tailor (tradew S l))).glow (F (y.1,room Y s i y))‖≤ Real.exp d) :
    let N:=count Y s i; let G:=gram Y s i k;let δ:=parcelF (ℶ s)
    Integrable (weightedReading Y s i k F) (city N) ∧
      (∫ y,weightedReading Y s i k F y∂city N)/‖Buffered.vac0 P.U G (room Y s i)‖ ≤ Real.exp (d+5*δ*sites N) := by
  intro N G δ
  let μ:= city N; let φ(y:Orbit N):= rental Y s i k G F y; let a(y:Orbit N):= tiltMaskFee N P.K.top.clip G y.1
  have he:Integrable φ μ:=Buffered.mark_integrable (roofage Y i s).bill hF ((Marks.can_read _ _ _ _ (Y.each_level i k s u p)).smul (Complex.exp (-G.v)))
  let R(y:Orbit N):= Real.exp (a y)*‖φ y‖
  have hg:AEStronglyMeasurable R μ:=((Real.continuous_exp.measurable.comp ((Gleam.conduct
      (More N) G.p.threshold (flagCup G.p P.K.top.clip G.beta/2)).meas.comp measurable_fst)).aestronglyMeasurable).mul he.norm.aestronglyMeasurable
  let r(y: Pane N) := -G.path.inChannels G.funds G.p G.beta y+greyFee Y 1 s i k y
  let H:= angleFin G.J.M N 4; let X:= δ*sites N; let v:=d+3*δ*sites N
  have hA : ∀ y:Orbit N, R y ≤ Real.exp (r y.1+(v+H)):= by
    intro y; obtain ⟨p',l,f',hP,hy⟩:= tilt_unmarked_point Y T y
    let A:= FlatPaneP 4 G.J.M N; let B:= ((exactShear 4 G.J.M N (by decide) p').foldC (tailor (tradew N l))); let Z:= B.glow (F (y.1,room Y s i y)); let Y':=acts (quant B.sell) (Graph.recX P.U G (room Y s i) y); let W:=Fock.grow (excitation A) 0
    have hw:‖acts W Y'‖ ≤ Real.exp (r y.1 + 3 * δ*sites N - a y) :=hy 0 (by simp)
    have hh:W= (1:FC (Single N)):=by unfold W Fock.grow; simp
    rw [hh,act_one] at hw
    change Real.exp (a y)*‖inner ℂ (mateK N) (acts _ (recX _ _ _ _))‖≤_
    rw [B.lawn]
    apply (mul_le_mul_of_nonneg_left ((norm_inner_le_norm ..).trans (mul_le_mul (le_of_eq hP)
      ((Graph.spentS _ Z Y').trans (mul_le_mul (h p' l y) hw (norm_nonneg _) (Real.exp_pos _|>.le))) (norm_nonneg _) (Real.exp_pos _|>.le))) (Real.exp_pos _|>.le)).trans
    change _*(Real.exp H *(_* _))≤_
    rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]; apply Eq.le; unfold v; congr 1; ring
  have hL:= normalized_integral Y p T v R hg (Eventually.of_forall fun y=>⟨mul_nonneg (Real.exp_pos _).le (norm_nonneg _),hA y⟩)
  refine ⟨hL.1,hL.2.trans_eq ?_⟩
  apply congrArg Real.exp; unfold N δ v; ring

end Papal
end LocalLimit
end Rate
end YM.CF.Py
