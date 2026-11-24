import Merino.Regalia
import Merino.Receipt
import YM.SU5.Exchange.Pace.Cult
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.CF.Merino
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Drapes Metric
open _root_.Zephyr.Chern
open scoped Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Finset Swell

variable {n:Side}

open Py.Rate.LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Skye Scree Vale RG
open Py (hueW stemS pinpr)
variable (P:Spine)

abbrev RegNum(s i:ℕ): Side:= age P.run i s
abbrev LedgerM (s i k:ℕ):GramM (RegNum P s i):= RootBook P.run i k s
abbrev LoomM (s i:ℕ): Loom (RegNum P s i):= (P.run.voyage i).CapeT s


/-- z gauge midpoint physical zero. For a global origin translate
at price tick QG, keep AP winds of the formula; `m` a matter count. -/
abbrev zeroBase:Cover:=-1
abbrev priceTick : ℕ:=8*P.par.block.val
/-- The x index in predicted prices, *not* actual beta field value. -/
abbrev scaleM(s:ℕ): ℝ:= hat P.par.R.L P.par.x s
abbrev radiusM(s:ℕ): ℕ:= Pressure.radiusB (scaleM P s)
abbrev tempM(s:ℕ): ℝ:= Pressure.temp (scaleM P s)
abbrev Qprice(s:ℕ): ℝ:= pinpr P.par.R.L (scaleM P s)
/-- unamplified prefactor vs. for the opening contract use `hueM`. -/
abbrev clearM(s:ℕ): ℝ:= Qprice P s/(tempM P s)^2
abbrev hueM(s:ℕ): ℝ:= hueW P.par.R.L (scaleM P s)
/-- retain exact date for exponentially small currency -/
abbrev loseM(a:ℝ)(s:ℕ): ℝ:= Real.exp (-a* ((radiusM P s/10:ℕ):ℝ))

def admitM(s i k:ℕ):Prop:= (P.run.voyage i).kick ≤ k ∧ s<P.run.uv k

/- Betting range in outer attestations. Use abbreviation in proofs avoids
nested `filter_upwards`. -/
def onReg (Q:ℕ→ℕ→ℕ→Prop):Prop:=∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop,
   ∀ k:ℕ,admitM P s i k → Q s i k
lemma lose_limit (a:ℝ)(ha:0<a): Tendsto (loseM P a) atTop (𝓝 0):=by
  apply Real.tendsto_exp_atBot.comp
  have h:Tendsto (fun s:ℕ=>radiusM P s/10:ℕ→ℕ) atTop atTop:=by -- parse adjust
    rw [Filter.tendsto_atTop]
    intro r
    filter_upwards [(Work.E01.radiusB_tendsto.comp (turnover P.par)).eventually_ge_atTop (r*10)] with s t
    exact (Nat.le_div_iff_mul_le (by decide:0<10)).mpr t
  exact Filter.Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr ha) (tendsto_natCast_atTop_atTop.comp h)


lemma admits (s i:ℕ):∀ᶠ k in atTop,admitM P s i k :=
  (eventually_ge_atTop _).and (P.run.uv_grows.tendsto_atTop.eventually_gt_atTop _)

lemma hue_positive (s:ℕ):0<hueM P s:=by
  have hx:=Vale.crown P.par.R.L P.par.x s
  have h0:0< scaleM P s:=(zero_lt_one.trans_le P.run.oneP).trans_le hx
  have hs:0≤SU.group.slopeConstant*Real.log P.par.R.L.val:=
    mul_nonneg (Work.E07.slope_nonneg _) (Real.log_nonneg (Nat.one_le_cast.mpr P.par.R.L.property))
  have h1:0<Qprice P s:=pow_pos (BPress.g_pos (add_pos_of_pos_of_nonneg h0 hs)) _
  have ht:0<tempM P s:=((P.run.meter.a s).threshold_pos.trans_eq (P.run.meter.boot s).1)
  exact mul_pos (div_pos h1 (pow_pos ht _)) (Real.rpow_pos_of_pos (BPress.drift_pos _) _)


lemma frame_fit (hM:8 ∣ P.par.M.val)(s i:ℕ): 2 * priceTick P ∣ (RegNum P s i).val:=by
  obtain ⟨b,hb⟩:=hM
  obtain ⟨⟨N,h,_⟩,_⟩:=P.run.lease i
  unfold RegNum priceTick
  unfold age
  refine ⟨b*N.val*P.par.R.L.val^s,?_⟩
  rw [show P.run.ir i= _ from h]
  change (N.val*P.par.M.val*(P.par.R.L.val ^ s))*2*P.par.block.val=_
  rw [hb];ring

lemma terminal_beta(i k:ℕ): (LedgerM P 0 i k).beta=P.par.x:=
  Buffered.Afterglow.Tapestry.prescribed_pivot P.run i k
lemma calibrated {s i k:ℕ}(h:s≤P.run.uv k):
    (LedgerM P s i k).p=P.run.meter.a s ∧ matchedX (scaleM P s) (LedgerM P s i k).beta:=
 let X:=(P.run.voyage i).X (P.run.uv k); ⟨(X.pull.owns s h).width.symm, X.pull.sift s h⟩

end YM.CF.Merino
