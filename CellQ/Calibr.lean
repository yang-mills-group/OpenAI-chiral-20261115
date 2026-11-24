import Rods.Fresh
import Verses.AnchorP
import YM.SU5.FiniteGaugeData.Pannier.Sketch
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief VolumeRate
open Roots Buffered LocalLimit LocalLimit.Papal Dyad Dyad.Keeping Mew Compass Drift
attribute [-instance] instDecidableEqLex
set_option quotPrecheck false
open Buffered Advance Afterglow YM.CF.Pannier.Chancel
namespace Decaf
open Stencil Push.SectorMeasure Larch
variable {K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group}{V:Grace K R L}{e kL:ℝ}{B:Side}{P:Grasp V.U B e}{qχ:Chi}(A:SiteLedger V P kL qχ){φ:Vxpert V A}{D0 f v D Q U:ℕ}(J:PaperTrace V A f v φ D0)(S:Tickets V D0 D Q R.L A f v)(h:Margin R.L D0 D Q U)
variable(j r p:ℕ){G:Calibration}{m:Side}(u₁: U=G.ℓ)(hf:f≤ j)(hr:j≤r)(hv:r≤ v)(hp:22≤ p)(C D₁:ℕ→ℝ)(he:Scree.mid (A.side j) B=G.c m)
local notation "tK"=> sportT A h j r p u₁ J S h hf hr hv u₁ hp C D₁ he
local notation "Σs" k:max=>mid (A.side k) B
variable (l:List (Tix A j))
section own
variable (Ξs Ξt:Mark (Scree.mid (A.side v) B)→ℂ)
local notation "n'" => (G.c m)
local notation "n₂"=> mid (A.side j) B
local notation "E"=> (steamPrice R.L j r v (A.gram v).p (A.gram r).p (A.money v) (A.money r))
include J S h u₁ hf hr hv hp
variable {μ χ d0:ℝ}
lemma linedance (plMu:0<μ)(pχ:0≤χ)(pD:0≤d0) (tM:(A.gram j).p.B^3+(A.gram j).p.B≤ p/2) -- name clash patch p
 (q:Sport.race tK l)(hs:∀ (I:Type)[LinearOrder I][Fintype I](o:I→Site n₂)(l:List (PairKey I)),Very_Ψ o (A.gram j).p.B→(wrap0 l).Nodup→ ‖Ξs (braidP (Yz:=φ) (v:=v) V A j r o C D₁ l)‖≤ μ^l.length*Real.exp (χ*Fintype.card (PairKey I)+ d0*sites n₂)) :
 ‖Ξs (Sport.film tK l)‖ ≤ (μ*Real.exp (2*χ))^l.length * Real.exp (d0*sites n₂):=by
 rw [links]; refine (hs _ _ _ (spreadRoster A J S h j r _ u₁ hf hr hv hp C D₁ he l tM q) (noDouble ..)).trans_eq ?_
 let I:= (PairKey (Fin l.length))
 have hq:(Fintype.card I:ℝ)=l.length*2:=by unfold I PairKey; change (Fintype.card (Fin l.length × Bool):ℝ)=_; simp
 rw [show (queueTag A j l).length=l.length from (by simp [queueTag]), (show (Fintype.card I:ℝ)= _ from hq), Real.exp_add, show χ*(l.length*2)=l.length*(2*χ) from ?_,Real.exp_nat_mul,←mul_assoc,←mul_pow]; ring

lemma perfusion (plMu:0<μ)(hlMu: μ ≤1)(pχ:0≤χ)(pD:0≤d0)
  (Hq:∀ l, Sport.race tK l→ ‖Ξs (Sport.film tK l)‖≤ (μ*Real.exp χ)^ l.length * Real.exp (d0*sites n₂))
  (tM:(A.gram j).p.B^3+(A.gram j).p.B≤ p/2)(w:∀ i,j≤ i → i<v→Niche R.L (C i) 0)(y:|revenue R.L C D₁ r j-1|≤1/4)
  (pΞ:Twosome G (Scree.mid (A.side v) B) Ξt)
  (pS:∀ t:Mark (mid (A.side v) B), RG.Envelope t→(∀ x,‖t x‖≤Real.exp ((E+(-Real.log μ))*sites n₂))→ ‖Ξs t-Ξt t‖≤1)(sV:∀ c:ℂ,∀ F, Ξs (c • F)-Ξt (c • F)= c*(Ξs F-Ξt F))
  {d:ℕ}(e₃:d+addgap G ≤ (G.c m).val)(w₃:∀i, rest G m (Sport.hopit tK l) i d)(q:Sport.race tK l)(hl:l≠[]): ‖Ξt (Sport.film tK l)‖ ≤ (μ*Real.exp (χ+1))^l.length * Real.exp (d0*(4*((d:ℝ)+(addgap G)))^4):=by -- handle empty by easiest extra 1. RP to ∅ invoices l always length=2. case omit entirely and require nonempty.
 obtain ⟨Kq,Lq,hz,hv',hq,W,hF⟩:= Sport.team _ Ξt pΞ l e₃ w₃ q
 let N:= (2^Kq)^4; have hp:0<N:=by unfold N; positivity
 let c:= Real.log μ
 have hc:c≤0:= Real.log_nonpos plMu.le hlMu
 let H:= μ*Real.exp χ
 have hH:0<H:= mul_pos plMu (Real.exp_pos _)
 have heE:0≤ E:=mul_nonneg (bpayG ..) (add_nonneg (pc_pos ..) (pc_pos ..))
 let V':= sites n₂
 let T:=Sport.film tK Lq
 have hn: (Lq.length:ℝ)≤ V':= countF _ (spreadRoster A J S h j r p u₁ hf hr hv ‹22≤p› C D₁ he Lq tM hq).1
 let a:= μ⁻¹^Lq.length; have ha:0 < a:=by unfold a; positivity
 have ht: ‖Ξt T-Ξs T‖≤ μ^Lq.length:=by
    obtain ⟨x₀,e⟩:= shelter A J S h j r p u₁ hf hr hv ‹22≤p› C D₁ he Lq w y
    let T':Mark (mid (A.side v) B):= (a:ℂ) • T
    obtain ⟨C',hC'⟩:=x₀.cost
    have hy(x:Fields (mid (A.side v) B)): ‖T' x‖=a*‖T x‖:=by unfold T'; rw [Pi.smul_apply,norm_smul,Complex.norm_real,Real.norm_of_nonneg ha.le]
    have he':Envelope T':=⟨measurable_const.smul (show Measurable T from x₀.meas),a*C',fun x=>by rw [hy]; exact mul_le_mul_of_nonneg_left (hC' x) ha.le⟩
    have hl:= pS T' he' (fun x=> by
       rw [hy]; apply (mul_le_mul_of_nonneg_left (e x) ha.le).trans; rw [show a=Real.exp ((-c)*Lq.length) from ?_,← Real.exp_add]; apply Real.exp_monotone; linarith only [mul_le_mul_of_nonneg_left hn heE,mul_le_mul_of_nonneg_left hn (neg_nonneg.mpr hc)]; rw [mul_comm (-c),Real.exp_nat_mul,Real.exp_neg]; unfold c a; rw [Real.exp_log plMu])
    change ‖Ξs ((a:ℂ) • T)-Ξt _‖ ≤ _ at hl; rw [sV,norm_mul,Complex.norm_real, Real.norm_of_nonneg ha.le,norm_sub_rev] at hl
    exact le_trans (b:=1/a) ((le_div_iff₀ ha).mpr (by linarith only [hl])) (le_of_eq (by unfold a; rw [one_div,inv_pow,inv_inv]))
 let u:= Real.exp (d0*V'); have hU: ‖Ξs T‖≤ H^Lq.length * u:=Hq _ hq
 have hp':0 ≤ V':=zero_le_one.trans (sites_pos n₂); have hu:1≤u:=Real.one_le_exp (mul_nonneg pD hp')
 have hy: ‖Ξt T‖≤ 2*(H^Lq.length*u):=by
    have hx:= norm_add_le (Ξt T-Ξs T) (Ξs T); rw [sub_add_cancel] at hx; apply (hx.trans (add_le_add ht hU)).trans; have he:μ ≤ H:= le_mul_of_one_le_right plMu.le (Real.one_le_exp pχ); have hw:=mul_le_mul (pow_le_pow_left₀ plMu.le he Lq.length) hu zero_le_one (pow_nonneg hH.le _); linarith only [hw]
 let Z:ℝ:=4*((d:ℝ)+addgap G)
 have hS: u ≤ (Real.exp (d0*Z^4))^N:=by
    have he': V' ≤ (N:ℝ)*Z^4:=by unfold V' Z; rw [he]; unfold sites; exact_mod_cast hv'
    rw [←Real.exp_nat_mul]; apply Real.exp_le_exp.mpr; exact (mul_le_mul_of_nonneg_left he' pD).trans_eq (by ring)
 refine le_of_pow_le_pow_left₀ (n:=N) hp.ne' ?_ (hF.trans (hy.trans ?_)); · positivity
 let X:= μ*Real.exp (χ+1); have hx:X= H*Real.exp 1:=by unfold X H; rw [Real.exp_add,mul_assoc]
 change 2*(H^Lq.length*u)≤(X^l.length*_)^N; rw [hx,mul_pow,mul_pow,show Lq.length=N*l.length from W]; let n:=l.length; let Y:= Real.exp (d0*Z^4)
 rw [←pow_mul, mul_pow H,Nat.mul_comm (l.length) N,←mul_pow μ]; change 2*(H^(N*l.length)*u)≤ _*(Real.exp 1)^(N*l.length)*Y^N
 have he₁:2 ≤ Real.exp 1:=by linarith only [Real.add_one_le_exp 1]
 have hn1:1 ≤ l.length:= List.length_pos_iff.mpr hl
 have he₂:2 ≤ (Real.exp 1)^(N*l.length):=he₁.trans (le_self_pow₀ (by linarith only [he₁]) (Nat.mul_ne_zero hp.ne' (Nat.ne_of_gt hn1)))
 have hk:=mul_le_mul he₂ hS (Real.exp_pos _).le (pow_nonneg (Real.exp_pos _).le _); nlinarith only [mul_le_mul_of_nonneg_left hk (pow_nonneg hH.le (N*l.length))] -- syntactic n*N vs N*n
end own
end Decaf
end YM.CF.Py.Rate
end
