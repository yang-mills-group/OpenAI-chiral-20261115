import YM.CF.Stake.Spruce
import YM.CF.Iva.Base
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pail
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Corne Lich Lich.Muster Rink Jet Vol
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}
variable {x e m:ℝ}(A:Muster G S x e T)(M:Monk SU.group S)(s:Signed)(b:Site (Domain N B))(g:Site (Domain N B)→ SU.group.El)
open AnalyticBridge.GaussianFieldAlignment Tensor Orthogonal PhysicalNext.OrderedAffine2B.SymRows Channels Locations
variable {d:ℕ}
local notation "d"=> Domain N B
local notation "d'"=> Domain P B
local notation "τ"=> Directions SU.group d
local notation "ρ"=> Directions SU.group d'
open Tye Iva Stake Fief
variable(f:Sweep (mid N B))(U:Config SU.group (Domain N B))(i:Site (Domain N B))
abbrev vigil := Tensor.lifting (scatter f.s (Facet.pasta f) U) (StepData.sendBonds f.s (Facet.pasta f))
def peakZ : τ ≃L[ℝ] τ:= let P:= vigil f U; if f.charge then P.trans (Tensor.lifting (Char.shiftF _) (Equiv.refl _)) else P
lemma peak_k: ‖(peakZ f U).toContinuousLinearMap‖ ≤ 1:=by
 apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y=>?_ ; rw [one_mul]; change ‖peakZ f U y‖≤_; unfold peakZ; dsimp only; split; change ‖Tensor.lifting (Char.shiftF _) (Equiv.refl _) (vigil f U y)‖≤_; unfold vigil; rw [Tye.hype,Tye.hype]; exact (Tye.hype ..).le
lemma rayT(y:τ): rough (rot f (M.atop y x)) 0= rough ((rot f M).atop (peakZ f M.V y) x) 0:=by
 let h1:= Channels.insert_turn f.s (Facet.pasta f) M.V (temp x • y); rw [map_smul] at h1; apply Tye.flank <;> unfold rot dice peakZ <;> dsimp only <;> cases p:f.charge <;> first|rfl|skip
 · exact h1.symm
 have he:=Char.inc_re (temp x • (vigil f M.V y)) (Lattice.pull f.s (Facet.pasta f) M.V); rw [map_smul] at he; exact (congrArg Reef.echo h1).symm.trans he.symm -- tune
lemma stalk_r{k:ℕ}(z:ℝ)(X:τ→ℂ)(u:Allows k X 0 z): Allows k (fun y=> payZ f (X y)) 0 z:=by
 obtain ⟨F,hp,g⟩:=pay_he (wageZ f) -- sign? inspect
 refine ((u.linear F hp).mono (by rw [one_mul])).germ (Eventually.of_forall fun i=>?_); exact g (X i) -- check
variable{k:ℕ}{b1 b2 b3 Z₀:ℝ}
lemma marble_k(v:Allows k (fun y=>footS A (M.atop y x) i) 0 b1)(p:Allows k (fun y=>fotoP A (M.atop y x) i) 0 b2)(g:Allows k (fun y=>motoP A (M.atop y x) i) 0 b3):Allows k (fun y=>marble A (M.atop y x) i) 0 (b1+(b2+b3)):=Newt.subtract_p ((v.linear Complex.ofRealCLM (show ‖Complex.ofRealCLM‖≤ 1 by simp)).mono (by rw [one_mul])) (p.add g)
def rungL (k:ℕ)(a b c:ℝ):= Jet.composeCost k (a+(b+c)) 1
lemma patrol_k {E:Type}[Fintype E](V:Sweep (mid N B)→ Equiv.Perm E)(F: Monk SU.group S→ E →ℂ) (i:E)(v: Sweep (mid N B)→ ℝ)(p:∀ f:Sweep (mid N B),Allows k (fun y=> F (rough ((rot f M).atop y x) 0) ((V f).symm i)) 0 (v f)): Allows k (fun y=> patrol V F (M.atop y x) i) 0 ((Fintype.card (Sweep (mid N B)):ℝ)⁻¹ * ∑ f:Sweep (mid N B),Jet.composeCost k (v f) 1):=by
 let Z:= Sweep (mid N B); have hx(z:Z): Allows k (fun y:τ=> payZ z (F (rough (rot z (M.atop y x)) 0) ((V z).symm i))) 0 (Jet.composeCost k (v z) 1):=by
    refine stalk_r z _ _ ((hg_k (peakZ z M.V).toContinuousLinearMap (peak_k ..) _ _ (p z)).germ ?_); filter_upwards with y; rw [rayT]; rfl -- tune
 exact ((Jet.allows_sum (fun i (_: i∈(univ:Finset Z))=> hx i)).smul (Fintype.card Z:ℝ)⁻¹).mono (by rw [abs_of_nonneg (by positivity)])
lemma mare_k (p:∀ f:Sweep (mid N B),Allows k (fun y=> marble A ((rot f M).atop y x) ((chart f).symm i)) 0 (b1+(b2+b3))): Allows k (fun y=> mare A (M.atop y x) i) 0 (rungL k b1 b2 b3):=by
 let L:=Fintype.card (Sweep (mid N B)); apply (patrol_k M (fun f:Sweep (mid N B)=>chart f) (marble A) _ (fun _=>b1+(b2+b3)) (fun f=>?_)).mono
 · unfold rungL; rw [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,←mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]
 exact p f
lemma mare_t(i:Site (Domain N B)):mare A (violet M) i=mare A M i:=by
 unfold Tye.mare patrol; apply congrArg; apply sum_congr rfl; intro i _; rw [cloak_t,show rough (violet M) 0 = rough M 0 from rfl,←cloak_t]
end YM.CF.Pail
