import YM.CF.Esti.Mode
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
lemma payer (P:Patch)(n j:ℕ)(w width C D M L u m K s:ℝ)(h:0<γ)(hD:0≤D)(hL:0≤L):∀ᶠ x in atTop,∀{c f:Side}(S:StepData c f),S.patch=P →∀ (A O:Stores S),0<O.shares→∀ (F: Forest S.ratio)(β:ℝ),β∈Set.Icc (Scales.y G P.L x/2) (2*y G P.L x) → perL S n j x w s (width*fiery G x P.L) C D M 0 γ u m L K β O A F (latticeFieldEstimates O j x) ≤ Real.exp (-γ/8 * (Scales.p G P.L x)^2*O.shares):=by
 let k:=γ/200; have hk:0<k:=by unfold k; positivity
 filter_upwards [dreamD P n j w s C M K k hk, beamT P k n j hk u m M u width,cardinalE P n j D L hD hL k hk,cardS P (fun _=>zest n) j k (Lento.sun _) hk,cardS P (fun _=>(n.factorial:ℝ)) j k (Lento.sun _) hk] with x hp hQ hv hK hL c f S he A O p F β ht
 let a:=obv x j 100 O; let g:=obv x j 110 O; let l:= Scales.p G P.L x; let t:ℝ:= width*fiery G x P.L; let d:= dream P n x w s C M K a.card (nearNoise a).card (nearFace S g).card; let M:= grip n u t m u M (locals A O x F ((j+104)*radiusB x)).card; let Q:= frieze (n:=n) (C:=D) (D:=L) β (latticeFieldEstimates O j x); let V:= -γ/4*l^2*O.shares
 let Z y:= espy P (y*k) x O.shares
 have hqp(y):0 ≤ Z y:= (Real.exp_pos _).le
 unfold perL; dsimp only; rw [he, coin]; simp only [zero_mul,sub_zero]; change lien d M K V Q n ≤ _
 unfold lien; dsimp only; apply (le_abs_self _).trans; let z:= zest n; have hx:|d| ≤ Z 7:= hp S he O p; have hh: |M| ≤ Z 3:= hQ S he A O F p; have hu:|1+Q|^n ≤ Z 2:= by unfold Z; rw [two_mul]; exact hv S he O p β ht
 have hz:|z| ≤ Z 1:=by unfold Z; rw [one_mul]; exact (pow_one _).symm.le.trans (hK S he O 1 (pin_p p))
 have hw: |(n.factorial:ℝ)| ≤ Z 1:=by unfold Z; rw [one_mul]; exact (pow_one _).symm.le.trans (hL S he O 1 (pin_p p))
 unfold Jet.composeCost; simp only [abs_mul, abs_pow,abs_of_pos (Real.exp_pos V)]
 apply le_trans (b:=Z 1*(Z 1*Z 7 * Z 3)*(Z 1*Real.exp V* Z 2)) ?_; swap -- tune
 · change |z| * (|z| * |d| * |M|) *_≤_; gcongr <;> unfold Z espy <;> positivity
 unfold Z V espy; simp only [← Real.exp_add]; apply Real.exp_monotone; unfold k at *; change _ ≤ (-γ)/8*l^2*_; unfold l at *; have hb1:=sq_nonneg (Scales.p G P.L x); nlinarith only [mul_nonneg (mul_nonneg h.le hb1) (Nat.cast_nonneg (α:=ℝ) O.shares)] -- tune
end YM.CF.Esti
