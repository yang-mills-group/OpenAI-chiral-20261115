import YM.CF.Esti.Blink
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
variable {u v':ℝ}{j:ℕ}
def espy (P:Patch)(g x:ℝ)(n:ℕ):ℝ:= Real.exp (g*(Scales.p G P.L x)^2*n)
lemma pin_p(p:0<O.shares): 1 ≤ latticeFieldEstimates O j x:=by
 change 0 < latticeFieldEstimates O j x; unfold latticeFieldEstimates fulg plotBill epoch; positivity -- tune
-- dream detail
lemma dreamD (P:Patch)(n j:ℕ)(w s C M K:ℝ)(g:ℝ)(hp:0<g):∀ᶠ x in atTop,∀ {c f:Side}(S:StepData c f), S.patch=P →∀ (O:Stores S),0<O.shares →
 let A:=obv x j 100 O
 let B:=obv x j 110 O
 |dream P n x w s C M K A.card (nearNoise A).card (nearFace S B).card| ≤ espy P (7*g) x O.shares:=by
 let T (x:ℝ):=zest n*dam G n (fiery G x P.L/4) M C; have ht:Lento T:=by
    apply (Lento.sun _).times (Lento.piece _ _ _); apply Lento.times _ (Lento.sun _); apply Lento.sco; apply Lento.mono (Lento.ledge P.L (1/4)); filter_upwards [] with x; exact le_of_eq (by ring_nf)
 let U (x):= zest n*trout P x w s C M K n; have hu : Lento U:= (Lento.sun _).times ((((Lento.sco (Lento.ledge _ w)).times (Lento.sun _)).piece n _))
 filter_upwards [Work.E01.radiusB_tendsto.eventually_ge_atTop 1,cardS P T j g ht hp,cardS P U j g hu hp,cardS P (fun _=>zest n*1) j g (Lento.sun _) hp, cardS P (fun _=>zest n) j g (Lento.sun _) hp] with x hx ht hu hk hz c f S h O p A B
 let t:=espy P g x O.shares; have he(i:ℕ): t^i=espy P ((i:ℝ)*g) x O.shares :=by unfold t espy; rw [← Real.exp_nat_mul]; congr 1; ring
 obtain ⟨l,u,v,k⟩:=tune (F:=Classical.choice (Tree.select S.ratio S.patch.odd_side)) (A:=O) (O:=O) j hx
 have hy: |zest n| ≤ t:= (pow_one _).symm.le.trans (hz S h O 1 (pin_p p))
 have Hq: 0 < t:=Real.exp_pos _
 unfold dream; simp only [abs_mul,abs_pow]; -- tune
 change |zest n| * (|zest n| * (|zest n| * |dam _ _ _ _ _|)^_ * (|zest n| * |trout _ _ _ _ _ _ _ _|)^_) * (|zest n| * (|zest n| * _ )^_ * (|zest n| *_)^_) ≤ _
 refine le_trans (b:=t*(t*t*t)*(t*t*t)) ?_ (le_of_eq ((show t*(t*t*t)*(t*t*t)=t^7 from by ring).trans ((he 7).trans ?_))); swap; · push_cast; rfl -- tune
 simp only [←abs_mul]; gcongr ?_*(?_ *?_ *?_)*(?_*?_*?_) -- tune simp absorbs multiplying group not targeted
 exact ht S h O _ v
 exact hu S h O _ u
 exact hk S h O _ l
 exact hk S h O _ u
end YM.CF.Esti
