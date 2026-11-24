import YM.CF.Esti.Duo
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
variable {F:Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{β c' D L v':ℝ}
section u
variable (T:Tube G S)(V:E→ Config G c)(j:ℕ)(x:ℝ)(A O:Stores S)(F:Forest S.ratio)(u:S.Choices)(q:Chi)(θ:ℝ)(Y: LinkArray G (Frozen A x F))(a δ:E→ Prices G (Active A x F))(s:ℝ)(w:ℝ)
abbrev whim(y:ℝ)(j:ℕ)(A:Stores S)(s:Signed):= anchorage (turnStore s A) (j*radiusB y)
abbrev obv(y:ℝ)(j d:ℕ)(A:Stores S):= A.dome ((j+d)*radiusB y)
local notation "U" =>fun y:E=>landed x A F (V y) Y (a y)
local notation "Z"=>whim x j O
 
lemma postC{y:E}(R: Prices G (Active A x F))(h:FuelG E U y n C)(hp:Offset.f0 T x A F u (V y) q θ Y=Rows.source T x (V y) u (shots S x) A F q θ Y)(hq:a y=δ y+coupling β • R)(hk:K'.Funds S T) (hZ:total A x q ((U) y) (obv x j 110 O) ≠ 0)(hv:Volo S n s b C K)(hf:fiery SU.group x S.patch.L ≤ s/2)(ht:0<temp x)(hh:shovel S.patch+10≤ radiusB x) (he:0<fiery SU.group x S.patch.L)(hp':spanO T x)(hb:0<β)(ho:A.flags=RG.flags (temp x) (V y)): pist T V x A F u q θ Y a δ s Z β y= emission T (V y) x A u F q θ Y Z β (δ y) R:=by
 let H(z:Signed):= ownedAt T (V y) x A u F q θ Y (whim x j O) ((U) y) (a y) z; let Kappa (z:Signed):= columns (V y) x u T F A q θ Y (δ y) z (Z z)
 let P:= H+Kappa
 have hg:S.patch.Branches S.kernel G:= hk.knobs.symm ▸ hk.kernel
 have he'(z:Signed): caseP T x A u q s ((U) y) (V y) z (Z z)-columnP z (wheel A F T x u q θ Y (a y) (V y)) (Z z)+columnP z (wheel A F T x u q θ Y (δ y) (V y)) (Z z)=P z:=by
    have hw:j*radiusB x+5*radiusB x ≤ (j+110)*radiusB x:=by rw [Nat.add_mul]; omega
    rw [keeps_f T _ _ _ _ hv h z hp' ho hh he ht hf hw hg hZ, sells z _ _ hp hk,sells z _ _ hp hk]; rfl -- tune
 unfold pist; simp_rw [he']; unfold P; simp only [Pi.add_apply]; rw [av_add]; unfold emission H Kappa; simp_rw [hq]; rw [mul_add,div_eq_mul_inv, show (coupling β ^ 2)⁻¹=β from by_coupling hb]; ring
lemma thins (q:Chi)(v:ℝ)(A:Stores S)(x w:ℝ)(u:S.Choices)(W:Config G f)(V:Config G c)(N M M': Support c) (z: N ⊆ M)(p: receipts q A x w N (nearFace S M) (nearNoise N) W V u≠ 0) : receipts q A x w N (nearFace S N) (nearNoise N) W V u≠ 0:=by
 unfold receipts profilesHere at *; refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul p)))) (right_ne_zero_of_mul (left_ne_zero_of_mul p))) (right_ne_zero_of_mul p)
 apply Finset.prod_ne_zero_iff.mpr; intro i l; exact fun g=> left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul p)) (Finset.prod_eq_zero (mem_filter.mpr ⟨mem_univ _,fun h=>(mem_filter.mp l).2 (Disjoint.mono_right z h)⟩) g)
end u
lemma posts (r:ℝ)(V:E→SU.group.Color)(p: Allows n V x' C)(q:Chi)(D:ℝ)(h: Dane G n q D): Mesh n (fun u=> Next.SectorChange.broad q r (V u)) x' (Jet.composeCost n D ((2/r^2)*(2^n*C*C))):=by
 have he:=h _ _ x' _ r true (cow p); have hp(u:E): Next.SectorChange.broad q r (V u)=testing q r (‖V u‖^2/2) true:=by unfold Next.SectorChange.broad Chi.innerShare testing cliff; rw [div_pow]; simp only [ite_true]; congr 1; ring
 simp_rw [hp]; exact ⟨he.1,he.2⟩
end YM.CF.Esti
