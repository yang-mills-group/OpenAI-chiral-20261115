import YM.CF.Esti.Gasp
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
abbrev wheelAux (T: Tube G S)(q:Chi)(d:ℝ)(x:ℝ)(A:Stores S)(F:Forest S.ratio)(V:Config G c)(D:ℝ)(n:ℕ)(k:S.Choices):Prop:= Offset.f0 T x A F k V q d=Rows.source T x V k (shots S x) A F q d∧∀ Y:LinkArray G (Frozen A x F),∀ (r:Directions G c→Prices G (Active A x F))(a:ℝ), Allows n r 0 a → Allows n (fun i=> wheel A F T x k q d Y (r i) (Vmove x V i)) 0 (D*(a+fiery G x S.patch.L))
def perL (S:StepData c f)(n j:ℕ)(x w s d C D M Q γ u m L K β:ℝ)(O A:Stores S)(F:Forest S.ratio)(r:ℝ):ℝ:=let H:=obv x j 100 O; let b:= obv x j 110 O; lien (dream S.patch n x w s C M K H.card (nearNoise H).card (nearFace S b).card) (grip n u d m u M (locals A O x F ((j+104)*radiusB x)).card) K (-γ/4*(Scales.p G S.patch.L x)^2*O.shares-SectorNext.Remainder.coin G S.patch.L Q n x*O.shares) (frieze (C:=D) (n:=n) (D:=L) β r) n -- G remove
lemma heat {R δ ξ v η σK e m:ℝ}(hn: 3 ≤ n)(hh:v ≤ 1)(hp:Red J n v η)(hM:1 ≤ M)(hQ:Dane G n q M)(hξ: 1 ≤ ξ)
 (hs:∀ (U:E→ Config G f)(N:E→ Config G c)(M':E→Bond c→SU.group.Mat)(X:Finset (Cell c))(F:Finset (Cell f)), (∀ i,Allows n (fun v=> M' v i) 0 (purM G n*C*horse S.patch n C s M K))→HeldT U F 0 → HeldT N X 0 →FuelG E N 0 n C → FuelG E U 0 n C → Circus T (fiery G x S.patch.L) (temp x) F X U N M' 0 (Stores.till x) n D)
 (hl: ∀ (V:Config G c)(z:E→L[ℝ] Directions G c),‖z‖≤1 → FuelG E (Vmove x V ∘ z) 0 n ξ∧∀(Y: LinkArray G (Frozen A x F))(U:E→ Prices G (Active A x F)), (∀ i:Active A x F, Allows n (fun y=> tape (U y) i) 0 1) → FuelG E (treeF Y (Vmove x V ∘ z) U) 0 n ξ)
 (hk:0≤K)(hL:0≤ D)(hw:0 < σK)(h:C≥ξ)(i:ℕ)(W: MossX n i x A F T V k e d (fiery G x S.patch.L) q)(j:ℕ)(p:e≥ 0)(Y:LinkArray G (Frozen A x F))(H:Volo S n s b C K)(T':wheelAux T q d x A F V σK n k)
 (hX:Cert P K' S T x)(ht:A.flags=RG.flags (temp x) V)(hc:SafeX K' P J w γ m Q j n x)(hr:Packet O A ((j+5)*radiusB x))(ht':PointCharge T x w γ)(hθ:0<w)(hj:2≤j)(hy:shovel S.patch+10≤radiusB x)(hK:spanO T x)(h':d=m*fiery G x S.patch.L)(hz:0<temp x)(hB: 0<fiery G x S.patch.L)(hv: fiery G x S.patch.L ≤ s/2)(V':E →L[ℝ] Directions G c)(hr':‖V'‖≤1)(u:∀ i, axl A.flags (temp x • V' i)= temp x • V' i)(z: LogArray G (Active A x F))(c':‖z‖ ≤ R)(hβ:β∈Set.Icc (y G S.patch.L x/2) (2*y G S.patch.L x))(J':0<β)(r:ℝ)(hY:∀ y:Signed,(cardsQ (whim x j O y):ℝ) ≤ r) (τ: e*fiery G x S.patch.L+|coupling β| * (2^n*e*R) ≤ δ) (h₂:Push.Uniform.shade G*Jet.composeCost n δ 1 ≤ v) (h₃: σK*(δ+fiery G x S.patch.L) ≤ L):
 Allows n (grandP T A O F x k q d Y i z β J j s w (Vmove x V ∘ V')) 0 (perL S n j x w s d C D M Q γ v η (Jet.composeCost n L 1) K β O A F r) :=by
 obtain ⟨p₁,p₂⟩:=ready_heat Y z _ W R c' p (β:=β); let U':= Vmove x V ∘ V'; have hv': U' 0=V:=by simp [U',Vmove]
 let g(t:E):=realP β T F A (U' t) k x i q d Y z
 let A':=treeF Y U' g; have h': Allows n g 0 (Jet.composeCost n δ 1) := (Allows.comp (g:=fun v : Directions G c=>realP β T F A (Vmove x V v) k x i q d Y z) (f:=V') ((map_zero V').symm ▸ p₂.mono τ) (allows_linear hr' (by simp)))
 have hp'(i):= (shelJ (A:=A) (F:=F) h' i).mono h₂; obtain ⟨hu,ha⟩:=hl V V' hr'; have H' := pileD (Y:=Y) (V':=U') (fE:=g) (x':=0) hy -- tune
 have H1:FuelG E A' 0 n C:=fun i=> (ha Y g (fun i=>(hp' i).mono hh) i).mono h
 have H2:FuelG E U' 0 n C:=fun i=> (hu i).mono h
 have pV:∀ᶠ i in 𝓝 0, Agrees (halo 15 A.flags) (U' i) (U' 0):=curtainP u
 have hss(t:Signed):= hs _ _ _ (traceZ (turnStore t A).flags) (turnStore t A).costs (power_s H1 H2 t · k H' (funds_branch hX.funds.1) q hQ hM H hk (by linarith) (hξ.trans h)) (tide_d t) (face_h pV t) (fuel_s H2 t) (fuel_s H1 t)
 have he : e*fiery G x S.patch.L ≤ δ:= (le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (mul_nonneg (mul_nonneg (by positivity : (0:ℝ)≤2^n) p) ((norm_nonneg _).trans c')))).trans τ
 apply perkS T A O F x k q d Y i z β J j s w U' r D K' P hX (ht.trans (hv'.symm ▸ rfl)) J' H H1 H2 hz hB hv hy hK (show Offset.f0 T x A F k (U' 0) q d Y= _ from by rw [hv']; exact congr_fun T'.1 Y) Q γ m ‹_› hY hss hc ht' hr hj hθ hβ v H' _ _ (fun i _ => hp' i) hQ hM (hξ.trans h) hk hL hp
 · have H:= (T'.2 Y _ _ (p₂.mono τ)).mono h₃; exact ((map_zero V').symm ▸ H : Allows n _ (V' 0) L).comp (f:=V') (allows_linear hr' (by rw [map_zero,norm_zero]; exact zero_le_one)) -- fix around at V'=0
 have H:=(T'.2 Y _ _ (p₁.mono he)).mono h₃; exact ((map_zero V').symm ▸ H : Allows n _ (V' 0) L).comp (f:=V') (allows_linear hr' (by rw [map_zero,norm_zero]; exact zero_le_one))
end YM.CF.Esti
