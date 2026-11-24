import YM.CF.Esti.East
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
variable {K': Teller G}{A:Stores S}{V:Config G c}{U:Config G f}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
lemma fuel_s{U:E→ Config G f}(p:FuelG E U x' n C)(s:Signed):FuelG E (pull s 0∘ U) x' n C:=by
 intro i; unfold grantB; simp_rw [Function.comp_def, Motion.turn_read]; split; exact gran (p _); exact p _
variable {U':E→ Config G f}{V':E→ Config G c} -- tune
lemma power_s (p:FuelG E U' x' n C)(t:FuelG E V' x' n C)(s:Signed)(i:Bond c) (k:S.Choices)(he:Frolic A x U' x')(hS:S.patch.Branches S.kernel G)(q:Chi)(hq:Dane G n q m)(hp: 1 ≤ m)(g:Volo S n a b C θ)(hθ:0 ≤ θ)(ha:0<a)(hC:1 ≤ C):Allows n (fun v=>layS q k A x a (U' v) (V' v) s i) x' (purM G n*C*horse S.patch n C a m θ):=by
 have he:= wears he p hq hS g ha hp hθ hC (sendEdge s 0 i) k; have hz : Allows n (fun v=> prism q k A x a (U' v) s i) x' (horse S.patch n C a m θ):=by unfold prism; dsimp only; split; exact pawn he; exact he
 exact (fuel_s t s i).bilinear (ContinuousLinearMap.mul ℝ SU.group.Mat) (pawn hz) le_rfl
variable {F:Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{β c' D L v':ℝ}
-- combine highest
section earn
variable (T:Tube G S)(A O: Stores S)(F:Forest S.ratio)(x:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(Y:LinkArray G (Frozen A x F))(l:ℕ)(z:LogArray G (Active A x F))(β:ℝ)(J:ChartRatio G)(j:ℕ)(s:ℝ)(w:ℝ)(E':E→ Config G c)
def lien(e u K v Q:ℝ)(n:ℕ):=let S:=zest n; S*(S*e*u)*(Jet.composeCost n (Real.exp v) Q) -- p gift
abbrev frieze (N:ℝ) := |β| * (N*C+2*N*carV n D+2*N*carV n D) -- type
variable (N:ℝ)(B:ℝ) (K': Teller G)(P:Patch)(hc:Cert P K' S T x)(ht:A.flags=RG.flags (temp x) (E' x'))(hp:0<β)(l':Volo S n s b C K)(hx:FuelG E (fun i=>fieldU β T F A (E' i) k x l q d Y z) x' n C)(hU:FuelG E E' x' n C)(hy:0<temp x)(hf:0<fiery G x S.patch.L)(ha:fiery G x S.patch.L ≤ s/2)(hn:shovel S.patch+10≤radiusB x)(hK:spanO T x)(hv: Offset.f0 T x A F k (E' x') q d Y=Rows.source T x (E' x') k (shots S x) A F q d Y)
variable (Q γ width:ℝ) (hj:d=width*fiery G x S.patch.L)(hW:∀ y: Signed,(cardsQ (whim x j O y):ℝ) ≤ N)(hG:∀ y: Signed, Circus T (fiery G x S.patch.L) (temp x) (turnStore y A).costs (traceZ (turnStore y A).flags) (fun i=>pull y 0 (fieldU β T F A (E' i) k x l q d Y z)) (pull y 0 ∘ E') (fun i=> layS q k A x s (fieldU β T F A (E' i) k x l q d Y z) (E' i) y) x' (Stores.till x) n B)
include Q γ width hc ht hp l' hx hU hy hf ha hn hK hv hW hj hG
lemma perkS{M:ℝ} (hP:SafeX K' P J w γ width Q j n x)(hw:PointCharge T x w γ)(hr:Packet O A ((j+5)*radiusB x))(hH:2 ≤ j)(hg:0<w)(hβ:β∈Set.Icc (y G S.patch.L x/2) (2*y G S.patch.L x))(t:ℝ)(h:Frolic A x (fun i=>fieldU β T F A (E' i) k x l q d Y z) x') -- tune
    (pz: Allows n (fun v=>wheel A F T x k q d Y (realP β T F A (E' v) k x l q d Y z) (E' v)) x' D)(pk: Allows n (fun v=>wheel A F T x k q d Y (nutM T A F (E' v) x k q d Y l) (E' v)) x' D)(pV:∀ i∈locals A O x F ((j+104)*radiusB x),Allows n (fun v=> putU β T F A (E' v) k x l q d Y z i) x' t)(hd:Dane G n q M) (hM:1 ≤ M)(h₁:1 ≤ C)(h₂:0≤ K)(h₃:0≤ B) (hq:Red J n t L) :
 let a:= obv x j 100 O
 let b' := obv x j 110 O
 let g:= dream S.patch n x w s C M K a.card (nearNoise a).card (nearFace S b').card
 let m' := grip n t d L t M (locals A O x F ((j+104)*radiusB x)).card
 let Y0 := -γ/4*(Scales.p G S.patch.L x)^2 * O.shares -SectorNext.Remainder.coin G S.patch.L Q n x*O.shares
 Allows n (grandP T A O F x k q d Y l z β J j s w E') x' (lien g m' K Y0 (frieze (C:=B) (n:=n) (D:=D) β N) n):=by
 intro a b' g m' Y0; let f'(v:E):= dawnP T A O F (E' v) x k q d Y l z β j s w; let L'(v:E):=beamE T A O F (E' v) x k q d Y l z β J j; let H:=σ T A O F x k q d Y l z β j s E'
 have he:Mesh n f' x' g:=como k w a b' h hn (funds_branch hc.funds.1) hx hU hd l' (by linarith only [hf,ha]) hM h₂ h₁
 have hm:Mesh n L' x' m':= capsule_p n _ _ pV q d le_rfl hq hd
 let C:= mesh _ _ _ he hm
 have hu: Allows n H x' (frieze (C:=B) (n:=n) (D:=D) β N):=past T E' n x A F k q d Y _ _ _ hG _ pz pk hW h₃
 exact lit_u (A:=0) C.nat C.cia hu fun q=>pull_l T A O F x k _ d Y l z β J j s w E' K' P hc ht hp l' hx hy hf ha hn hK hv Q γ width hj hP hw hr hH hg hβ q
end earn
end YM.CF.Esti
