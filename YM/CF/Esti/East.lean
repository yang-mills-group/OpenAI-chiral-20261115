import YM.CF.Esti.Coup
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
variable {S}{n:ℕ}{θ a b m t K C:ℝ}
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {c' D L v':ℝ}
variable (T:Tube G S) (A O:Stores S)(F:Forest S.ratio)(V:Config G c)(x:ℝ)(k:S.Choices)(q:Chi)(d:ℝ)(Y: LinkArray G (Frozen A x F))(l:ℕ) (z:LogArray G (Active A x F)) -- tune κ
abbrev bagM (β:ℝ):= pushP T A F V k q d x Y l z
abbrev nutM := liftN T x V k A F q d Y l
-- evaluate on path with u literal at actual Z (Y fixed). $crust$ receipt product only. later optimizer
variable (β:ℝ) (J:ChartRatio G)(j:ℕ) (s:ℝ) (w:ℝ)
local notation "a_"=> realP β T F A V k x l q d Y z
local notation "H"=> fieldU β T F A V k x l q d Y z
def dawnP := cohoT A x w s q V H k (obv x j 100 O) (obv x j 110 O)
def beamE := capsule x A F q d J (locals A O x F ((j+104)*radiusB x)) (tape a_)
def ma := dawnP T A O F V x k q d Y l z β j s w * beamE T A O F V x k q d Y l z β J j
-- E rep burden analytic projections on E moves only
section gate
variable (U':E→ Config G c)
-- Notations V collision. rename strategy.
local notation "fps"=>fun i : E=> realP β T F A (U' i) k x l q d Y z
local notation "Η"=>fun i : E=> fieldU β T F A (U' i) k x l q d Y z
local notation "q'"=> fun i:E=> ma T A O F (U' i) x k q d Y l z β J j s w
def σ := pist T U' x A F k q d Y fps (fun i=> nutM T A F (U' i) x k q d Y l) s (whim x j O) β
def grandP := (q') * fun i=> Real.exp (σ T A O F x k q d Y l z β j s U' i) -- tune arg order
variable (K': Teller G)(P:Patch)(hc:Cert P K' S T x)(ht:A.flags=RG.flags (temp x) (U' x'))(hp:0<β)(l':Volo S n s b C K)(hx:FuelG E (fun i=>fieldU β T F A (U' i) k x l q d Y z) x' n C)(hy:0<temp x)(hf:0<fiery G x S.patch.L)(ha:fiery G x S.patch.L ≤ s/2)(hn:shovel S.patch+10≤radiusB x)(hK:spanO T x)(hv: Offset.f0 T x A F k (U' x') q d Y=Rows.source T x (U' x') k (shots S x) A F q d Y)
include ht hp hx hy hf ha l' hn hK hv hc
local notation "Q'"=> dawnP T A O F (U' x') x k q d Y l z β j s w
lemma palmC (p:Q' ≠0) : σ T A O F x k q d Y l z β j s U' x'=embH T A F (U' x') k q β d x Y l z (whim x j O):=by
 let f(i):=nutM T A F (U' i) x k q d Y l; let X:= U' x'; let z':=pushP T A F X k q d x Y l z
 have he: (fps) x'=f x'+coupling β • z':=rfl
 have hg:total A x q ((Η) x') (obv x j 110 O) ≠0:= fun u=> p (by unfold dawnP cohoT; change (_*_)*_=0; rw [show total _ _ q _ _=_ from u,zero_mul,zero_mul])
 exact postC T U' j x A O F k q d Y (fps) f s z' hx hv he hc.funds.1 hg l' ha hy hn hf hK hp ht
omit hp hv hK hy hc
lemma chest : receipts q A x w (obv x j 100 O) (nearFace S (obv x j 110 O)) (nearNoise (obv x j 100 O)) ((Η) x') (U' x') k=Q':=by
 change _=cohoT A x w s q (U' x') ((Η) x') k _ _; symm; apply works_b A q k _ _ hx O _ (Finset.Subset.refl (obv x j 110 O)) _ hn hf ha l' _ _ ht
 simp only [Nat.add_mul]; omega
variable (Q γ width:ℝ) (hj:d=width*fiery G x S.patch.L) -- v' witness LebD
include hK hp hy hv hc hj
lemma pull_l(hQ:SafeX K' P J w γ width Q j n x)(hw:PointCharge T x w γ)(hr:Packet O A ((j+5)*radiusB x))(hH:2 ≤ j)(hg:0<w)(hβ:β∈Set.Icc (SectorNext.Remainder.Scales.y G S.patch.L x/2) (2*SectorNext.Remainder.Scales.y G S.patch.L x))(p:(q') x'≠0) : σ T A O F x k q d Y l z β j s U' x' ≤ -γ/4*(Scales.p G S.patch.L x)^2 * O.shares -SectorNext.Remainder.coin G S.patch.L Q n x*O.shares :=by
 have hJ:=left_ne_zero_of_mul p -- tune unfolded lhs
 have hθ: (obv x j 100 O) ⊆ obv x j 110 O := farther (Nat.mul_le_mul_right _ (by omega))
 let t:=nearFace S (obv x j 100 O)
 have hh: receipts q A x w (obv x j 100 O) t (nearNoise (obv x j 100 O)) ((Η) x') (U' x') k≠0:= thins q 0 _ _ _ _ _ _ _ _ ∅ hθ (by rw [chest T A O F x k q d Y l z β j s w U' ht l' hx hf ha hn]; exact hJ)
 have hz:=right_ne_zero_of_mul p; rw [palmC T A O F x k q d Y l z β j s w U' K' P hc ht hp l' hx hy hf ha hn hK hv hJ]; subst d
 exact (ditto q K' γ width Q J j n hQ T O hc ht hw hr hH q l hg β z hβ hh hz).2
end gate
end YM.CF.Esti
