import YM.CF.Reine.Fresh
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Reine
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti Cay Slate Forge Bloch Exterior
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {s:Signed}
section
open scoped Classical
-- kernel comparison on coarse config in one frame channel
local notation "B₀"=>radiusB x
local notation "r₀"=>Stores.till x
local notation "t₀"=>fiery G x S.patch.L
local notation "E₀"=>temp x
open Vol
variable (T:Tube G S)(x:ℝ)(M: Monk G S)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(F' W:BudgetPoint)
def fence(s:Signed): Dill S→ℝ:= let Y(i):=Esti.media i; let P:=wheel M.key M.park T x M.k q d (M.bush x); let U:=pull s 0 (M.sent x T q d l β); let V:=pull s 0 M.V; (fun i=> payX T x i U (S.prediction U (choice s M.k)) V)- Gloss S s (fun i=> Y i (P (M.fuel x T q d l β) M.V)- Y i (P (liftN T x M.V M.k M.key M.park q d (M.bush x) l) M.V))
def tend(s:Signed):Site f ⊕Site c→ℝ:= Sum.elim (clippedP T.up F' (Stores.till x) (pull s 0 (M.sent x T q d l β))) (- clippedP T.down W (Hors.cart x S.patch.L) (pull s 0 M.V))
def bend(s:Signed) := Sum.elim (fence T x M q d l β s) (tend T x M q d l β F' W s)
def tie(Q: Affine.Window S): Finset (Dill S) := Q.face.disjSum (Q.noise.disjSum (Q.coarse.disjSum Q.rows))
local notation "V₀"=>M.V
local notation "a₀"=> M.key
local notation "m₀"=> M.park
local notation "Y₀"=>M.bush x
local notation "Z₀"=> M.bell x
local notation "Q₀"=> M.k
local notation "ξ"=>M.sent x T q d l β
local notation "T₂"=>tend T x M q d l β F' W
variable {s:ℝ}{K':Teller G}{j:ℕ}
lemma mirX(s:Signed)(H:Affine.Window S)(i: Config G f) (t t': Slots S → ℝ) : (∑ v∈tie H,(payX T x v (pull s 0 i) (S.prediction (pull s 0 i) (choice s Q₀)) (pull s 0 V₀)- Gloss S s (t-t') v))=H.work T x (pull s 0 i) (choice s Q₀) (pull s 0 V₀)- ((∑ i∈ H.face,∑ j:Bool,t (s,.inl (i,j)))+∑ i∈H.noise,t (s,.inr i))+((∑ i∈ H.face,∑ j:Bool,t' (s,.inl (i,j)))+∑ i∈H.noise,t' (s,.inr i)):=by
 simp_rw [tie,sum_disjSum,payX,Gloss]; simp only [Sum.elim_inr,Sum.elim_inl, Pi.sub_apply, sum_sub_distrib,sum_const_zero,sub_zero] -- tune
 unfold Affine.Window.work onWindow; abel
lemma pond (H:Signed→Affine.Window S)(p:0<β)(he: f0 T x a₀ m₀ Q₀ V₀ q d Y₀=Rows.source T x V₀ Q₀ (shots S x) a₀ m₀ q d Y₀)(h:K'.Funds S T): -β * averaged (fun s=>∑ i∈tie (H s),fence T x M q d l β s i)=embH T a₀ m₀ V₀ Q₀ q β d x Y₀ l Z₀ H:=by
 let μ:= liftN T x V₀ Q₀ a₀ m₀ q d Y₀ l; let a:=M.fuel x T q d l β; let Y:=ownedAt T V₀ x a₀ Q₀ m₀ q d Y₀ H (ξ) a; let U(s):=columns V₀ x Q₀ T m₀ a₀ q d Y₀ μ s (H s); let W(z:Prices G (Active a₀ x m₀)):= wheel a₀ m₀ T x Q₀ q d Y₀ z V₀
 have hx(s:Signed):(∑ i∈tie (H s),fence T x M q d l β s i) =Y s+U s:=by
    let P(z) i:= Esti.media i (W z)
    change (∑ v∈tie _,(payX T x v (pull s 0 (ξ)) (S.prediction _ _) (pull s 0 V₀)- Gloss S s (P a-P μ) v)) = _; rw [mirX]; unfold U Y ownedAt; unfold P W; rw [← sells (V:=V₀) s _ _ he h,← sells (V:=V₀) s _ _ he h]; rfl
 simp_rw [hx]; rw [av_add]; unfold embH emission; change _= -β*averaged Y - averaged U/ _; rw [div_eq_mul_inv,by_coupling p]; ring
lemma bend_eq(Z:Signed)(i:Along S)(t:i∈rush x a₀ Z j)(p:BoltP a₀ ξ V₀ x)(he:spanO T x)(hq:spanC T x)(hv:taxM x≤ j*radiusB x)(h:F'.threshold=fiery G x S.patch.L)(hk:W.threshold=temp x)(hp:0<fiery G x S.patch.L) : bend T x M q d l β F' W Z i=dense T x q d l β Z i M:=by
 rcases i with i|i|i
 next => refine congrArg₂ (fun a b:ℝ=>a-b) (Eq.symm (bay (U:=pull Z 0 (ξ)) (V:=pull Z 0 V₀) (o:=(turnStore Z a₀).place) (k:=choice Z M.k) (T:=T) ⟨he,hq,p.1 Z, p.2 Z⟩ hp i ?_)) rfl; intro v; exact (mem_filter.mp t).2 ((dome_turn ..).mp (Corona.halo_mono hv (Finset.Subset.refl _) v))
 next => exact bail_f hv p F' h i t
 exact congrArg (- ·) (bail_c hv p W hk i t)
end
end YM.CF.Reine
