import YM.CF.Reine.Whee
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
open Vol
variable (T:Tube G S)(x:ℝ)(M: Monk G S)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)(F' W:BudgetPoint)
local notation "V₀"=>M.V
local notation "a₀"=> M.key
local notation "m₀"=> M.park
local notation "Y₀"=>M.bush x
local notation "Z₀"=> M.bell x
local notation "Q₀"=> M.k
local notation "ξ"=>M.sent x T q d l β
local notation "T₂"=>tend T x M q d l β F' W
open Affine
lemma usus(S:StepData c f): tie (Appel.globe S)=univ:=by ext i; rcases i with i|i|i|i <;> simp [tie,Appel.globe]
def keyU (j:ℕ)(O:Stores S):ℝ:= -β*averaged (fun s=>∑ i∈lyn x s O j,T₂ s i)
private lemma size_p (j:ℕ)(s:Signed)(h:j*radiusB x≤ r)(F:Along S→ℝ): (∑ i: Along S,F i)= (∑ t∈ blip S a₀ r, ∑ i∈strum x s t.val j,F i)+∑ i∈rush x a₀ s j, F i:= by rw [rush_eq,← sum_biUnion (seed_B x s a₀ h),← seed_r, Finset.sum_add_sum_compl]
lemma pulse_g (j:ℕ)(s:Signed)(h:j*radiusB x≤ r)(p:BoltP a₀ ξ V₀ x)(he:spanO T x)(hq:spanC T x)(hv:taxM x ≤ j*radiusB x)(H:F'.threshold=fiery G x S.patch.L)(hk:W.threshold=temp x)(hp:0<fiery G x S.patch.L): let B:=fence T x M q d l β s
 (∑ i:Dill S,B i)+(∑ i,T₂ s i)=(∑ t∈blip S a₀ r, ((∑ i∈ tie (whim x j t.val s),B i)+ ∑ i∈lyn x s t.val j,T₂ s i)) + ∑ i∈rush x a₀ s j,dense T x q d l β s i M:=by
 intro B; let f:= bend T x M q d l β F' W s; have hS:= size_p x M j s h f; rw [show ((∑ i,_) + _) = (∑ i,f i) from ?_,hS]; swap
 · change _= ∑ i:Dill S⊕ _,Sum.elim B (T₂ s) i; simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
 simp_rw [strum_eq,sum_disjSum]; refine congrArg₂ (·+·) ?_ (sum_congr rfl fun i t=>bend_eq T x M q d l β F' W s i t p he hq hv H hk hp); rfl
private lemma along_i {α:Type}(P:Finset α) (L:α→ Signed→ℝ) : -β*averaged (fun s=>∑ i∈P,L i s)=∑ i∈ P,-β*averaged (L i):=by unfold averaged; simp_rw [mul_sum]; rw [sum_comm]
lemma banz(j:ℕ)(h:j*radiusB x≤ r)(p:BoltP a₀ ξ V₀ x)(he:spanO T x)(hq:spanC T x)(hv:taxM x ≤ j*radiusB x)(H:F'.threshold=fiery G x S.patch.L)(hk:W.threshold=temp x)(hp:0<fiery G x S.patch.L)(pβ:0<β)(ht:AnalyticBridge.SectorAffine.Offset.f0 T x a₀ m₀ Q₀ V₀ q d Y₀=Rows.source T x V₀ Q₀ (shots S x) a₀ m₀ q d Y₀)(hx:K'.Funds S T): let g(s:Signed)(i:Along S):= dense T x q d l β s i; let fT(Z:Signed→Affine.Window S):= embH T a₀ m₀ V₀ Q₀ q β d x Y₀ l Z₀ Z; let F(s:Signed):= rush x a₀ s j
 fT (fun _=>Appel.globe S)+ -β*averaged (fun s=>∑ i,T₂ s i)+adjust T x q d l β M=
 (∑ i∈blip S a₀ r,(fT (whim x j i.val)+ keyU T x M q d l β F' W j i.val))+ (-β*averaged (fun s=>∑ i∈F s,g s i (rough M 0))+-β*averaged (fun s=>∑ i∈F s,shotB (g s i) M)+∑ e:Bond f,opus T x q d l β j e M) :=by -- tune f'
 intro g Q Z; unfold g Z; rw [← massP,←add_assoc]; congr 1
 unfold Q; rw [← pond T x M q d l β (fun _=> _) pβ ht hx]; simp_rw [usus]; rw [←mul_add,←av_add]
 simp_rw [pulse_g T x M q d l β F' W j _ h p he hq hv H hk hp]; rw [av_add,mul_add]; congr 1
 rw [along_i]; refine sum_congr rfl fun i _=>?_ ; rw [av_add,mul_add, pond T x M q d l β (whim x j i.val) pβ ht hx]; rfl
end
end YM.CF.Reine
