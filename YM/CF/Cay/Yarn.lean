import YM.CF.Cay.Pique
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Cay
open Slate Forge Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.Uniform (curve Slope tint partSpace meetVar)
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
variable {G:Gauge}{c f:Side}{S:StepData c f}{r v l n:ℕ}{w x β d:ℝ}{q:Chi}{T:Tube G S}{F:Forest S.ratio}{E A:Type}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup A][NormedSpace ℝ A]
local notation "G"=>SU.group
variable {K:Teller SU.group}{T:Tube SU.group S}
local notation "ζ"=>Monk G S
open Slate.Far
open Matrix
variable {A:Monk SU.group S}{X: Support c}
section
variable(T:Tube G S)(x:ℝ)(q:Chi)(d:ℝ)(l:ℕ)(β:ℝ)
def dense (s:Signed)(i:Along S)(M: Monk G S):=stars T x M q d l β s i
def rush(A:Stores S)(s:Signed)(r:ℕ):Finset (Along S) := univ.filter fun i=> herald S s i∉ A.dome (r*radiusB x)
def opus(j:ℕ)(e:Bond f)(M:ζ):= -β*averaged (fun s=>∑ i∈rush x M.key s j,spring (dense T x q d l β s i) e M)+spring (adjust T x q d l β) e M
abbrev coverB(l j:ℕ):=2*(l+76)+j
lemma opus_p (j:ℕ)(e:Bond f)(p:Beat.shadows (o:=S.ratio.parent e.1) X (coverB l j*radiusB x))(h:Ready T x)(hp:1000 ≤ radiusB x)(hv:0<β): Virt S (opus T x q d l β j e) X:=by
 intro M N H; let B(t:ζ)(s:Signed):= ∑ i∈ rush x t.key s j,spring (dense T x q d l β s i) e t
 have ht: Beat.shadows (o:=S.ratio.parent e.1) X (2*horn x l):= aroundBk X p (by unfold coverB horn; rw [←mul_assoc,Nat.add_mul,separation_self,zero_add]; omega)
 have hh:B M=B N:=by
    funext s; unfold B rush; rw [sum_filter,sum_filter]; refine sum_congr rfl fun i _=> ?_
    let U:Site c:=herald S s i; let P:=S.ratio.parent e.1
    have hz:Virt S (dense T x q d l β s i) (halo (horn x l) {U}):= calm s i h hp (Subset.refl _)
    by_cases he:horn x l< separation U P
    · rw [off hz e (points_p e U he),off hz e (points_p e U he)]; simp
    have hv':separation P U+j*radiusB x ≤ coverB l j*radiusB x:=by rw [separation_comm]; unfold coverB; rw [Nat.add_mul,mul_assoc]; unfold horn at he; omega
    have hw:(herald S s i∈M.key.dome (j*radiusB x)) ↔ herald S s i∈N.key.dome (j*radiusB x):=⟨fun u=>H.same p u hv',fun u=>H.sym.same p u hv'⟩
    simp only [hw]; split_ifs; rfl; exact curt _ hz ht H
 change -β*averaged (B M)+_= _; rw [hh]; exact congrArg (-β*averaged (B N)+·) (cog (T:=T) (q:=q) (d:=d) e ht h hp hv H)
lemma strut_w (k:ℕ)(e:Bond f)(M:ζ)(hp:M.key=bareStores S)(h:0<β)(v:∀ s i,ContDiffAt ℝ (2:ℕ) (dense T x q d l β s i∘ rough M) 0): opus T x q d l β k e M= spring (fun M=>aster T x M q d l β) e M :=by
 let P(z):=potH T x (rough M z) q d l β; let Q:= adjust T x q d l β ∘ rough M; let F(s:Signed)(i:Along S)(z:Directions G f):=dense T x q d l β s i (rough M z); let U(t:Signed)(z):=∑ i:Along S,F t i z; let a:=arrow e M.z; let Z(s:Signed):=∑ i∈rush x M.key s k,spring (dense T x q d l β s i) e M
 have he(s:Signed):rush x M.key s k=Finset.univ:=by rw [hp]; simp [rush,bareStores,Stores.dome,Stores.place,halo_spec]
 have hQ:ContDiffAt ℝ (2:ℕ) Q 0:= (rivet _ _ _ _ _ _ h M).contDiffAt.of_le le_top
 let C:= (Fintype.card Signed :ℝ)⁻¹
 have ht(s:Signed)(i):ContDiffAt ℝ (2:ℕ) (F s i) 0:= v s i; have hz(s):ContDiffAt ℝ (2:ℕ) (U s) 0:= ContDiffAt.sum fun i _=> ht s i
 have hg:ContDiffAt ℝ (2:ℕ) (fun z=> C*(∑ s:Signed,U s z)) 0:= contDiffAt_const.mul (ContDiffAt.sum fun s _=>hz s); have hh: ContDiffAt ℝ (2:ℕ) P 0:= (contDiffAt_const (c:=-β)).mul hg
 change -β*averaged Z+strut Q a M.z=strut (fun i=>aster T x (rough M i) q d l β) a M.z; rw [show (fun i=>aster T x (rough M i) q d l β)=fun i=>P i+Q i from funext fun i=> add_assoc ..,strut_add P Q a M.z hh hQ]
 congr 1; rw [show P= (fun i=> -β*(C*(∑ s:Signed,U s i))) from rfl,strut_const (fun z=>C*_) _ _ hg,strut_const (fun z=>∑ s:Signed,U s z) _ _ (ContDiffAt.sum fun s _=>hz s),strut_sum _ (fun s=>U s) _ _ (fun i _=>hz i)]; unfold U; simp_rw [strut_sum _ (F _) _ _ fun i _=>ht _ i]; unfold averaged Z; simp_rw [he]; rfl
end
end YM.CF.Cay
