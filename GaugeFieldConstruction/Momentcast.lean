import GaugeFieldConstruction.Eccolo
import YM.CF.Hove.Bay
/-! # Directional moments to order two. Do not require alias differentiability at phase outside open.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
section
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
-- second derivative =2 times polynomial cost. triangular truncated products. polarization for fixed finite E.
structure TierS (f: ℝ→E)(x y z:E):Prop where
 cost: ContDiffAt ℝ ((2:ℕ):WithTop ℕ∞) f 0
 post : f 0=x
 fone : deriv f 0=y
 gOne : deriv (deriv f) 0= z -- pure derivative, not /2
variable {f g:ℝ→ E}{x y z a b d:E}
lemma TierS.equal (h:TierS f x y z)(j:f=ᶠ[𝓝 0] g): TierS g x y z:=⟨h.cost.congr_of_eventuallyEq j.symm, j.self_of_nhds.symm.trans h.post,j.deriv_eq.symm.trans h.fone, j.deriv.deriv_eq.symm.trans h.gOne⟩
lemma TierS.diff (h:TierS f x y z): HasDerivAt f y 0:= h.fone ▸ (h.cost.differentiableAt (by norm_num)).hasDerivAt
lemma TierS.diff₂ (h:TierS f x y z): HasDerivAt (deriv f) z 0:= (h.gOne ▸ ((show ContDiffAt ℝ 1 (deriv f) 0 from ((h.cost.fderiv_right (m:=1) (by norm_num)).clm_apply contDiffAt_const)).differentiableAt (by norm_num)).hasDerivAt)
lemma TierS.const (x:E):TierS (fun _=>x) x 0 0:=⟨contDiffAt_const,rfl,by simp,by simp⟩
lemma TierS.add (l:TierS f x y z)(k:TierS g a b d): TierS (f+g) (x+a) (y+b) (z+d):=by
 have hi: deriv (f+g)=ᶠ[𝓝 0] deriv f+deriv g:=by filter_upwards [l.cost.eventually (by norm_num), k.cost.eventually (by norm_num)] with x h k; exact deriv_add (h.differentiableAt (by norm_num)) (k.differentiableAt (by norm_num)) -- tune
 refine ⟨l.cost.add k.cost, congrArg₂ _ l.post k.post,(l.diff.add k.diff).deriv,hi.deriv_eq.trans ((l.diff₂.add k.diff₂).deriv)⟩
lemma TierS.map {F:Type*}[NormedAddCommGroup F][NormedSpace ℝ F] (l:TierS f x y z) (L:E→L[ℝ]F) : TierS (L ∘ f) (L x) (L y) (L z):=by
 have hi: deriv (L∘f) =ᶠ[𝓝 0] L∘deriv f:= by filter_upwards [l.cost.eventually (by norm_num)] with x h; exact (L.hasFDerivAt.comp_hasDerivAt _ (h.differentiableAt (by norm_num)).hasDerivAt).deriv
 exact ⟨L.contDiff.contDiffAt.comp _ l.cost,congrArg L l.post,(L.hasFDerivAt.comp_hasDerivAt _ l.diff).deriv,hi.deriv_eq.trans (L.hasFDerivAt.comp_hasDerivAt 0 l.diff₂).deriv ⟩
lemma TierS.sum {α:Type*}(F:α→ ℝ→E)(x y z:α→E)(K:Finset α)(l:∀ i∈K,TierS (F i) (x i) (y i) (z i)):TierS (∑ i∈K,F i) (∑ i∈K,x i) (∑ i∈K,y i) (∑ i∈K,z i):=by
 classical
 induction K using Finset.induction_on with
 | empty=> simp only [sum_empty]; exact TierS.const _
 | @insert i K p ih=> simp_rw [sum_insert p]; exact (l _ (mem_insert_self ..)).add (ih (fun i v=>l i (mem_insert_of_mem v)))
lemma TierS.unique (l:TierS f x y z)(u:TierS g a b d)(h:f=ᶠ[𝓝 0]g): x=a ∧ y=b ∧ z=d:=by let t:=l.equal h; exact ⟨t.post.symm.trans u.post,t.fone.symm.trans u.fone,t.gOne.symm.trans u.gOne⟩
end
section
variable {E:Type*}[NormedRing E][NormedAlgebra ℝ E]
lemma TierS.mul {f g:ℝ→E}{x y z u v w:E} (e:TierS f x y z)(k:TierS g u v w): TierS (f*g) (x*u) (y*u+x*v) ((z*u+x*w)+(y*v+y*v)):=by
 constructor
 · exact e.cost.mul k.cost
 · exact congrArg₂ _ e.post k.post
 · -- derivative noncomm
   rw [(e.diff.mul k.diff).deriv,e.post,k.post] -- tune
 let P:(ℝ→E):=deriv f*g+f*deriv g; have hp: deriv (f*g)=ᶠ[𝓝 0] P:=by
    filter_upwards [e.cost.eventually (by norm_num), k.cost.eventually (by norm_num)] with i u v; exact ((u.differentiableAt (by norm_num)).hasDerivAt.mul (v.differentiableAt (by norm_num)).hasDerivAt).deriv
 rw [hp.deriv_eq, show deriv P 0=_ from ((e.diff₂.mul k.diff).add (e.diff.mul k.diff₂)).deriv]; rw [e.fone,e.post,k.fone,k.post]; abel
end
section
variable {E F:Type*}[NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F]
lemma TierS.clm {f:ℝ→(E→L[ℝ]F)}{x y z:E→L[ℝ] F}{g:ℝ→E}{a b d:E} (h:TierS f x y z)(p:TierS g a b d): TierS (fun i=> f i (g i)) (x a) (y a+x b) ((z a+x d)+(y b+y b)):=by
 refine ⟨h.cost.clm_apply p.cost, by rw [h.post,p.post],(h.diff.clm_apply p.diff).deriv.trans ?_,?_⟩
 · rw [h.post,p.post]
 let H:ℝ→F:= (fun x=>deriv f x (g x))+(fun x=> f x (deriv g x)); have he: deriv (fun i=>f i (g i))=ᶠ[𝓝 0] H:=by filter_upwards [h.cost.eventually (by norm_num),p.cost.eventually (by norm_num)] with x h k; exact ((h.differentiableAt (by norm_num)).hasDerivAt.clm_apply (k.differentiableAt (by norm_num)).hasDerivAt).deriv
 rw [he.deriv_eq, show deriv H 0=_ from ((h.diff₂.clm_apply p.diff).add (h.diff.clm_apply p.diff₂)).deriv, h.post,h.fone,p.post,p.fone]; abel
end
end Lenten
end YM.CF.TableF
end
