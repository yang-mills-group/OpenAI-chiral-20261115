import GaugeFieldConstruction.Pliant
import GaugeFieldConstruction.Ethos
set_option autoImplicit false
set_option maxHeartbeats 220000
set_option maxRecDepth 5700
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
set_option linter.style.longLine false
open Function Filter Set MeasureTheory
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
namespace Spine
open Fock Analysis SlabMark MeshClock Vacancy Tapestry Etch
open Germ Alliance Lattice Py.Rate Py.Rate.LocalLimit Preparation Journey Satin Heat
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
noncomputable section
open Fock
variable {P:Spine}{j:Axis}{V G:ℕ→Buffered.Family P.calibration}{f g:P.Test}{S T:Finset Cover}
/- exact thinnings & leaf bookkeeping. -/
lemma Coheresγ (P:Spine)(a:ℕ→ℕ)(h:StrictMono a): Coherent (i:=P.period) (k:=P.cutoff) (E:=P.E) P.run P.large P.projection.refine (P.projection.rows∘ a) (P.projection.columns∘ a):=by
 let t:=P.history
 refine ⟨t.circuit, t.growsA.comp h,t.growsB.comp h,fun k=> t.gate (a k),fun s=>h.tendsto_atTop.eventually (t.finance s),?_⟩
 intro s S; obtain ⟨c,u,X⟩:=t.implements s S; exact ⟨c,u,fun e he=> h.tendsto_atTop.eventually (X e he)⟩
abbrev LongQueue (P:Spine)(S:Finset Cover)(F:ℕ→Buffered.Family P.calibration)(f:P.Test):Prop:=BQueue S F f.val
lemma LongQueue.mono {s:ℕ→ℕ}(h:Tendsto s atTop atTop)(u:P.LongQueue S V f):P.LongQueue S (V∘s) f := ⟨fun i=> u.whereTo _,u.landing, (by obtain ⟨A,a,p,q⟩:=u.bdd; exact ⟨A,a,p,h.eventually q⟩), fun k hk=>h.eventually (u.saved k hk)⟩
lemma LongQueue.bayΛ (u:P.LongQueue S V f): f∈bay P.calibration S true:= (Tapestry.locates ..).mpr u.landing
lemma LongQueue.attain (f:P.Test)(p:f∈bay P.calibration S true):P.LongQueue S (fun _=>f.val) f :=by
 let u:= (Tapestry.locates ..).mp p; obtain ⟨c,t⟩:= Journey.valuation P.run P.large u; let d:=max 1 c; have hx:0<d:=zero_lt_one.trans_le (le_max_left ..); exact BQueue.stay u hx (fun i x=> (t i x).trans (le_max_right ..))
lemma LongQueue.ellone (P:Spine)(S:Finset Cover):P.LongQueue S (fun _=>1) 1:=LongQueue.attain (P:=P) 1 (one_mem (bay P.calibration S true))
lemma LongQueue.plus (p:P.LongQueue S V f)(q:P.LongQueue S G g):P.LongQueue S (fun i=>V i+G i) (f+g):=by
 obtain ⟨A,u,t⟩:=p.bdd; obtain ⟨B,v,k⟩:=q.bdd; refine ⟨fun i=>(p.whereTo i).add (q.whereTo i),p.landing.add q.landing,⟨A+B,add_pos u v,pay_add t.1 k.1,(t.2.and k.2).mono fun i h=>pay_add h.1 h.2⟩,fun e w=>?_⟩
 filter_upwards [p.saved _ (half_pos w),q.saved _ (half_pos w)] with i a b; have h:= pay_add a b; change pay _ _; rwa [add_halves, show _ = _ from (show V i-f.val+(G i-g.val)=V i+G i-(f.val+g.val) by abel)] at h
lemma LongQueue.step (p:P.LongQueue S V f){a:ℕ → ℂ}{A:ℂ}(h:Tendsto a atTop (𝓝 A)):P.LongQueue S (fun i=> a i • V i) (A•f):=by
 obtain ⟨B,v,t⟩:=p.bdd; let C:=‖A‖+1; have hx: ‖A‖ ≤ C:=le_add_of_nonneg_right zero_le_one; have hp:0<C:=add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
 have he:∀ᶠ i in atTop,‖a i‖≤ C:=h.norm.eventually (ge_mem_nhds (lt_add_of_pos_right _ zero_lt_one))
 refine ⟨fun i=> InTest.smul _ (p.whereTo i),InTest.smul _ p.landing,⟨C*B,mul_pos hp v,fun i k=> ((pay_scale t.1 A) i k).trans (mul_le_mul_of_nonneg_right hx v.le),(he.and t.2).mono fun i ⟨u,b⟩ m n=> ((pay_scale b (a i)) m n).trans (mul_le_mul_of_nonneg_right u v.le)⟩,fun e w=>?_⟩
 let d:=e/(C+B); have hd:0<d:=div_pos w (by positivity)
 filter_upwards [p.saved d hd, he, Metric.tendsto_nhds.mp h d hd] with i u b g
 have hg:A • f.val = (A•f).val:=rfl
 have ht:= pay_add (pay_scale u (a i)) (pay_scale t.1 (a i -A))
 rw [show _+(a i-A)• f.val=a i • V i-(A•f).val from (by rw [smul_sub,sub_smul,←hg]; abel)] at ht
 exact fun m n=> (ht m n).trans ((add_le_add (mul_le_mul_of_nonneg_right b hd.le) (mul_le_mul_of_nonneg_right ((le_of_lt (show ‖a i - A‖<d from (dist_eq_norm (a i) A) ▸ g))) v.le)).trans_eq (by linarith only [show d*(C+B)=e from div_mul_cancel₀ _ (by positivity)]))
lemma LongQueue.minus (p:P.LongQueue S V f)(q:P.LongQueue S G g):P.LongQueue S (fun i=>V i-G i) (f-g):=by
 simpa [sub_eq_add_neg] using p.plus (q.step (A:=-1) tendsto_const_nhds)
lemma LongQueue.books {a:ℕ → ℂ}{A:ℂ}(p:P.LongQueue S V f)(z:ℂ)(g:Tendsto a atTop (𝓝 A)) : P.LongQueue S (fun i=> 1+z • (V i-(a i) •1)) (1+ z • (f-A •1)):= (ellone P S).plus ((p.minus ((ellone P S).step g)).step tendsto_const_nhds)
end
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
