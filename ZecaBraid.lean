import ZecaDrop
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis

variable {K:Calibration}
namespace BQueue
variable {S T:Finset Cover}{F G:ℕ→Family K}{x y:Family K}
lemma reindex {κ:ℕ→ℕ}(b:BQueue S F x)(h:Tendsto κ atTop atTop): BQueue S (F ∘ κ) x:=by
 obtain ⟨t,u,⟨C,v,p,q⟩,z⟩:=b
 exact ⟨fun _=>t _,u,⟨C,v,p,h.eventually q⟩,fun _ d=>h.eventually (z _ d)⟩
lemma subtract (b:BQueue S F x)(c:BQueue T G y):
 BQueue (S∪T) (fun i=>F i-G i) (x-y):=by
 obtain ⟨t,u,⟨C,v,p,q⟩,z⟩:=b
 obtain ⟨a,r,⟨D,f,x',y'⟩,e⟩:=c
 refine ⟨fun i=>InTest.subOp ((t i).mono subset_union_left) ((a i).mono subset_union_right),
    InTest.subOp (u.mono subset_union_left) (r.mono subset_union_right),
    ⟨C+D,by positivity,pay_sub p x',(q.and y').mono fun i hv=>pay_sub hv.1 hv.2⟩,?_⟩
 intro A hA
 filter_upwards [z (A/2) (by linarith), e (A/2) (by linarith)] with i ht hg
 rw [show F i-G i-(x-y)=(F i-x)-(G i-y) from by abel, show A=(A/2+A/2) from by ring]
 exact pay_sub ht hg


lemma scale{b:ℂ}{a:ℕ→ℂ} (c:BQueue S F x)(t:Tendsto a atTop (𝓝 b)):
 BQueue S (fun i=>a i • F i) (b • x):=by
 obtain ⟨u,j,⟨C,v,p,q⟩,z⟩:=c
 let D:= ‖b‖+1
 have f:0<D:=by unfold D; positivity
 have g: ‖b‖≤D:=le_add_of_nonneg_right zero_le_one
 have h: ∀ᶠ i in atTop, ‖a i‖≤D:=(t.norm.eventually_le_const (by unfold D; linarith))
 refine ⟨fun i=>InTest.smul _ (u i),InTest.smul _ j,
    ⟨D*C,by positivity,fun k y=>(pay_scale p b k y).trans ?_,?_⟩,?_⟩
 · exact mul_le_mul_of_nonneg_right g v.le
 · filter_upwards [h,q] with i ht hg
   exact fun k y=>(pay_scale hg (a i) k y).trans (mul_le_mul_of_nonneg_right ht v.le)
 intro E e
 filter_upwards [z (E/(2*D)) (by positivity), Metric.tendsto_nhds.mp t (E/(2*C)) (by positivity), h]
    with i hx hy ht
 rw [dist_eq_norm] at hy
 rw [show a i • F i - b • x= (a i • (F i-x)) + ((a i-b) • x) by rw [smul_sub,sub_smul]; abel]
 intro k y
 refine ((pay_add (pay_scale hx (a i)) (pay_scale p (a i-b))) k y).trans ?_
 exact (add_le_add (mul_le_mul_of_nonneg_right ht (by positivity:0≤ E/(2*D))) (mul_le_mul_of_nonneg_right hy.le v.le)).trans_eq (by field_simp; ring)
end BQueue
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
lemma stayQueue{S: Finset Cover}{x:Family (tent Y H)}(h: InTest (tent Y H) true S false x):BQueue S (fun _=>x) x:=by
 obtain ⟨d,t⟩:=valuation Y H h
 have p: 0<d+1:=by have w:= Tower.pay_nonneg (F:=x) t; linarith
 exact BQueue.stay h p (fun i y=>(t i y).trans (le_add_of_nonneg_right zero_le_one))
end YM.CF.Buffered.Afterglow.Tower.SlabMark
