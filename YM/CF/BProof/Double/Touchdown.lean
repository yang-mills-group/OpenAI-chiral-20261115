import YM.CF.BProof.Double.Touch
import YM.CF.BProof.Wick.Bits
/-! annihilator argument for actual Wick conditioning. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Double
open Function Filter Fock Finset Branch Align Wick
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][LinearOrder I] [Nonempty I] {p q: Finset I} {v:Ket I}
lemma cabin_up(q:Finset I)(h: acts (cutM p) v=v): create v * cabin p q=0:=by
 rw [create_def,sum_mul]; apply sum_eq_zero; intro i _; rw [Algebra.smul_mul_assoc]; by_cases t:i∈p; rw [stopCap p q i t,smul_zero]; rw [show v.ofLp i=0 from (by nth_rw 1 [←h]; rw [cut_apply,if_neg t]), zero_smul]
lemma cabin_down(p:Finset I)(h:acts (cutM q) v=v): remove v*cabin p q=0:=by
 rw [remove_def,sum_mul]; apply sum_eq_zero; intro i _; rw [Algebra.smul_mul_assoc]; by_cases t:i∈q; rw [stopEmpty p q i t,smul_zero]; rw [show v.ofLp i=0 from (by nth_rw 1 [←h]; rw [cut_apply,if_neg t]),star_zero,zero_smul]
lemma roomU (h:Disjoint p q): cutM (p∪q)ᶜ=space (cutM p) (cutM q):=by
 rw [dim_cut,space]; congr 1; apply op_columns; intro i; rw [act_add,cut_basis,cut_basis,cut_basis]; by_cases p:i∈p; have hz:i ∉ q:=disjoint_left.mp h p; simp [p,hz]; by_cases t:i∈q <;> simp [t,p]
lemma moved (h:acts (cutM p) v=v) : acts (cutM p) (pend v)=pend v := by nth_rw 1 [←cut_real p]; rw [←pend_move,h]
variable {A C:Op I}{c r:ℝ} (x:Book I)(C':Double.Deck A (cutM p) (cutM q) C c r)
def pressB (p q: Finset I)(C:Op I): Wave I:= acts (cabin p q) (pairWave C)
include C'
theorem touchdown (e:Disjoint p q)(h:Live x (cutM p) (cutM q) C) : acts (star (printT x)) (pressB p q C)=0:=by -- include
 let P:=cutM p; let Q:=cutM q; let L:=space P Q; let S:= (p∪q)ᶜ; let v:=rows x; let w:=cols x; obtain ⟨g,d,h⟩:= h; let b:= C'.cbP; let D:=acts L v; let T:=acts L w; let K:=join D T
 let U:=join (acts Q v) 0; let W:=join 0 (acts P w); let Z:=pressB p q C; rw [show x=U+W+K from ?_]; swap
 · apply book_ext; rw [add_rows,add_rows]; change v=_+_; rw [row_join (acts Q v) 0,row_join (0:Ket I),row_join D]; unfold D L space; rw [act_sub,act_add, g,act_one]; abel -- tune let unfold
   rw [add_cols,add_cols]; change w=_+_; rw [col_join (acts Q v),col_join (0:Ket I),col_join D]; unfold T L space; rw [act_sub,act_add,d,act_one]; abel
 have hu: acts (star (printT U)) Z=0:=by
    have hi: star (printT U)=remove (acts Q v):=by unfold U; rw [printed,row_join,col_join,pend_zero]; simp [remove]
    rw [hi]; unfold Z pressB; rw [←act_mul,cabin_down _ (selfApply b.q _),act_zero]
 have hv: acts (star (printT W)) Z=0:=by
    have hi: star (printT W)=create (pend (acts P w)):=by unfold W; rw [printed,row_join,col_join]; simp [remove]
    rw [hi]; unfold Z pressB; rw [← act_mul,cabin_up q (moved (p:=p) (selfApply b.p _)),act_zero]
 have hp: Sector S true (printT K):=by
    have hx:cutM S=L:=roomU e; unfold K; rw [printed, col_join, row_join]; exact (Sector.makeP D (hx ▸ (selfApply b.wall v))).add ((Sector.makeP (pend T) (moved (show acts (cutM S) T=T from hx ▸ (selfApply b.wall w)))).contr) -- direction?
 have hZ: acts (star (printT K)) Z=0:=by
    have hg: Commute (star (printT K)) (cabin p q):= by
       show _*_=_*_; simpa only [Sector.grainB,Bool.and_false,Bool.false_eq_true,ite_false,one_smul] using Sector.apart hp.contr (tagged (S:=p∪q) subset_union_left subset_union_right) disjoint_compl_left
    have he:T=acts (cc C) D:=h; unfold Z pressB; rw [←act_mul,hg.eq,act_mul,show K=_ from congrArg (join D) he,pushVector C'.safety.sym,map_zero]
 rw [map_add,map_add,star_add,star_add,act_add,act_add,hu,hv,hZ,zero_add,zero_add]
end YM.CF.BProof.Double
