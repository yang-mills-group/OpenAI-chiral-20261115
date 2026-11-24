import YM.CF.BProof.Stave.Simplex
/-! Equivalence on simplices. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Stave
open Function Filter Topology Finset Metric
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal
variable {I J:Type*}[Fintype I][DecidableEq I][Fintype J][DecidableEq J]
def octa (e:I≃J)(w:Pool I): Pool J:=fun j=> w (e.symm j)
omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
@[simp] lemma octa_oct (e:I≃J)(w:Pool I):octa e.symm (octa e w)=w:=by ext j; simp [octa]
omit [DecidableEq I] [DecidableEq J] in
lemma octa_iso(e:I≃J): Isometry (octa e):=by
  refine Isometry.of_dist_eq fun a b=>?_ ; apply le_antisymm ((dist_pi_le_iff (dist_nonneg)).mpr fun j=>dist_le_pi_dist _ _ (e.symm j))
  apply (dist_pi_le_iff (dist_nonneg)).mpr fun i=>?_ ; have hh:=dist_le_pi_dist (octa e a) (octa e b) (e i); simpa only [octa,e.symm_apply_apply] using! hh
omit [DecidableEq I] [DecidableEq J] in
@[simp] lemma supp_octa(e:I≃J)(w:Pool I): supp (octa e w)= (supp w).map e.toEmbedding:=by
 classical
 ext j; constructor; intro h; exact Finset.mem_map.mpr ⟨e.symm j,mem_supp.mpr (show octa e w j≠0 from mem_supp.mp h),e.apply_symm_apply j⟩; intro h; obtain ⟨i,p,rfl⟩:=Finset.mem_map.mp h; apply mem_supp.mpr; simpa [octa] using (mem_supp.mp p)
omit [DecidableEq I] [DecidableEq J] in
lemma octa_sim(e:I≃J){x:Pool I}{S:Finset I}(h:Sim S x): Sim (S.map e.toEmbedding) (octa e x):= ⟨fun _=> h.pos _,by rw [supp_octa]; exact map_subset_map.mpr h.box,(Equiv.sum_comp e.symm x).trans h.mass⟩
omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
@[simp] lemma octa_back(e:I≃J)(S:Finset I): (S.map e.toEmbedding).map e.symm.toEmbedding=S:=by ext; simp
end YM.CF.BProof.Mesh.Stave
