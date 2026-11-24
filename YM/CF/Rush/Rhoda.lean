import YM.CF.Rush.Rill
set_option autoImplicit false
noncomputable section
namespace YM.CF.Rush
open Fir Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N L M:Side}
def tJustice(L:Side):= stack L fun _=>spinJ
lemma coolT (p:Momentum): trident L p*tJustice L=tJustice L*trident L p:=by
  ext ⟨i,a⟩ ⟨k,b⟩; unfold tJustice; simp only [Matrix.mul_apply,trident,s_app,St,Fintype.sum_prod_type,aliasBlock,Matrix.of_apply,s_app,Matrix.smul_apply,smul_eq_mul]; simp [ite_mul,mul_ite,mul_comm]
lemma jewel (j:ℕ)(L:Side)(p:Momentum)(hp:physical p): Commute (tJustice L) (brix j L p):= by rw [brix_scale j L hp]; apply Commute.add_right; exact Commute.mul_right (coolT p).symm (stackA ..); exact Commute.sub_right (Commute.one_right _) (show tJustice L*peb L=peb L*tJustice L by simp only [tJustice,peb,mul_spike,spike_mul,one_mul,mul_one])
lemma posed (j:ℕ)(ho:Odd L.val): cc (plates N (brix j L))=plates N (brix j L) := by
  apply shape; intro k; obtain ⟨w,h⟩:= dollar k; change mel (backN k)=_ at h
  have hP := base_subset_realCube zone_pos (mel_h k); rw [h,verifies _ _ (realCube_neg hP) w (h ▸ base_subset_realCube zone_pos (mel_h (backN k))),bonK j L ho _ hP.1]
lemma bT (j:ℕ):Commute (plates N fun _=>tJustice L) (plates N (brix j L)):=by unfold Commute SemiconjBy; rw [pilesP,pilesP]; exact pilesE _ _ fun p hp _=>jewel j L p hp.1
lemma pT(j:ℕ)(u: Bool)(ho:Odd M.val): plates N (bent u j M)*plates N (fun _=>spinJ)=plates N (fun _=>spinJ)*cc (plates N (bent u j M)):=by
  let H(p):=cc (bent u j M (-p))
  have hh: cc (plates N (bent u j M))=plates N H:=by
    apply shape; intro k; obtain ⟨l,h⟩:= dollar k; change mel (backN k)= _ at h
    have hp:=base_subset_realCube zone_pos (mel_h (backN k)); unfold H; rw [h,bent,bent,bar_overlap _ _ (realCube_neg (base_subset_realCube zone_pos (mel_h k))) l (h ▸ hp)] -- defeq
  rw [hh,pilesP,pilesP]; exact pilesE _ _ fun p hp hx=> barR j M u ho hp hx
end YM.CF.Rush
