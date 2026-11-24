import YM.SU5.Relativistic.IrreducCAR

/-! # Pure Tensor can read a unique block (up to phase) from its disjoint products. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
open Fock Reflect Function Filter MeasureTheory NormedSpace Finset Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra

variable {I : Type*} [Fintype I] [LinearOrder I]
local notation "W" => FC I

noncomputable def Shed (S:Finset I)(a:Bool):Submodule ℂ (FC I) where
 carrier:= {A|Sector S a A}
 add_mem' := fun x y=>Sector.add x y
 zero_mem':= Sector.zero _
 smul_mem':=fun z _ h=> h.scale z
lemma paidCAR {A:W} (S:Finset I)(b:Bool) : A∈ Shed S b ↔ Sector S b A:=Iff.rfl

lemma leverage {S T:Finset I} (h:Disjoint S T)(a b:Bool) :∃ c:ℝ,0<c∧ ∀ (A B:FC I),Sector S a A → Sector T b B → c*‖A‖*‖B‖≤‖A*B‖:=by
 let V : Set W := (Shed S a : Set W) ∩ sphere (0:W) 1
 let X : Set W := (Shed T b:Set W) ∩ sphere (0:W) 1
 let L:= Set.prod V X
 have he : IsCompact L:= (IsCompact.inter_left (isCompact_sphere ..) ((Shed S a).closed_of_finiteDimensional)).prod ((isCompact_sphere ..).inter_left ((Shed T b).closed_of_finiteDimensional))
 let F(z:W × W):= ‖z.1*z.2‖
 suffices hh:∃ c:ℝ,0<c∧ ∀ x∈ L,c≤ F x by
    obtain ⟨c,t,x⟩:=hh; refine ⟨c,t,?_⟩
    intro A B u v; by_cases p:A=0; · simp [p]
    by_cases q:B=0; · simp [q]
    have hp:= norm_pos_iff.mpr p; have hq:=norm_pos_iff.mpr q
    let Y(D:W):= (‖D‖⁻¹:ℂ) • D
    have hg (D:W) (t:0<‖D‖) : Y D∈ sphere (0:W) 1:=by rw [mem_sphere_zero_iff_norm]; unfold Y; rw [norm_smul]; simp [t.ne']
    have hv:=(x (Y A,Y B) ⟨⟨u.scale _,hg A hp⟩,v.scale _,hg B hq⟩)
    change c ≤ ‖Y A*Y B‖ at hv
    unfold Y at hv; rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, norm_smul,norm_smul] at hv; push_cast at hv
    simp only [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp,abs_of_pos hq] at hv
    field_simp at hv; linarith
 by_cases p:L.Nonempty
 · obtain ⟨x,hx,f⟩:= he.exists_isMinOn p (continuous_norm.comp (continuous_fst.mul continuous_snd)).continuousOn -- elaboration
   have hu:= mem_sphere_zero_iff_norm.mp (show x.1∈sphere 0 1 from hx.1.2); have hv:= mem_sphere_zero_iff_norm.mp hx.2.2
   exact ⟨F x,norm_pos_iff.mpr (splitNK h hx.1.1 hx.2.1 (norm_pos_iff.mp (by rw [hu]; norm_num)) (norm_pos_iff.mp (by rw [hv]; norm_num))),fun _ hh=> f hh⟩
 exact ⟨1,zero_lt_one,fun x h=>False.elim (p ⟨x,h⟩)⟩

lemma sector_sub {S:Finset I}{a:Bool}{A B:W}(h:Sector S a A)(q:Sector S a B):Sector S a (A-B):= (Shed S a).sub_mem h q
end YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.FermionSlab.leverage
