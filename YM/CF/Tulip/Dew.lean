import YM.CF.Tulip.Guard
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {ι:Type*}{f:WG ι} {N:Side} {a r e:ℝ}
lemma allsum {I:Type*}(s:Finset I)(f:I→WG ι)(p:∀ i∈s,Lively (f i)): Lively (fun i N x=>∑ j∈s, f j i N x):=by
  classical
  induction s using Finset.induction_on with
  | empty=> simp only [Finset.sum_empty]; exact Lively.zero
  | @insert a s l ih=> simp only [Finset.sum_insert l]; exact (p a (Finset.mem_insert_self ..)).add (ih fun i h=>p i (Finset.mem_insert_of_mem h))
lemma landscape {A:Chin N→Op (Single N)}(p:Solo a r A e)(h:0<a)(hp:0<e)(x y : Chin N)(hx:x∈Openc _ e)(hy:y∈Openc _ e):
   ‖A x-A y‖ ≤ (r * (4/a))*(‖x-y‖/e):=by
  let V:Openc (More N) e:=⟨x,hx⟩; let W:Openc (More N) e:=⟨y,hy⟩
  obtain ⟨F,C,p,l,q⟩:=p
  let T:=4/a*(‖x-y‖/e); have ht:0≤T:=by unfold T; positivity
  have he(S:Seal (Site (More N))): (forum N e).eval S V W≤rent a S*T:=by
    change fare S x y/ _≤ _; rw [abs_of_pos hp]; unfold fare
    have hh: ((leaks S).card:ℝ) ≤ S.card*4:=by
      have he:(leaks S).card≤(S ×ˢ (Finset.univ: Finset Axis)).card:=card_le_card fun i hi=> mem_product.mpr ⟨(mem_filter.mp hi).2.1,mem_univ _⟩
      simp [Axis] at he; exact_mod_cast he
    calc
      _ ≤ (∑ _i∈leaks S, ‖x-y‖)/e:=by gcongr; exact norm_le_pi_norm (x-y) _
      _ ≤ (↑S.card*4)* (‖x-y‖/e):=by rw [sum_const,nsmul_eq_mul,mul_div_assoc]; gcongr
      _ ≤ _:=by
        unfold T; rw [←mul_assoc]; apply mul_le_mul_of_nonneg_right _ (by positivity); unfold rent; rw [← mul_div_assoc,le_div_iff₀ h]; linarith [Real.add_one_le_exp (a*S.card)]
  let U:=fun i j=> saleM a C i j*T
  have hr:=l.posP
  rw [mul_assoc]
  refine Branch.schur U (A x-A y) _ (by change 0≤r*T; positivity) ?_ (fun i=>by unfold U; rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (l.rows i) ht) (fun j=>by unfold U; rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (l.cols j) ht)
  intro i j
  rw [Matrix.sub_apply, show A x=_ from q V, show A y=_ from q W,Matrix.sum_apply, Matrix.sum_apply, ← Finset.sum_sub_distrib]; apply (norm_sum_le ..).trans
  unfold U saleM; rw [sum_mul]; refine sum_le_sum fun S _=> ((p S).expo i j|>.variation V W).trans ((mul_le_mul_of_nonneg_left (he _) ((p S).nonn i j)).trans_eq (by ring))
def unityP (N:Side)(U:Op (Model N)) : Op (Single N):=U.submatrix (helix N) (helix N)
def love (N:Side): Op (Model N) ≃⋆ₐ[ℂ] Op (Single N) := { Matrix.reindexAlgEquiv ℂ ℂ (helix N).symm with map_star' _:=rfl, map_smul' a b:=rfl }
lemma loveAt (A : Op (Model N)): love N A=unityP N A:=rfl
lemma love_money (A: Op (Model N)) : ‖love N A‖=‖A‖:=by exact StarAlgEquiv.norm_map .. -- inspect
open scoped ComplexOrder
lemma pushed {A:Op (Model N)}(h:Safe A): Safe (love N A):=by
  have he : IsSelfAdjoint (love N A):=by rw [isSelfAdjoint_iff,←map_star,h.self.star_eq]
  have hx : Monotone (love N) := fun A B h=> by rw [← sub_nonneg] at *; rw [←map_sub]; exact ((Matrix.nonneg_iff_posSemidef.mp h).submatrix (helix N)).nonneg
  refine ⟨he, (love_money ..).trans_le h.bound,?_⟩
  have ht:=hx h.margin; rw [map_pow,show love N ((1/2:ℝ) • 1)=(1/2:ℝ) • (love N 1) from rfl,map_one] at ht; exact ht
end YM.CF.Tulip
