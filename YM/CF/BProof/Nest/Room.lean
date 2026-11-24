import YM.CF.BProof.Stave.Horn
/-! Beam rows. Unnormalized HS to book. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Nest
open Stave Function Finset Metric
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
variable {q:ℕ}
abbrev Floor (q:ℕ):= Fin q × Fin 5
def btl(c:Fin q)(A:plate (Fin 5)):plate (Floor q):= Matrix.of fun ⟨b,i⟩ j=> if c=b then A i j else 0
variable (q)
abbrev Attic:= plate (Floor q)
variable {q}
lemma bond {c a:Fin q}(A B:plate (Fin 5)): (btl c A)ᴴ * (btl a B) = if c=a then Aᴴ*B else 0:=by
 ext i j : 1; by_cases h:c=a
 · subst a; rw [if_pos rfl, Matrix.mul_apply,Fintype.sum_prod_type]; rw [sum_eq_single c (fun b _ hb=>?_) (by simp),Matrix.mul_apply]; · simp [btl]
   simp [btl,Ne.symm hb]
 rw [if_neg h,Matrix.mul_apply]; simp only [Matrix.zero_apply]; apply sum_eq_zero; rintro ⟨u,v⟩ _; by_cases e:c=u
 · subst u; simp [btl,Ne.symm h]
 simp [btl,e]
lemma beam_s (c:Fin q)(A:plate (Fin 5)): ‖btl c A‖=‖A‖:=by rw [←sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),size_R,size_R,bond,if_pos rfl]
lemma beam_roll (c:Fin q)(A:plate (Fin 5))(u:SU.E): roll (btl c A) u=btl c (roll A u):=by
 ext ⟨d,v⟩ i; by_cases g:c=d <;> simp [btl,g,roll, Matrix.mul_apply]
lemma beam_mult (c:Fin q)(A B:plate (Fin 5)): btl c (A-B)=btl c A-btl c B:=by ext ⟨d,v⟩ i <;> by_cases h:c=d<;> simp [btl,h]
@[simp] lemma btl_zero (c:Fin q): btl c 0=0:=by ext; simp [btl]
@[simp] lemma beam_dist (c:Fin q)(A B:plate (Fin 5)): dist (btl c A) (btl c B)=dist A B:=by rw [dist_eq_norm,← beam_mult,beam_s,dist_eq_norm]
lemma beam_blink(c:Fin q)(A:plate (Fin 5)):blink (btl c A)=btl c (blink A):=by
 ext ⟨d,v⟩ i; by_cases g:c=d <;> simp [btl,g]
end YM.CF.BProof.Mesh.Nest
