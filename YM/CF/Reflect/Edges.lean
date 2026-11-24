import YM.CF.Reflect.Banks

/-! All gauge variables in closed halves sharing the plane variables. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side}
abbrev RZ (m B : Side) := Edges (Domain m B)
def rayUK (m B : Side) (i : Axis) := through B (slideM m i)
def rayI (m : Side) (i : Axis) := oncue (slideM m i)
def rayE (m B : Side) (i : Axis) (x : RZ m B) : RZ m B := (if x.2=i then revX m B i x.1-step i else revX m B i x.1,x.2)
abbrev Pbar (m B : Side) i (x : Pack m B) := onPack B (slideM m i) x
lemma reflect_E (x : RZ m B) (U : Skin m B) (i) : rayUK m B i U x = if x.2=i then (U (rayE m B i x))⁻¹ else U (rayE m B i x) := by
  rcases x with ⟨x,j⟩
  change Step.read _ _ _ = _; unfold Step.read Step.used rayE
  change (if (((posDir j).rotate (glazed (slideM m i).glare)).neg)=_ then _ else _)=_
  by_cases g:j=i
  · subst i; simp only [posDir,Step.rotate,glazed,slideM,ite_true,Bool.false_xor,decide_true,Equiv.refl_apply]; rfl
  simp only [posDir,Step.rotate,glazed,slideM,g, Ne.symm g,ite_false,Bool.false_xor,decide_false,Bool.false_eq_true,Equiv.refl_apply]; rfl
lemma rev_steps (x : Site (Domain m B)) (i j : Axis) : revX m B i (x+step j)=if j=i then revX m B i x-step i else revX m B i x+step j := by
  unfold revX; rw [step_plane]; by_cases g:j=i
  · subst i; simp only [slide_glare,ite_true,sub_eq_add_neg]
  rw [if_neg (by rw [slide_glare]; exact Ne.symm g), if_neg g]
lemma rev_minus (x : Site (Domain m B)) (i) : revX m B i (x-step i)= revX m B i x + step i := by
  have he := rev_steps (x-step i) i i; rw [sub_add_cancel,if_pos rfl] at he; rw [he,sub_add_cancel]
lemma ray_back (x : RZ m B) (i) : rayE m B i (rayE m B i x)=x := by
  rcases x with ⟨x,j⟩; unfold rayE; dsimp only; by_cases h:j=i
  · subst i; simp [rev_minus]
  simp [h]
def rx (m B : Side) (i : Axis) : Equiv.Perm (RZ m B) := ⟨rayE m B i,rayE m B i,fun x=>ray_back x i,fun x=>ray_back x i⟩
lemma rpbar (x : Pack m B) (i) : Pbar m B i (Pbar m B i x)=x := by unfold Pbar; rw [trip_comp,show slideM m i*slideM m i=1 by nth_rw 1 [←slide_inv]; rw [inv_mul_cancel],pack_id]
abbrev E₁ m B i := leaks (upField m B i)
abbrev E₂ m B i := leaks (downField m B i)
lemma flipsP (x : RZ m B) (i) : rayE m B i x∈E₁ m B i ↔ x∈E₂ m B i := by
  rcases x with ⟨x,j⟩; simp only [E₁,E₂,rayE,leaks,mem_filter,mem_univ,true_and]; by_cases h:j=i
  · subst i; simp only [ite_true,sub_add_cancel]; rw [return_north,show revX m B j x-step j=revX m B j (x+step j) by rw [rev_steps,if_pos rfl],return_north,and_comm]
  rw [if_neg h,return_north, ←show revX m B i (x+step j)=revX m B i x+step j by rw [rev_steps,if_neg h],return_north]
lemma flipQ (x : RZ m B) (i) : rayE m B i x∈E₂ m B i ↔ x∈E₁ m B i := by rw [←flipsP,ray_back]
lemma all_vars (i) (x:RZ m B) : x∈E₁ m B i ∨ x∈E₂ m B i := by
  rcases x with ⟨x,j⟩; simp only [E₁,E₂,leaks,mem_filter,mem_univ,true_and,north_mem, south_mem]; by_cases h:j=i
  · subst i; simp only [Pi.add_apply,step_apply,ite_true]; exact admiss_step (N:=CSide m B) (x j)
  simp only [Pi.add_apply,step_apply, Ne.symm h,ite_false,add_zero,and_self]; exact cover_t ..
lemma sharedE (x:RZ m B) (i) (h:x∈E₁ m B i) (g:x∈E₂ m B i) : x.2≠i ∧ rayE m B i x=x := by
  rcases x with ⟨x,j⟩
  obtain ⟨hX,hY⟩ := (mem_filter.mp h).2; obtain ⟨k,X⟩ := (mem_filter.mp g).2
  have hu : j≠i := by
    intro e; subst i; change x+step j∈_ at hY X; rw [north_mem,show (x+step j : Site (Domain m B)) j=x j+1 by simp] at hY; rw [south_mem,show (x+step j : Site (Domain m B)) j=x j+1 by simp] at X; exact shared_step (suff_pos m B) _ ⟨(north_mem ..).mp hX,(south_mem ..).mp k⟩ hY X
  exact ⟨hu,by rw [rayE]; dsimp only; rw [if_neg hu,ends_share _ _ hX k]⟩

lemma stays (z : Site (Domain m B)) {i j : Axis} (h : i≠j) (a : Axis) :
    (∀ x∈ visits z (square i j),x∈upField m B a) ∨ (∀ x∈ visits z (square i j),x∈downField m B a) := by
  rw [square_corners]; simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,true_and,and_true,north_mem,south_mem,Pi.add_apply,step_apply]
  by_cases e:a=i
  · subst a; simp only [h,ite_true,ite_false,add_zero]; rcases admiss_step (N:=CSide m B) (z i) with ⟨A,B⟩|⟨A,B⟩ <;> tauto
  by_cases g:a=j
  · subst a; simp only [e,ite_false,ite_true,add_zero]; rcases admiss_step (N:=CSide m B) (z j) with ⟨A,B⟩|⟨A,B⟩ <;> tauto
  simp [g,e]; exact cover_t ..
end YM.CF.RP
