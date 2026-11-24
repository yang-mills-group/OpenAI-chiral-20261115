/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.CF.Braid.Step
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
lemma plight {f:SpanAt (t+1) (r+1)}(y:Axis→ℝ): headPress (cob r (twist (axes y)) f)=cob r (twist (axes y)) (headPress f):=by funext p a b; simp only [headPress,cob,Matrix.mulVec,dotProduct,mul_sum]; rw [sum_comm]; exact sum_congr rfl fun i _=> sum_congr rfl fun j _=>mul_left_comm ..
-- drop & zero
lemma tale{x:SheetLeg (Keys t) ξ r}(h:Board M A x): Board M A (x ∘ clipVars):=by
 intro i p; apply Pond.travel clipVars (h i p); intro v he
 have hx(y:X ℂ (t+1)): mode (clipVars y) v=mode y (extendVar v 0):=by
    simp only [mode,Fintype.sum_prod_type]; conv_rhs=> arg 1; rhs; rw [Fin.sum_univ_succ]; simp
    rfl
 simp_rw [hx]; have hh:=Pond.modes (1:ℂ) (extendVar v 0); simp only [norm_one,mul_one] at hh; refine hh.mono le_rfl (le_trans ?_ he); simp only [size,Fintype.sum_prod_type]; rw [Fin.sum_univ_succ]; simp
lemma woody{x:SheetLeg (Keys (t+1)) ξ r}(h:Board M A x): Board M A (fun p=>x (extendVar p 0)):=by
 intro i b; apply Pond.travel (fun p:X ℂ t=>extendVar p 0) (h i b); intro v he
 have hx(y): mode (extendVar y 0) v=mode y (clipVars v):=by simp only [mode,Fintype.sum_prod_type]; rw [Fin.sum_univ_succ]; simp [clipVars]
 simp_rw [hx]; have hh:=Pond.modes (1:ℂ) (clipVars v); simp only [norm_one,mul_one] at hh; apply hh.mono le_rfl; refine le_trans ?_ he; simp only [size,Fintype.sum_prod_type]; conv_rhs=> rw [Fin.sum_univ_succ]; simp
 simp [clipVars]
lemma pressP{f:SpanAt (t+1) r}(h:Board M A f)(ha:0≤ A): Board (1+M) (A*topG 0) (headPress f):=by
 intro i x
 let g : SheetLeg (Keys (t+1)) Unit 1 := fun p j _=>f p i (Fin.cons j x)
 exact cargo (stick t) (f:=g) (fun a _=>h _ _) ha vac ()
lemma press_pref {s : ℕ} (f : SheetLeg (Keys (t+1)) (Run t) r) (ha : 0 ≤ A)
    (hf : Board M A f) (hj : JetWall s f) (hW : wall (fun p => locus0 (clipVars p)) f)
    (hv : ∀ p : Corn (Keys (t+1)), p ∘ stick t = 0 → f (axes p)=0) :
    ∃ V : SpanAt (t+1) r, Board M (A*(4*(M:ℝ))) V ∧ JetWall (s-1) V ∧
      wall lineTail V ∧ ∀ p : Corn (Keys (t+1)), headPress V (axes p)=f (axes p) := by
  let T p := locus0 (clipVars p) (t:=t)
  have H : Uniforms (Run t) _ (stick t) T := var_uniform (fun p q he => by unfold T; rw [he])
  choose X HX HY HH He using fun i : TypeFace r =>
    wall_pull (stick t) ha (fun p (_ : TypeFace 0) => f p i) (fun _ b => hf i b) (by trivial) (Or.inr (fun p he => by rw [hv p he]; rfl))
      (s:=s) (fun _ b => hj i b) H (fun p _ => hW p i)
  let V (p : Phase (Keys (t+1))) (a : TypeFace r) (b : Run (t+1)) := X a p (b 0) (Fin.tail b)
  refine ⟨V,fun i x => HX i _ _,fun i x => HY i _ _,fun p i a => ?_,fun p => ?_⟩
  · change (fun b => X i (axes p) _ _)∈ _
    simpa only [Fin.tail_cons,Fin.cons_zero] using HH i p a
  funext i x
  simp only [headPress,V,Fin.tail_cons,Fin.cons_zero]
  exact congr_fun (congr_fun (He i p).symm vac) x

end YM.CF.Braid
