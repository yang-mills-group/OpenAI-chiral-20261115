import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
set_option autoImplicit false
open Function Filter Set Metric
open scoped Topology
namespace GarnetAct
variable {G : Type*} [NormedAddCommGroup G][NormedSpace ℝ G]
private lemma spiral_eq (x:Fin 8 → G) (t:∀ i:Fin 8,x (i+1)+x (i-1)=x i+x i): x 7=x 0 ∧ x 1=x 0 ∧ x 2=x 0 ∧ x 3=x 0 ∧ x 4=x 0 ∧ x 5=x 0 ∧ x 6=x 0:=by
 set y:= x 0 with ← hy; set c:= x 1-y with hv; have h(i:Fin 8): x (i+1)-x i=x i-x (i-1):= by rw [sub_eq_sub_iff_add_eq_add]; rw [t] -- order?
 have hx:x 1=y+c:=by rw [hv]; abel
 have h2 : x 2=y+ (2:ℝ) • c:=by
    have g:=h 1; rw [show (1:Fin 8)+1=2 from rfl, show (1:Fin 8)-1=0 from rfl] at g; linear_combination (norm:= module) g + (2:ℝ) • hx-hy
 have h3 : x 3=y+ (3:ℝ) • c:=by
    have g:=h 2; rw [show (2:Fin 8)+1=3 from rfl, show (2:Fin 8)-1=1 from rfl] at g; linear_combination (norm:= module) g + (2:ℝ) • h2-hx
 have h4 : x 4=y+ (4:ℝ) • c:=by
    have g:=h 3; rw [show (3:Fin 8)+1=4 from rfl, show (3:Fin 8)-1=2 from rfl] at g; linear_combination (norm:= module) g + (2:ℝ) • h3-h2
 have h5 : x 5=y+ (5:ℝ) • c:=by
    have g:=h 4; rw [show (4:Fin 8)+1=5 from rfl, show (4:Fin 8)-1=3 from rfl] at g; linear_combination (norm:= module) g + (2:ℝ) • h4-h3
 have h6 : x 6=y+ (6:ℝ) • c:=by
    have g:=h 5; rw [show (5:Fin 8)+1=6 from rfl, show (5:Fin 8)-1=4 from rfl] at g; linear_combination (norm:= module) g + (2:ℝ) • h5-h4
 have h7 : x 7=y+ (7:ℝ) • c:=by
    have g:=h 6; rw [show (6:Fin 8)+1=7 from rfl, show (6:Fin 8)-1=5 from rfl] at g; linear_combination (norm:= module) g + (2:ℝ) • h6-h5
 have h8 : x 0=y+ (8:ℝ) • c:=by
    have g:=h 7; rw [show (7:Fin 8)+1=0 from rfl, show (7:Fin 8)-1=6 from rfl] at g; linear_combination (norm:= module) g + (2:ℝ) • h7-h6
 have hC:c=0:= (smul_eq_zero.mp (show (8:ℝ) • c =0 from add_left_cancel (a:=y) (by rw [←h8,add_zero,hy]))).resolve_left (by norm_num)
 rw [hC] at h7 h2 h3 h4 h5 h6 hx; simp [←hy] at *; exact ⟨h7,hx,h2,h3,h4,h5,h6⟩
lemma spiralDay (x: Fin 8→ G)(t:∀ i:Fin 8,x (i+1)+x (i-1)=(2:ℝ) • x i)(i:Fin 8): x i=x 0:=by
 simp_rw [two_smul ℝ] at t; have h:=spiral_eq x t; fin_cases i <;> simp [h]
lemma circle_sum (x: Fin 8→ G): ∑ i:Fin 8,(x (i+1)+x (i-1))=(2:ℝ) • ∑ i:Fin 8, x i:=by
 classical
 let e:= Equiv.addRight (1:Fin 8); let F:=Equiv.addRight (-1:Fin 8); have q:(∑ i:Fin 8,x (i+1))=∑ i:Fin 8, x i:= Equiv.sum_comp e x; have p:(∑ i:Fin 8,x (i-1))=∑ i:Fin 8,x i:= (by simp_rw [sub_eq_add_neg]; exact Equiv.sum_comp F x)
 rw [Finset.sum_add_distrib,p,q,two_smul]
end GarnetAct
