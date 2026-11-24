import YM.CF.Braid.Mimi
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
-- contraction f values pointer-wise binary slot
lemma wee {n:ℕ} (p: Momentum)(F:TypeFace (n+2)→ℂ): (symbol n p).transpose *ᵥ ((symbol (n+1) p).transpose *ᵥ F)=0:=by rw [Matrix.mulVec_mulVec,←Matrix.transpose_mul,symbol,symbol,d_d,Matrix.transpose_zero,Matrix.zero_mulVec]
lemma first_h (p:Momentum) (F:TypeFace 2→ℂ) : ∑ j:TypeFace 1, symbol 0 p j vac* ((symbol 1 p).transpose *ᵥ F) j=0:= congr_fun (wee ..) vac -- tune
variable{n:ℕ}
lemma chr (m:Fin n→Momentum) (F:CurRun n→ℂ)(i:Fin n)(s:Run n):∑ j:TypeFace 1, symbol 0 (m i) j vac * fromCurl m F (update s i j)=0:=by -- n undecl. induction
 induction n with
 | zero=> exact i.elim0
 | succ n ih=>
    rw [← Fin.cons_self_tail s]; refine Fin.cases ?_ (fun i=> ?_) i
    · simp_rw [Fin.update_cons_zero,fromCurl_cons,Fin.cons_zero,Fin.tail_cons]; exact first_h (m 0) (fun y=> fromCurl (Fin.tail m) (fun x=> F (Fin.cons y x)) (Fin.tail s))
    simp_rw [← Fin.cons_update, fromCurl_cons, Fin.cons_zero, Fin.tail_cons, mul_sum]; rw [sum_comm]; apply sum_eq_zero; intro j _; simp_rw [mul_left_comm (symbol 0 _ _ _) (symbol 1 _ _ _),← mul_sum]; exact mul_eq_zero_of_right (symbol 1 (m 0) j (s 0)) (ih (Fin.tail m) (fun x=> F (Fin.cons j x)) i (Fin.tail s))
-- tuple vary representation rather than array Typeface i separately. C(i:leg)(a:TypeFace 3)(x:CurrRun t). consistency independent at i. Null image B j...
abbrev Shed(α:Type)(t:ℕ):= SheetLeg α (CurRun t) 3
variable{n:ℕ}
def Paddle (i:Fin t)(U:Shed α t):Prop:= ∀ p j x (k:TypeFace 2), U p j (update x i k)=U p j x
def nullL (m:Fin t→Momentum)(i:Fin t)(V:TypeFace 3→CurRun t→ℂ)(x:CurRun t):=∑ b: TypeFace 3,symbol 2 (m i) b (x i)* V b x
def wallS(v:Phase α→Fin t→Momentum)(M C':ℕ)(A:ℝ)(H:CurRun t→Phase α→ℂ): Prop:=
 ∃ C:Fin t→ Shed α t,(∀ i,Paddle i (C i))∧ (∀ i, Board M A (C i))∧ ∀ (p:Corn α) (x:CurRun t), H x (axes p)=∑ i,nullL (v (axes p)) i (C i (axes p)) x
lemma con_s (m:Keys t↪α)(h:0 ≤ A)(u:CurRun t→Phase α→ℂ)(hp:∀ i,Pond M A (u i)):∀ i,Pond (M+t) (A*(topG 1)^t) (fun p=>fromCurl (strands m p) (fun i=> u i p) i):=by
 induction t with
 | zero=>
    intro i; have hh(p:Phase α): fromCurl (strands m p) (fun i=> u i p) i=u default p:=by simp [fromCurl] -- tune
    simp_rw [pow_zero,mul_one,Nat.add_zero,hh]; exact hp _
 | succ t ih=>
    have ht (j:TypeFace 2):= ih (decaym m) (fun i=> u (Fin.cons j i)) (fun i=>hp _)
    intro i
    let V: SheetLeg α Unit 2:=fun p j _=> fromCurl (Fin.tail (strands m p)) (fun y=>u (Fin.cons j y) p) (Fin.tail i)
    have hV: Board (M+t) (A*topG 1^t) V:= fun j _=>ht j _
    simp_rw [fromCurl_cons]; exact (cargo ((stick t).trans m) hV (mul_nonneg h (pow_nonneg (show 0≤topG 1 from by unfold topG; positivity) _)) (i 0) ()|>.mono (by rw [pow_succ,mul_assoc]) (by omega))
end YM.CF.Braid
