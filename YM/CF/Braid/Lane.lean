import YM.CF.Braid.Weir
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Braid
open Function Lattice RG Exterior Bloch Laurent Filter Finset Asymptotics Stationary
open Matrix (transpose mulVec of)
open scoped Matrix Topology ContDiff BigOperators
open Work.F06
variable {α ξ:Type}[Fintype α][DecidableEq α][Fintype ξ] {σ τ A C : ℝ}{M N r t:ℕ}
section combin
variable {m:Phase α→Fin (t+1)→Momentum}{u:SheetLeg α (CurRun t) 3}
def pipe(u:SheetLeg α (CurRun t) 3):Shed α (t+1):=fun p j v=>u p j (Fin.tail v)
lemma pipe_down(u:SheetLeg α (CurRun t) 3): Paddle 0 (pipe u):=by intro x j v k; rw [←Fin.cons_self_tail v]; simp [pipe]
def spouse (u:TypeFace 2→ Shed α t):Shed α (t+1):=fun p j v=>u (v 0) p j (Fin.tail v)
lemma spouse_p(u:TypeFace 2→Shed α t)(i:Fin t)(h:∀j,Paddle i (u j)): Paddle i.succ (spouse u):=by intro x j v k; rw [←Fin.cons_self_tail v,←Fin.cons_update]; simp only [spouse, Fin.cons_zero, Fin.tail_cons]; apply h
lemma spouse_n (u:TypeFace 2→ Shed α t)(i:Fin t)(x:Phase α)(k:CurRun (t+1)) : nullL (m x) i.succ (spouse u x) k=nullL (Fin.tail (m x)) i (u (k 0) x) (Fin.tail k):=by unfold nullL spouse; rfl
abbrev inlet (F:CurRun (t+1)→Phase α→ℂ)(m:Phase α→Fin t→Momentum): SheetLeg α (Run t) 2:=fun p j x=>fromCurl (m p) (fun k=> F (Fin.cons j k) p) x
def stern(m:Phase α→ Momentum)(P:SheetLeg α (CurRun t) 3): CurRun (t+1)→Phase α→ℂ:=fun x p=> cob 2 m P p (x 0) (Fin.tail x)
lemma steer {P:SheetLeg α (CurRun t) 3}(p:Phase α)(v: Phase α→Momentum)(m:Phase α→Fin t→Momentum)(x:TypeFace 2)(y:Run t): inlet (stern v P) m p x y=cob 2 v (fun z a b=> fromCurl (m z) (P z a) b) p x y:=by unfold inlet stern fromCurl cob Matrix.mulVec dotProduct; simp_rw [Fin.cons_zero,Fin.tail_cons,mul_sum]; rw [sum_comm]; exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>mul_left_comm ..
lemma growsP (u: SheetLeg α (CurRun t) 3){F:CurRun (t+1)→Phase α→ℂ}(hp:Board M A u)(h:∀ j:TypeFace 2, wallS (fun p=>Fin.tail (m p)) N t C (fun k p=> F (Fin.cons j k) p-stern (fun p=>m p 0) u (Fin.cons j k) p)): wallS m (M+N) (t+1) (max A C) F:=by
 choose X hx hq he using h; let L: Fin (t+1)→ Shed α (t+1):= Fin.cons (pipe u) (fun i=>spouse (fun j=>X j i)); refine ⟨L,?_,?_,?_⟩
 · intro i; induction i using Fin.cases with
   | zero=>exact pipe_down u
   | succ i=> unfold L; rw [Fin.cons_succ]; exact spouse_p _ i (fun j=>hx j i)
 · intro i; induction i using Fin.cases with
   | zero=> exact Board.mono (f:=pipe u) (fun i j=>hp i _) (le_max_left A C) (Nat.le_add_right M N)
   | succ i=> unfold L; rw [Fin.cons_succ]; exact fun a j=> (hq (j 0) i a (Fin.tail j)).mono (le_max_right ..) (Nat.le_add_left ..) -- tune
 intro p x; rw [Fin.sum_univ_succ]; have hU: nullL (m (axes p)) 0 (L 0 (axes p)) x=stern (fun p=>m p 0) u x (axes p):=rfl
 rw [hU]; unfold L; simp_rw [Fin.cons_succ, spouse_n (m:=m)]; have hf:=he (x 0) p (Fin.tail x); dsimp only at hf; rw [Fin.cons_self_tail x] at hf; rw [← hf]; abel
end combin
end YM.CF.Braid
