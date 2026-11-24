import YM.CF.BProof.Wick.Purl
import YM.CF.BProof.Stint.Dawn

/-! Scalar support prices actually on site-trace matrices, their sum cont & cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Wick
open Function Filter NormedSpace Fock Finset Branch Align Double MeasureTheory Stint
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L r:ℝ}(x:0≤L)
include x
theorem eatConst : ∃ p:Pay,∀ {I Y D G:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D G}{s:Tag b}, Capacity b L→Earn p (straw s) (straw s) (fun i=>i.2.val • (1:Op I)):=by
 let T:= L*((↑(0:ℕ):ℝ)+1)^4* Real.exp (1*(L*((↑(0:ℕ):ℝ)+1)^4))*2; refine ⟨⟨1,max 1 T,one_pos,lt_max_of_lt_left one_pos⟩,?_⟩; intro I Y D G _ _ _ _ _ _ b s h
 let u:= straw s; let F(i:D×Time):=i.2.val • (1:Op I); refine (row_earn (m:=0) (b:=Ella b) (K:=2) (Ella_pay h) x zero_le_one (F:=F) (s:=u) (t:=u) ?_ ((continuous_subtype_val.comp continuous_snd).smul continuous_const) (by norm_num) ?_ ?_ ?_).books (le_max_right ..)
 · intro i x; unfold F; simp only [Ella,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,mul_one,one_mul]
 · intro p i j t; have he:i≠j:=fun v=>by rw [v,(Ella b).F.reflex] at t; omega; -- tune
   simp [F, Matrix.one_apply_ne he]
 · intro i j p; refine (norm_entry (F p) i j).trans ?_; unfold F; rw [norm_smul,norm_one,mul_one]; exact (upt p.2.property).trans (by norm_num)
 intro i j p p'; by_cases l:p.2=p'.2; · rw [show F p=F p' from congrArg (fun i:Time=>i.val • (1:Op I)) l,sub_self,norm_zero]; exact mul_nonneg (by norm_num) ((Ella b).pos ..)
 refine (norm_entry (F p-F p') i j).trans ?_; unfold F; apply (norm_sub_le ..).trans; simp only [norm_smul,norm_one,mul_one,Ella,l,↓reduceIte]; have hu:=upt p.2.property; have hv:=upt p'.2.property; linarith only [hu,hv,b.pos (bay b.F (b.home i) 0) p.1 p'.1]

theorem exPay (p q u:Pay)(h:r<1) : ∃ v w:Pay,∀{I Y D G:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D G}{s:Tag b}{A C:Raw D I}, Capacity b L→Earn p s s A → Earn q s s.reverseV C → (∀ i,Shelf (A i) (C i) r) →
 (∀ (G:Raw D I), Earn u s s G→ Earn v s s (fun i=>salary (A i) (G i) (C i))) ∧ ∀ G:Raw D I, Earn u s s.reverseV G → Earn w s s (fun i=> (bonus (A i) (G i) (C i))ᵀ):=by
 obtain ⟨X,T⟩:= pullF one_pos h x p p p q; let y:= X; refine ⟨u.mul X, (u.mul X).wage ‖(1/2:ℂ)‖,?_⟩; intro I Y D G _ _ _ _ _ _ b s A C hB hS W hC; let F(x):=cern (A x) 0 0 (C x); let t:=s.reverseV
 have he:Earn X (signs t s) (signs s t) F:=by apply elevate s ▸ (T (P:=fun _=>0) (Q:=fun _=>0) hB hS (Earn.free p) (Earn.free p) W (fun i=>nothing_deck (hC i))) -- tune
 have hf:Earn X t t (fun i=> letter true false (F i)) := account true false he; have hp:=transE hf; unfold t at hp; rw [restore s] at hp
 refine ⟨fun G g=> g.times hp,fun B k=>?_⟩
 have ht:Earn X s t (fun i=> letter false false (F i)):= account false false he; have hk:Earn X s t (fun i=> (letter false false (F i))ᵀ) := by convert transE ht using 1; exact (restore s).symm
 have hv:Earn ((u.mul X).wage ‖(1/2:ℂ)‖) t t (fun i=> bonus (A i) (B i) (C i)) := (k.adj.times hk).scalar le_rfl; simpa only [t,restore s] using transE hv
variable {I Y D G:Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D G}
omit x in
lemma avgTrace (g:D×Time→Op I)(h:Continuous g)(f:ℝ→Op I)(x:D)(p:∀ i:Time, f i.val=g (x,i)): ∫ t in (0:ℝ)..1,(f t).trace=(avg g x).trace:=by
 rw [avg_use (U:=ℂ) (fun x=>(g x).trace) _ x (fun i=>congrArg Matrix.trace (p i))]; let F: Op I →L[ℝ] ℂ := (Matrix.traceLinearMap I ℝ ℂ).toContinuousLinearMap; exact F.intervalIntegral_comp_comm (grain g h x)
end YM.CF.BProof.Wick
