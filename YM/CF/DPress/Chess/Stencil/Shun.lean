import YM.CF.DPress.Chess.Stencil.Width
import YM.CF.Peaks.Orange
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Chess.Symbol
open Function Filter Finset Lattice Bloch Laurent Next.Free Fir Rush Scroll Lat
open scoped Topology BigOperators NNReal ENNReal Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{I J:Type*}
open Trig
lemma freight(j:ℕ)(L:Side)(i k:St L): Trig (fun x=> brix j L x i k):=by
 rcases i with ⟨i,u⟩; rcases k with ⟨k,v⟩; let g(p:Momentum):=mode p (lift i)*muff j L p; let w:=((L.val:ℂ)^2)⁻¹ * (((Real.sqrt L.val)⁻¹ :ℝ) :ℂ)
 by_cases h:k=0; swap
 · exact (Trig.fixed (((if i=k then (1:ℂ) else 0) • (1:Op SpinIdx)) u v)).cong (fun x p=> Eq.symm (by change Scroll.tap (brix j L x) i k u v=_; rw [tapeB L x j i k p,if_neg h]))
 apply (Trig.mul (Trig.mul (Trig.fixed w) (hord (A:=g) ((tone (lift i)).mul (muffX j L)) L)) (Trig.fixed ((1:Op SpinIdx) u v))).cong; intro x p; change w*_*_=Scroll.tap (brix j L x) i k u v; rw [tapeB L x j i k p,if_pos h,Matrix.smul_apply,smul_eq_mul,mul_sum]; apply congrArg (·*(1:Op _) u v); apply Finset.sum_congr rfl; intro k _; unfold w g money; ring -- syntax.
section
variable [Fintype I][DecidableEq I] {F:Momentum→Op I}
lemma finance (p:∀ i j, Trig fun x=> F x i j) : ∃ U : Cover→ Op I,Reads U F ∧ ∃ S: Finset Cover,∀ x: Cover,x∉ S→U x=0:=by
 choose S u v using p; let f(x:Cover)(i j:I):= if x∈S i j then u i j x else 0; let U(x:Cover):Op I:=Matrix.of (f x); have ht (i j : I) (x:Cover)(h:x ∉ S i j): U x i j=0:=if_neg h
 refine ⟨U,⟨?_,?_⟩, ?_⟩
 · intro i j; apply summable_of_ne_finset_zero; intro b hb; rw [ht i j b hb,norm_zero]
 · intro a h i j; apply Eq.trans _ (v i j a h.1).symm; unfold Laurent.read; rw [tsum_eq_sum (s:=S i j)]; apply Finset.sum_congr rfl; intro x k; change mode a x*U x i j=_; exact congrArg _ (show U x i j= _ from if_pos k)
   intro b v; change mode a b* U b i j = 0; rw [ht i j b v,mul_zero]
 refine ⟨univ.biUnion (fun i:I=> univ.biUnion (S i)), fun x p=>Matrix.ext fun i j=>ht i j x (?_)⟩; exact fun k=> p (mem_biUnion.mpr ⟨i,mem_univ _,mem_biUnion.mpr ⟨j,mem_univ _,k⟩⟩)
end
lemma brix_h (j:ℕ)(L:Side)(h:Odd L.val): ∃ S:Finset Cover,∀ x:Cover,x ∉ S → tub (brix j L) x=0:=by obtain ⟨g,p,T,v⟩:= finance (freight j L); rw [Reads_u (brix j L) _ g (cBrix j L h) p]; exact ⟨T,v⟩ -- tune
end YM.CF.DPress.Chess.Symbol
