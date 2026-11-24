import YM.CF.DPress.Analytic.Line
import YM.CF.Vow.Pole
/-!
 Uniform sum by *degrees*, never allowing each sup × number of actual clusters.
 With fixed costs eventually, the tail over any support holds using each own weight.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.DPress.Analytic
open Function Set Filter Metric MeasureTheory Finset
open scoped Topology Classical ContDiff InnerProductSpace ComplexConjugate YM.CF.Mew Matrix MatrixOrder Matrix.Norms.L2Operator
open Lattice RG Cube Lat Fock Push.AbsoluteSums Trees Hake Wray Pastry Skye Scree Vow Mew Palot Ursell
attribute [local instance] opCStarAlgebra
variable {n:Side}{a b δ q:ℝ}{P:BudgetPoint} (s:Set ℂ)(p:IsOpen s)(A:ℂ→Pax n)(j:Aura n)(i:Orbit n)(W : ℂ→ Aura n → ℝ)
variable (u:∀ x:ℂ,Ready stern P.B (W x) a b δ q)(h:0 ≤ a){k:ℝ}(hK:1≤k)(w:∀ x T, Medal P T.val ∅ (A x T) k (W x T))
-- uniform tail & invisible.
include hK u h w
private lemma boundH (v:visible P j.val ∅ i.1)(m:ℕ)(x:ℂ) : ‖funge j (A x) 0 m i‖≤ b*q^m*(1-q)⁻¹:=by
 obtain ⟨V,h',c⟩:=v; let Z(u:Aura n) := spanD u (W x) m; have ht(y:Aura n):0 ≤ Z y:= (glenP y hK (w _) (u _) h m).wage (zero_le_one.trans hK); obtain ⟨j',v'⟩:=j.property; refine le_trans (b:=Z j) ?_ ?_
 · have he (t:Clusters (Aura n)) : ‖sta (A x) j m t i‖ ≤ sepV (W x) j m t:=by let G:=ponder j t hK (w x) m; rw [G.same i (V,i.2) c (fun _ _=>rfl)]; exact G.capF hK (V,i.2) h'
   let X:=glomM j (m:=m) (u x) h; unfold funge; rw [Finset.sum_apply]; apply le_trans (norm_sum_le ..); apply le_trans (sum_le_sum (g:=fun v:Tuple (Aura n) m=>sepV (W x) j m ⟨m,v⟩) (fun t (_:t∈Finset.univ)=>?_ )); swap; · rw [show sta (A x) j 0 ⟨m,t⟩=sta (A x) j m ⟨m,t⟩ from (by unfold sta; simp)]; exact he _
   unfold Z spanD; rw [X.tsum_sigma, ← show (∑' v:Tuple (Aura n) m,sepV (W x) j m ⟨m,v⟩)=(∑ v:Tuple (Aura n) m,sepV (W x) j m ⟨m,v⟩) from tsum_fintype _]; apply X.sigma.le_tsum _; intro i k; exact tsum_nonneg fun v=> le_trans (norm_nonneg _) (he _)
 refine le_trans ?_ (thinX (u x) h j' m); exact (le_mul_of_one_le_right (ht j) (Real.one_le_exp (mul_nonneg h (by positivity)))).trans (single_le_sum (f:=fun i: Aura n=>spanD i (W x) m*currency P.B a i.val) (fun i _=>mul_nonneg (ht i) (Real.exp_pos _).le) (mem_filter.mpr ⟨mem_univ _,v'⟩))
include p
lemma glowing (g:∀ j:Aura n,∀ i:Orbit n,DifferentiableOn ℂ (fun x=> A x j i) s): DifferentiableOn ℂ (fun x=> FeeD P (A x) j i) s:=by
 unfold FeeD spinD lasting Vow.zenS; split; next v=>
    apply Complex.differentiableOn_tsum_of_summable_norm (((summable_geometric_of_lt_one (ready_pos _ _ (u 1)|>.le) (u 1).2.2.2.1).mul_left b).mul_right (1-q)⁻¹) _ p (?_ ); swap; · intro i x p; exact boundH A _ _ W u h hK w v i x
    intro l; unfold funge; simp_rw [Finset.sum_apply]; apply DifferentiableOn.fun_sum; intro t _; unfold sta; split; rename_i hv; unfold guava; simp_rw [Pi.smul_apply,Finset.prod_apply,RCLike.real_smul_eq_coe_smul (K:=ℂ)]; show DifferentiableOn ℂ (fun z=> (_:ℂ) • _) s; exact DifferentiableOn.fun_const_smul (DifferentiableOn.fun_finsetProd (fun _ _ => g _ _)) _; exact differentiableOn_const _
 next h=> exact differentiableOn_const _
end YM.CF.DPress.Analytic
