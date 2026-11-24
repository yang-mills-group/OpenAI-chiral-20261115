import YM.CF.Sods.Coal
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sods
open Function Filter Metric Finset
open scoped Topology BigOperators ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {E:Type*}[DecidableEq E][Fintype E][Nonempty E]{k:ℝ}{A B C:Op E}
def fro (p:Bool)(A:Op E):Op E:=if p then (1/2:ℝ) • (A+star A) else (-Complex.I) • ((1/2:ℝ) • (A-star A))
lemma fresh(p:Bool)(A:Op E):IsSelfAdjoint (fro p A):=by
 cases p; swap; · rw [fro,if_pos rfl,isSelfAdjoint_iff,star_smul,star_add,star_star]; simp [add_comm]
 rw [fro,if_neg (show _ from Bool.false_ne_true),isSelfAdjoint_iff,star_smul,star_smul,star_sub,star_star]; rw [star_neg, show star Complex.I= -Complex.I from Complex.conj_I,neg_neg,← neg_sub A,smul_neg,smul_neg,neg_smul]; simp; -- tune sign
lemma mix_g(U:UNI E):U.val=fro true U.val+ Complex.I • fro false U.val:=by
 simp only [fro,ite_true,Bool.false_eq_true,↓reduceIte,smul_smul, mul_neg,Complex.I_mul_I,neg_neg,one_smul]; module
lemma fro_b(U:UNI E)(p:Bool): ‖fro p U.val‖≤1:=by
 have he:‖U.val‖=1:=CStarRing.norm_of_mem_unitary U.property
 rcases p
 · have ht:=norm_sub_le U.val (star U.val); rw [fro,if_neg Bool.false_ne_true,norm_smul,norm_neg,Complex.norm_I,one_mul,norm_smul]; rw [norm_star,he] at ht; norm_num; linarith
 have ht:=norm_add_le U.val (star U.val); rw [fro,if_pos rfl,norm_smul]; rw [norm_star,he] at ht; norm_num; linarith
lemma fro_f(U:UNI E)(A:Op E)(p:Switch U.val A k)(b:Bool): Switch (fro b U.val) A k:=by
 have he:=p.star_left U.property
 cases b
 · rw [fro,if_neg Bool.false_ne_true]; have ht:= (p.sub_left he).smul_left (1/2:ℝ); unfold Switch; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,←smul_sub,norm_smul,norm_neg,Complex.norm_I,one_mul]; refine ht.trans_eq ?_; norm_num; ring
 rw [fro,if_pos rfl]; have ht:=(p.add_left he).smul_left (1/2:ℝ); refine ht.trans_eq ?_; norm_num; ring
lemma twink(V:UNI E)(z:ℂ)(A:Op E): twist V (z • A)=z • twist V A:=by rw [twist_formula, twist_formula, Matrix.mul_smul,Matrix.smul_mul]; -- order
lemma turned {I:Type*}(S:Finset I):∃ (r:ℕ)(C c:ℝ),1 ≤ r∧0<C∧0<c∧∀ (k:ℝ),0<k→ k≤1→∀ U:I→UNI E,(∀ i∈S,∀ j∈S,Switch (U i).val (U j).val (c*k^r)) → ∃ V:UNI E,∀ i∈S,∃ F:E→ℂ, ‖twist (star V) (U i).val-Matrix.diagonal F‖≤ C*k:=by
 classical
 obtain ⟨r,C,c,t,p,v,W⟩:=pact E (S×ˢ (univ:Finset Bool)) 1 le_rfl
 refine ⟨r,2*C,c,t,by linarith, v,fun k h H U L=>?_⟩
 obtain ⟨V,g,T⟩:= W k h H (fun _ : E=>[]) (fun i : I×Bool=>fro i.2 (U i.1).val) (fun i _=>⟨fresh ..,fro_b ..,fun _ _ p=>False.elim (p rfl)⟩) (fun i s j b=> fro_f (U i.1) _ (fro_f (U j.1) _ (L _ (mem_product.mp b).1 _ (mem_product.mp s).1) j.2).symm i.2)
 refine ⟨V,fun i h=>?_⟩
 obtain ⟨F,H⟩:=T (i,true) (mem_product.mpr ⟨h,mem_univ _⟩); obtain ⟨G,S⟩:=T (i,false) (mem_product.mpr ⟨h,mem_univ _⟩)
 let J(a):= (F a:ℂ)+Complex.I * (G a:ℂ); let D(u:E→ℝ):Op E:=Matrix.diagonal fun i=>(u i:ℂ); let A:=fro true (U i).val; let B:=fro false (U i).val
 have he:Matrix.diagonal J=D F +Complex.I • D G:=by ext x y; by_cases h:x=y <;> simp [D,h,J]
 have hh(K:Op E):twist V (twist (star V) K) = K:=by nth_rw 1 [←star_star V]; exact twist_inv ..
 refine ⟨J,?_⟩; rw [← twist_norm V,map_sub,hh,he,map_add,twink,mix_g,add_sub_add_comm, ←smul_sub]; apply (norm_add_le ..).trans; rw [norm_smul,Complex.norm_I,one_mul]; exact (add_le_add H S).trans_eq (by ring)
end YM.CF.Sods
