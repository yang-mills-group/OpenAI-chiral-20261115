import YM.SU5.Selected.Lantern.Hallmark
import Mathlib.LinearAlgebra.Alternating.Basic
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern.Stencil
open Function Finset BigOperators
variable {k n V W:Type*}
-- any foil S, path. homogeneous polynomial counting A vs B patches. Finite setting usable in both comm and noncomm algebras.
variable [Ring W][Algebra ℂ W]
def foil (F : n→ W)(L:List n): W:= (L.map F).prod
-- noncomm shadow. simple recursion
variable (a b:n → W)
def rake : List n→ℕ→W
 | [],0=>1
 | [], _+1=>0
 | i::l,0 => b i*rake l 0
 | i::l,k+1=> a i*rake l k+b i*rake l (k+1)
lemma rake_above (L:List n) :∀ j:ℕ,j>L.length → rake a b L j=0:=by induction L with
 | nil=> intro j h; cases j; simp at h; rfl
 | cons i l ih=> intro j h; cases j with
                  | zero => omega
                  | succ j=> rw [rake,ih j (by simp at h; omega),ih (j+1) (by simp at h; omega),mul_zero,mul_zero,add_zero]
lemma polish (c:ℂ)(L:List n): foil (c • a+b) L= ∑ k∈ range (L.length+1), c^k • rake a b L k:=by
 induction L with
 | nil => simp [rake,foil]
 | cons i l ih=>
    rw [show foil _ _=(c • a i+b i) * foil (c • a+b) l from rfl,List.length_cons,sum_range_succ' _ (l.length+1),ih]; simp_rw [rake,pow_zero,one_smul,smul_add,sum_add_distrib]; rw [add_mul]; conv_rhs => rw [add_assoc];
    congr 1
    · rw [mul_sum]; apply sum_congr rfl; intro k _; rw [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,pow_succ']
    -- second shift
    · have het: ∑ k∈range (l.length+1+1), c^k • rake a b l k=∑ k∈range (l.length+1), c^k • rake a b l k:=by rw [sum_range_succ,rake_above a b l (l.length+1) (by omega),smul_zero,add_zero]
      rw [←het,sum_range_succ',mul_add,pow_zero,one_smul,mul_sum]; congr 1; apply sum_congr rfl; intro k _; rw [Algebra.mul_smul_comm] -- tweak above congr maybe assoc.
lemma foil_scale (c:ℂ)(L:List n): foil (c•b) L=c^L.length • foil b L:=by induction L with|nil=>simp [foil]|cons i L ih=>rw [show foil _ _=(c• b i)* foil _ L from rfl,ih,List.length_cons, Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,pow_succ']; rfl
-- quadrature $t_k=k/121\in[0,1]$, code β on patch-a; pulse $c α + β = ...$. positive repairs not uniform analytics. choose capture k=12.
abbrev pulseNode:= Fin 121
def pval (i:pulseNode):ℝ:= i.val/(121:ℝ)
def heatize (t:ℝ):ℝ:= (1+t^(12:ℕ))⁻¹
lemma pace (i:pulseNode): pval i ∈ Set.Icc 0 1:= ⟨by unfold pval; positivity,(div_le_one (by norm_num : (0:ℝ)<121)).2 (by exact_mod_cast i.isLt.le)⟩
lemma heats(t:ℝ)(p:0≤t):heatize t ∈ Set.Ioc (0:ℝ) 1:= ⟨by unfold heatize; positivity, inv_le_one_of_one_le₀ (le_add_of_nonneg_right (by positivity))⟩
lemma power_node(i:pulseNode) : 0<(1:ℝ)+pval i^(12:ℕ):=by have h:0≤pval i:=(pace i).1; positivity
private theorem paid_point : ∃ w:pulseNode→ℂ,∀ i:pulseNode,∑ k, w k*(pval k:ℂ)^i.val= if i.val=12 then (10:ℂ)⁻¹ else 0 :=by
 let v:pulseNode→ℂ:= fun k=> pval k; let M:= Matrix.vandermonde v; let f(i:pulseNode):ℂ:= if i.val=12 then (10:ℂ)⁻¹ else 0; have he: Injective pval:= fun i j p=> Fin.ext (Nat.cast_injective (R:=ℝ) ((div_left_inj' (by norm_num:(121:ℝ)≠0)).mp p)); have hx: M.det ≠ 0:= Matrix.det_vandermonde_ne_zero_iff.mpr (Complex.ofReal_injective.comp he)
 obtain ⟨w,h⟩:= (show Function.Surjective (fun w=> Matrix.vecMul w M) from (Matrix.vecMul_surjective_iff_isUnit).2 ((Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.mk0 _ hx))) f
 refine ⟨w,fun i=>?_⟩; exact congrFun h i

def rho (i:pulseNode):ℂ:= paid_point.choose i * (1+(pval i:ℂ)^(12:ℕ))^(10:ℕ)
lemma point_trophy (i:ℕ)(p:i ≤ (120:ℕ)): ∑ k, rho k * ( (heatize (pval k):ℂ)^ (10:ℕ))*(pval k:ℂ)^i= if i=12 then (10:ℂ)⁻¹ else 0:=by
 have he(k:pulseNode):rho k*(heatize (pval k):ℂ)^ (10:ℕ)=paid_point.choose k:=by unfold rho heatize; have hp: ( (↑(1+(pval k)^ (12:ℕ)):ℂ)) ≠0:= Complex.ofReal_ne_zero.mpr (power_node k).ne'; push_cast at *; rw [mul_assoc,←mul_pow,mul_inv_cancel₀ hp,one_pow,mul_one]
 simp_rw [he]; exact paid_point.choose_spec (⟨i,by omega⟩:pulseNode)
lemma rho_unit : ∑ k,rho k=1:=by
 let w:= paid_point.choose; have e(t:ℕ)(p:t≤10): ∑ k,w k*(pval k:ℂ)^(12*t)= if t=1 then (10:ℂ)⁻¹ else 0:=by
    have h:= paid_point.choose_spec (⟨12*t,by omega⟩:pulseNode); exact h.trans (if_congr (by dsimp; omega) rfl rfl) -- tune
 unfold rho; change ∑ k,w k * _=_; simp_rw [add_comm (1:ℂ),add_pow,one_pow,mul_one,←pow_mul,mul_sum,←mul_assoc]; rw [sum_comm,sum_eq_single 1]; swap
 · intro i u v; have p:=e i (by have h:=mem_range.mp u; omega); rw [←sum_mul, p, if_neg v,zero_mul]
 · rw [←sum_mul,e 1 (by decide)]; norm_num
 simp

-- capture cross coefficient; includes mixed gauge charge earmark ($nontriv mod5$,1 particle A) 
lemma polarized {n:Type*}(x y z w:n→W)(L:List n)(h:L.length=10):
 ∑ i:pulseNode, (rho i) • (foil ((pval i:ℂ)^ (11:ℕ) • x + y) L * foil ((heatize (pval i):ℂ) • (((pval i:ℂ) • z) + w)) L) =
 ((10:ℂ)⁻¹ • rake x y L 1)* (rake z w L 1):=by
 simp_rw [polish x y, foil_scale,polish z w, h]; let a:ℕ:=11; let F:=range a; let f(i j:ℕ):=rake x y L i*rake z w L j; let g(i k k':ℕ):ℂ:=0 -- tune
 let P(t:pulseNode)(i j:ℕ):=(rho t*(heatize (pval t):ℂ)^ (10:ℕ))*(pval t:ℂ)^(11*i+j); have he(t:pulseNode)(i j:ℕ): rho t • (((pval t:ℂ)^ (11:ℕ))^i • rake x y L i *((heatize (pval t):ℂ)^ (10:ℕ) • ((pval t:ℂ)^j • rake z w L j))) =P t i j • f i j:=by unfold P f; rw [←pow_mul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,Algebra.mul_smul_comm, smul_smul,smul_smul,smul_smul,pow_add]; ring_nf -- tune
 have ht(i j:ℕ)(p:i ∈ F)(q:j∈ F):∑ t:pulseNode,P t i j=if i=1 ∧ j=1 then (10:ℂ)⁻¹ else 0:=by
    have p:=mem_range.mp p; have q:=mem_range.mp q; unfold a at *
    unfold P; rw [point_trophy _ (by omega)]; refine if_congr ?_ rfl rfl; omega
 simp_rw [smul_sum,sum_mul,mul_sum,smul_sum,he]; rw [sum_comm];
 calc _ = ∑ i∈F, ∑ j∈F, (if i=1∧j=1 then (10:ℂ)⁻¹ else 0) • f i j:= by
        apply sum_congr rfl; intro i t; rw [sum_comm]; refine sum_congr rfl (fun j e=>?_); rw [← Finset.sum_smul, ht i j t e]
      _ = _:=by rw [sum_eq_single 1];
                · rw [sum_eq_single 1]; simp only [ite_true, and_self_iff, Algebra.smul_mul_assoc]; rfl; intro j _ e; rw [if_neg (mt And.right e),zero_smul]; simp [F,a];
                · intro i t e; apply sum_eq_zero; intro j _; rw [if_neg (mt And.left e),zero_smul]
                simp [F,a]
end YM.CF.Pannier.Chancel.Lantern.Stencil
open YM.CF.Pannier.Chancel.Lantern.Stencil
#print axioms polarized
#print axioms polish
#print axioms rho_unit
