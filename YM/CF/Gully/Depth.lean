import YM.CF.Gully.Tax
set_option autoImplicit false
set_option maxHeartbeats 550000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Gully
open Function Fock Filter Metric NormedSpace Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset Mir Scroll Spire RP Str Petal Manifest Palot Stilo Dial Paige Vault Brace RG Push.AbsoluteSums Trees
open scoped Topology Classical BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B L N:Side}
local notation "Λ" => CSide m B
local notation "ξ" => Domain m B
open Maize Gloss Floe Ave Phase.Sample Jet Pastry Drapes Gas
variable {r e U K A H:ℝ}{n:ℕ}
variable {a b c d r p:ℝ}{ρ:ℕ→ℝ}
def Ant(n:ℕ)(j:ℕ)(c:ℝ)(ρ:ℕ→ℝ):= c+ n.factorial*c*(ρ j)⁻¹^n
lemma poly_m (n:ℕ)(q:0 < a)(hp:Apert ρ):∃ C:ℝ,0 ≤ C∧∀ (j:ℕ)(c:ℝ),0 ≤ c→ Real.exp (a/2*j)*Ant n j c ρ ≤ C*(Real.exp (a*j)*c):=by
 obtain ⟨m,d,l,w⟩:=hp.poly; let V:= (n.factorial:ℝ)*d^n; have hv:0≤V:=by unfold V; positivity
 obtain ⟨X,hx,h⟩:=stash 0 le_rfl (m*n) q
 refine ⟨1+X*V,by positivity,fun i c hc=>?_⟩; unfold Ant; rw [mul_add,add_mul,one_mul]; apply add_le_add
 · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (half_le_self q.le) (Nat.cast_nonneg _))) hc
 let u:= V*c; have hu: 0 ≤u:=mul_nonneg hv hc; let N:= m*n; apply le_trans _ ((h u hu i i le_rfl).trans_eq ?_)
 · have ht:=hp.pos i; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr ht.le) (w i) n) (show 0≤ (n.factorial:ℝ)*c by positivity)).trans
   rw [mul_pow,← pow_mul,show (n.factorial:ℝ)*c*(d^n*(1+i:ℝ)^(m*n))=u*(1+i:ℝ)^(m*n) by unfold u V; ring]; unfold mercury; apply mul_le_mul_of_nonneg_right _ (by positivity); simp only [mul_zero,Real.exp_zero,mul_one]; have he:1≤ (↑(m*n).factorial:ℝ):=(by exact_mod_cast Nat.factorial_pos _); exact le_trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hu)) (le_mul_of_one_le_left (by positivity) he)
 unfold u; ring
lemma pay_conv {T:Type}[Fintype T] (w:T→Support N)(v:T→ℝ)(r:ℝ)(x:Site N): hitE r (fun S=>∑ i∈dest w S,v i) x=bill_X w v r x:=by
 unfold hitE hit0 bill_X dest; simp_rw [sum_filter]
 conv_lhs =>
    arg 2; ext i
    rw [mul_sum,ite_sum_zero]
 rw [sum_comm]; refine sum_congr rfl ?_; intro S _; rw [sum_eq_single_of_mem _ (mem_univ (w S))]; simp only [↓reduceIte,mul_comm]; intro i _ g; simp [Ne.symm g]
variable {C P:ℝ} (q:1≤ H)
lemma ant_n {T:Briar m B e→ Ewe m B}{S:ApD m}{w:ℝ}(p:Token (welter m B e H q) S.val T w (Grove (terr _))) (h:Γe U n T H ρ S.val.card w)(v:Apert ρ) : CoInk S.val e H q U n T (Ant n S.val.card w ρ):=by
 let R:= ρ S.val.card; let h:= h; have ht:= v.pos S.val.card; let D:= n.factorial*w* R⁻¹ ^ n; have hu:0≤ w:=p.price; have hg:0≤ D:=by unfold D R; positivity
 refine ⟨{p with price:= add_nonneg hu hg, shape:= fun e=>p.shape (fun k=>e (by simp [Ant,k])),owns:=fun x=> (p.owns x).trans (le_add_of_nonneg_right hg)},?_⟩
 intro E _ _ _ f S p g x t -- S shadows
 exact ((h E f S p g x t).out ht (v.cap _)).mono (le_add_of_nonneg_left hu)
lemma nozz (n:ℕ)(p:0<P)(v:Apert ρ)(u:0≤ C): ∃ Z:ℝ,0≤Z∧∀ (m B:Side)(H:ℝ)(e U:ℝ)(K:Scroll m B (northZ m B))(t:1 ≤ H)(x:ℝ),ArtX K U n ρ P C H t e x → ∃ F,coBooks (m:=m) (B:=B) e U H t n F (P/2) Z∧∀ y,(motor (Ave.travel m B e H t) (fun w=>exp (chillT K x w)) y)=exp (F y)∧∀ s:Era m,Rayp s B (F y)=F (shotV s y):=by
 obtain ⟨Z,hz,Y⟩:=poly_m n p v; refine ⟨_,mul_nonneg hz u,fun m B H e U W t x K=>?_⟩
 obtain ⟨T,w,h,g,l⟩:=K; let R(i:ApD m):=i.val; let F(x:Briar m B e):=∑ i:ApD m,T i x; refine ⟨F,groupT (R:=R) (K:=Z*C) (fun i=> ant_n t (h i).1 (h i).2 v) ?_ (fun _=>rfl),l⟩ -- tune stem
 intro i; apply le_trans _ (mul_le_mul_of_nonneg_left (g i) hz); rw [pay_conv]; unfold bill_X; rw [mul_sum]; apply sum_le_sum; intro j _; change Ant n j.val.card (w j) ρ*rent _ (R j)≤ Z*(w j*rent P j.val); rw [mul_comm (Ant ..),mul_comm (w j)]; exact Y j.val.card (w j) (h j).1.price
end YM.CF.Gully
