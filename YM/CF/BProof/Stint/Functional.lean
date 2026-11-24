import YM.CF.BProof.Align.Order
import YM.CF.BProof.Stint.Earn

/-! B-matrix. Costs on Op authority. Use the *same* uniform parameter price for
all configurations; geometric series bill, then inversion and log. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Stint
open Function Filter Fock Finset Branch NormedSpace
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
abbrev Happy (v C:ℝ)(p r:Pay)(l:ℝ):Prop := ∀ {I Y Z G: Type} [Fintype Y] [Fintype I] [Nonempty I] [DecidableEq I] [DecidableEq Y] [TopologicalSpace Z] {b:Branch.Stage Y I Z G} {s: Branch.Tag b} {A: Raw Z I}, Capacity b C→Earn p s s A→ (∀ x, ‖A x‖ ≤ v) → ∀ n:ℕ, RootedK s s r.rate (r.cash*l^n) (fun x=> A x ^ n)
variable {v C:ℝ}{p r:Pay}(h:0<v)(q:v<1)(e:0≤C)
include h q e
lemma chunk (p:Pay) : ∃ (l:ℝ)(r:Pay), 0<l ∧ l<1 ∧ Happy v C p r l := by
 obtain ⟨k,ht,hk⟩:=exists_between q
 obtain ⟨n,hN,w,d,hp,g,W,U⟩:=grouping e p.charge p.funding ht (h.trans ht) hk (show 0<(1:ℝ)/4 by norm_num)
 obtain ⟨t,j,f,B⟩:=drift_name hN (show 0<(1:ℝ)/2 by norm_num) (by norm_num)
 refine ⟨t,⟨d,2*(Real.exp d*(t^n)⁻¹*(Real.exp d*(max 1 (2*p.cash))^n)),hp,?_⟩,j,f,?_⟩; swap
 · intro I Y Z G _ _ _ _ _ _ b s A H hA hv i
   have he : RootedK s s d (1/4) (fun x=>A x^n):= power_low C p.rate p.cash k _ v n w d e p.charge.le (h.trans ht).le hp.le g W U H hA.holds hv
   exact tariff hN hA.holds he (g.trans (half_le_self p.charge.le)) hp j B i
 positivity
lemma seriesCost (p: Pay)(j:ℕ) (c:ℕ→ℝ)(g:∀ i, ‖c i‖≤1): ∃ r:Pay, ∀ {I Y Z G: Type} [Fintype Y] [Fintype I] [Nonempty I] [DecidableEq I] [DecidableEq Y] [TopologicalSpace Z] {b:Branch.Stage Y I Z G} {s: Branch.Tag b} {A: Raw Z I}, Capacity b C→Earn p s s A→ (∀ x, ‖A x‖ ≤ v) → Earn r s s (fun x=>∑' i:ℕ,c i • A x ^(i+j)):= by
 obtain ⟨l,r,he,hv,X⟩:=chunk h q e p
 let M(i:ℕ):=r.cash*l^(i+j); have hp:Summable M:= ((summable_nat_add_iff j).mpr (summable_geometric_of_lt_one he.le hv)).mul_left _
 refine ⟨⟨r.rate,max 1 (∑' i,M i),r.charge,lt_max_of_lt_left one_pos⟩,?_⟩; intro I Y Z G _ _ _ _ _ _ b s A H hA hN; refine (RootedK.tsK M ?_ r.charge.le hp).books (le_max_right ..); intro i; have ht:= (X H hA hN (i+j)).raise (c i); simp only [Complex.coe_smul, Complex.norm_real] at ht; have hf: 0≤ M i:=mul_nonneg r.funding.le (pow_nonneg he.le _); exact ht.books (mul_le_of_le_one_left hf (g i))
abbrev Functional (C:ℝ)(p r:Pay)(P:∀ {I: Type} [Fintype I] [Nonempty I] [DecidableEq I], Op I → Prop)(F:∀ {I: Type} [Fintype I] [Nonempty I] [DecidableEq I], Op I→Op I) : Prop:= ∀ {I Y Z G: Type} [Fintype Y] [Fintype I] [Nonempty I] [DecidableEq I] [DecidableEq Y] [TopologicalSpace Z] {b:Branch.Stage Y I Z G} {s: Branch.Tag b} {A: Raw Z I}, Capacity b C→ Earn p s s A→ (∀ x,P (A x))→ Earn r s s (fun x=> F (A x))
lemma windCost (p: Pay): ∃ r, Functional C p r (fun a=> ‖a‖≤v) (fun A=> (1-A)⁻¹):=by -- tune binders
 obtain ⟨r,S⟩:=seriesCost h q e p 0 (fun _=>1) (by simp); refine ⟨r,?_⟩; intro I Y Z G _ _ _ _ _ _ b s A W ht hx; simpa only [one_smul,add_zero,route_inv ((hx _).trans_lt q)] using S W ht hx -- hx type dsimp
lemma pencilCost (p:Pay): ∃ r, Functional C p r (fun a=> ‖a‖≤v) (fun A=> pencil A):= seriesCost h q e p 1 bcoef bc_norm
omit q in
theorem inverseCost (p:Pay): ∃ r, Functional C p r (fun a=>v • 1 ≤ a) (fun a=> a⁻¹):=by
 let k:=p.cash+v; let g:=p.wage ‖k⁻¹‖; have hx:=p.funding; have hp:v<k:=by unfold k; linarith
 have he:=h.trans hp; obtain ⟨r,T⟩:=windCost (sub_pos.mpr ((div_lt_one he).mpr hp)) (show 1-v/k<1 by have := div_pos h he; linarith) e (Pay.simple.add g); refine ⟨r.wage ‖k⁻¹‖,?_⟩; intro I Y Z G _ _ _ _ _ _ b s A W ht hy
 have hu(x): A x ≤ k •1:= Align.under (Align.strictPositive h (hy x)).nonneg ((ht.norm x).trans (by unfold k; linarith))
 have hg:= T W ((Earn.one s).minus (ht.wage (v:=‖k⁻¹‖) le_rfl)) (fun i=> Align.rescale h hp.le (hy i) (hu i)); simp only [sub_sub_cancel] at hg; simp_rw [Align.rescale_inv (A:=A _) he (Align.active h (hy _))]; exact hg.wage le_rfl
omit q in
theorem singularCost (p:Pay): ∃ r, ∀ {I Y Z G: Type} [Fintype Y] [Fintype I] [Nonempty I] [DecidableEq I] [DecidableEq Y] [TopologicalSpace Z] {b:Branch.Stage Y I Z G} {s t: Branch.Tag b} {A: Raw Z I}, Capacity b C→ Earn p s t A→ (∀ x, v • (1:Op I) ≤ star (A x)*A x) → Earn r t s (fun x=> (A x)⁻¹):=by
 obtain ⟨r,T⟩:=inverseCost h e (p.mul p); refine ⟨r.mul p,?_⟩; intro I Y Z G _ _ _ _ _ _ b s t A u W H
 have ht(x): (A x)⁻¹=(star (A x)*A x)⁻¹*star (A x):= Matrix.inv_eq_left_inv (by rw [mul_assoc]; exact (live (Align.active h (H x))).2)
 simp_rw [ht]; exact (T u (W.adj.times W) H).times W.adj
end YM.CF.BProof.Stint
