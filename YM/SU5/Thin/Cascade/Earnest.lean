import YM.SU5.Thin.Cascade.Devices
import YM.SU5.FiniteGaugeData.Pannier.Gale
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Pannier.Chancel
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {a C r e:ℝ}{n N:Side}
variable {F:Chin n→Op (Single n)}
private lemma one_p_bill {r:ℕ}(S:Seal (Site (More n)))(p:S.card ≤ r)(s T: Pane n)(h:∀ i∈ leaks S, ‖profile s i-profile T i‖ ≤ e)(v:0≤e): fare S (profile s) (profile T) ≤ (r:ℝ)*4*e:=by
 have he: (leaks S).card ≤ r*4:= by
    calc
    _ ≤ Finset.card (S ×ˢ (Finset.univ: Finset Axis)):= card_le_card fun i hi=> mem_product.mpr ⟨(mem_filter.mp hi).2.1, mem_univ _⟩
    _ = S.card*4 := by simp [Axis] -- RHS placeholder ambiguous
    _ ≤ r*4 := Nat.mul_le_mul_right _ p
 unfold fare; refine (sum_le_sum (g:=fun _=> e) (fun i hi=> h i hi)).trans ?_
 rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast he) v
private lemma wave_help (p:RootedK (bail n r) (bail n r) a C (fun v : Openc (More n) r=> F v.val))(hr:0<a) (hx:0<r) (d:ℕ)(U V:Pane n)
    (u:Guard U r)(v:Guard V r)(L:Finset (Seat n))(e:ℝ)(h:0≤e)(t:Rightful (Lattice.halo d L) U V e) (z:Single n)(x:node z.1.1∈L) :
    ∑ i:Single n, ‖(F (profile U)-F (profile V)) i z‖ ≤ (2*Real.exp (-(a*d))+ d*4*e/r) * C:=by
 obtain ⟨N,b,p,j,w⟩:=p
 let U':Openc (More n) r:=⟨profile U,U,u,by simpa⟩
 let V':Openc (More n) r:=⟨profile V,V,v,by simpa⟩
 let A:=saleM a b
 let E:=2*Real.exp (-(a*d))+(d:ℝ)*4*e/r
 have hp:0≤E:= by unfold E; positivity
 let Q(i v):= E*A i v
 have hu(i:Single n): ‖(F (profile U)-F (profile V)) i z‖ ≤ Q i z:=by
   rw [Matrix.sub_apply]; rw [show F (profile U)=_ from w U', show F (profile V)=_ from w V',Matrix.sum_apply,Matrix.sum_apply,← sum_sub_distrib]; unfold Q A saleM; rw [mul_sum]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro s _
   let a':=b s i z; let H:= (p s).expo i z; have ha : ‖_‖ ≤ _:= H.bounded U'; have hb:= H.bounded V'; let Q:= N s U' i z - N s V' i z; have hQ: ‖Q‖ ≤ a'+a':= (norm_sub_le ..).trans (add_le_add ha hb)
   change ‖Q‖≤ E * (rent a s*a'); rw [←mul_assoc]; by_cases g:a'=0; · rw [g,mul_zero]; simpa [g] using hQ
   rcases le_or_gt s.card d with he|he
   · obtain ⟨s₁,h₁,g₁⟩:=H.triggered g
     have hs(y)(l:y∈s): y ∈ (Lattice.halo d L) := halo_spec.mpr ⟨_,x,(le_of_lt (show separation (node z.1.1) y<s.card from s₁.lim _ g₁ _ l)).trans he⟩
     have hu:= one_p_bill s he U V (fun i hi=>t i (mem_filter.mpr ⟨mem_univ _,hs i.1 (mem_filter.mp hi).2.1,hs _ (mem_filter.mp hi).2.2⟩)) h
     apply (H.variation U' V').trans
     rw [mul_comm (E*rent a s)]; apply mul_le_mul_of_nonneg_left _ (show 0≤a' from H.positive)
     change fare s _ _ / |r| ≤ _; rw [abs_of_pos hx]; exact (div_le_div_of_nonneg_right hu hx.le).trans (le_trans (le_add_of_nonneg_left (by positivity)) (le_mul_of_one_le_right hp (rent_one hr.le _)))
   · rw [show a'+a'= 2*a' from (by ring)] at hQ; apply hQ.trans; apply mul_le_mul_of_nonneg_right _ H.positive
     unfold E Branch.rent; rw [add_mul]; apply le_trans _ (le_add_of_nonneg_right (show 0 ≤ ↑d*4*e/r*Real.exp (a*s.card) by positivity)); rw [mul_assoc,←Real.exp_add]; refine le_mul_of_one_le_right (by norm_num) (Real.one_le_exp (by nlinarith [show (d:ℝ) ≤ s.card by exact_mod_cast he.le]))

 refine (sum_le_sum (fun i _=>hu i)).trans ?_; unfold Q; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (j.cols _) hp

open Rapids
-- A single variation bound for full columns; paid by rootedness, no resumming individual element budgets.
structure Finisher (δ a C:ℝ)(j N:ℕ) : Prop where
 health : 0 < δ
 credit : 0 < C
 rate : 0<a
 column (n:Side)(k:N ≤ n.val)(U:Pane n)(p:Guard U δ) (M:Tulip.Male): Filed (spar j M U) C
 wind (n:Side)(k:N ≤ n.val)(U V:Pane n)(p:Guard U δ) (h:Guard V δ) (M:Tulip.Male)(d:ℕ)(z:Single n)(e:ℝ)(s:0 ≤ e)(t: Rightful (Lattice.halo d {node z.1.1}) U V e): ∑ i:Single n, ‖(spar j M U-spar j M V) i z‖ ≤ (2*Real.exp (-(a*d))+ d*4*e/δ)*C
lemma finishingLine(j:ℕ)(p:1≤j):∃ δ a C:ℝ,∃ N:ℕ, Finisher δ a C j N:=by
 obtain ⟨a,r,e,h,hc,l,v,Q⟩:= funde_s _ p
 refine ⟨e,a,r,v,l,hc,h,fun n g U H M i=>?_,?_⟩
 · let b:=bail n e; let x:Openc (More n) e:=⟨profile U, U,H,by simpa⟩; obtain ⟨F,C,p,j,q⟩:= (show Solo _ _ _ _ from Q M n g).lib
   rw [show spar _ M U= _ from q x]; refine le_trans (sum_le_sum (g:=fun t=>saleM a C t i) (fun t _=>?_)) (j.cols i); rw [Matrix.sum_apply]; exact (norm_sum_le ..).trans (sum_le_sum (fun S _=> ((p S).expo _ _ |>.bounded x).trans (le_mul_of_one_le_left ((p S).nonn _ i) (rent_one h.le S))))
 intro n g U V u v M d z y s t; exact wave_help (Q M n g|>.lib) h l d U V u v _ y s t z (mem_singleton_self _)
end YM.CF.Pannier.Chancel