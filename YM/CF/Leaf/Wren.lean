import YM.CF.Leaf.Wish
import Mathlib.Analysis.Calculus.SmoothSeries
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Leaf
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre PowerSeries Vow
open RG
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
variable {ι:Type*}[LinearOrder ι][Fintype ι]{A:Type*}[Fintype A][DecidableEq A]{B:Type*}[AddCommMonoid B]
variable (Q:FC ι)(FF:PowerSeries (↥(Dough ι)))
section Ω
variable {U:Type*}[NormedCommRing U][NormedAlgebra ℝ U][CompleteSpace U](F:PowerSeries U)
abbrev duty_H(F:PowerSeries U):Prop:=Summable fun i:ℕ=> (2:ℝ)^i * ‖coeff i F‖
abbrev read_Y(P:PowerSeries U)(t:ℝ) := ∑' i:ℕ, t^i • coeff i P
lemma po_Y(i:ℕ): (i:ℝ)*(3/2:ℝ)^(i-1) ≤(2:ℝ)^i *4:=by
 induction i with
 |zero=>norm_num
 |succ i ih=> by_cases h:i<3; · interval_cases i <;> norm_num
              have hu: i-1+1=i:=by omega
              have hp: (3/2:ℝ)^i=(3/2:ℝ)^(i-1)*(3/2:ℝ):=by rw [←pow_succ,hu]
              simp only [add_tsub_cancel_right,pow_succ, Nat.cast_add,Nat.cast_one]; have hx:(3:ℝ) ≤ i:=by exact_mod_cast (by omega: 3≤ i)
              have he: ((i:ℝ)+1)*(3/2) ≤2*i:=by linarith
              calc _ = (((i:ℝ)+1)*(3/2))*(3/2:ℝ)^(i-1):=by rw [hp]; ring
                   _ ≤ (2*i:ℝ)*(3/2:ℝ)^(i-1):=mul_le_mul_of_nonneg_right he (by positivity)
                   _ ≤ _:=by linarith
variable (t:ℝ)(ht:|t|< 3/2)(f:duty_H F)
include ht f
lemma go_p : Summable fun i=> ‖t^i • coeff i F‖:=by
 refine Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>?_) f; rw [norm_smul,norm_pow]; exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (show ‖t‖≤2 from (by rw [Real.norm_eq_abs]; linarith)) _) (norm_nonneg _)
lemma hf_v : Summable (fun i=> t^i • coeff i (derivative _ F)) ∧ HasDerivAt (read_Y F) (read_Y (derivative _ F) t) t:=by
 let D:= {x:ℝ| |x|<3/2}; have hx:D=Metric.ball 0 (3/2:ℝ):=by ext i; simp [D,Metric.mem_ball,dist_zero_right,Real.norm_eq_abs]
 let L(i:ℕ)(t:ℝ):=t^i • coeff i F; let v(i:ℕ)(t:ℝ):=((i:ℝ)*t^(i-1)) • coeff i F
 have hp(i:ℕ)(t:ℝ): HasDerivAt (L i) (v i t) t:=((hasDerivAt_pow i t).smul_const (coeff i F)) -- syntax
 let W(i:ℕ):=4*((2:ℝ)^i * ‖coeff i F‖); have hh:Summable W:=f.mul_left _
 have he(i:ℕ)(x:ℝ)(q:x∈ D): ‖v i x‖ ≤ W i:=by
    have hz: ‖x‖ ≤ 3/2:= show |x|≤ _ from le_of_lt q
    unfold v; rw [norm_smul,norm_mul,norm_pow,Real.norm_of_nonneg (Nat.cast_nonneg i)]; unfold W; exact (mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz _) (Nat.cast_nonneg i)).trans (po_Y i)) (norm_nonneg _)).trans_eq (by ring)
 have ht' := ht; change t∈D at ht'
 have hf:=hasDerivAt_tsum_of_isPreconnected hh (hx ▸ Metric.isOpen_ball) (hx ▸ (convex_ball (0:ℝ) (3/2)).isPreconnected) (fun i t' _=> hp i t') he ht' ((go_p F t ht f).of_norm) ht'
 have Hs:Summable fun i=> v i t:= (Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun i=>he i t ht') hh).of_norm
 have hr(i:ℕ):v (i+1) t=t^i • coeff i (derivative _ F):=by
    rw [coeff_derivative,mul_comm (coeff _ F),show (↑i+1: U)= (↑(i+1:ℕ)) by push_cast; rfl, ←nsmul_eq_mul,←Nat.cast_smul_eq_nsmul ℝ]; unfold v; rw [smul_smul,mul_comm]; simp
 refine ⟨?_,hf.congr_deriv ?_⟩
 · simp_rw [←hr]; exact (summable_nat_add_iff 1).mpr Hs
 unfold read_Y; simp_rw [←hr]; have he:=Hs.sum_add_tsum_nat_add 1; exact he.symm.trans (by simp [v])
omit ht f
end Ω
variable (F:PowerSeries (↥(Dough ι)))
lemma bum_L (F G:ℕ→ FC ι) (p:Summable fun i=>‖F i‖)(h:Summable fun i=>‖G i‖):let Φ:=fun i:ℕ=>∑ j∈antidiagonal i,bump (F j.1) (G j.2); Summable Φ ∧ ∑' i,Φ i = bump (∑' i,F i) (∑' i,G i):=by
 intro V; let f(n:ℕ):=∑ t∈antidiagonal n, F t.1*G t.2; let g(n:ℕ):=∑ t∈antidiagonal n,G t.1*F t.2; have he: V=f-g:=by
    funext n; unfold V bump; rw [sum_sub_distrib]; change _= f n - _; exact congrArg (f n-·) (by unfold g; exact Finset.Nat.sum_antidiagonal_swap (f:=fun p:ℕ×ℕ=> G p.1*F p.2)) -- tune swap syntax
 have hp:Summable f:= (summable_norm_sum_mul_antidiagonal_of_summable_norm p h).of_norm; have hu: Summable g:= (summable_norm_sum_mul_antidiagonal_of_summable_norm h p).of_norm; rw [he]; exact ⟨hp.sub hu,(show (∑' i,(f-g) i)=_ from (by change (∑' i,(f i-g i))=_; rw [hp.tsum_sub hu]; unfold bump; rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm p h,tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm h p]))⟩
lemma crave(A:FC ι)(U:ℕ→FC ι)(p:Summable fun i=>‖U i‖): let T:=fun i=>bump A (U i); (Summable fun i=>‖T i‖)∧∑' i,T i=bump A (∑' i,U i):=by
 intro T; let Z: FC ι→ₗ[ℝ] FC ι:={toFun:=bump A,map_add':=fun x y=>by unfold bump; rw [add_mul,mul_add]; abel,map_smul':=fun t x=>by unfold bump; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,smul_sub]; rfl}; let V:=Z.toContinuousLinearMap
 exact ⟨Summable.of_nonneg_of_le (fun i=>norm_nonneg _) (fun i=>V.le_opNorm (U i)) (p.mul_left _), (V.map_tsum p.of_norm).symm⟩
lemma εr (A B:FC ι)(t s:ℝ): bump (t • A) (s • B)=(t*s) • bump A B:=by unfold bump; simp only [Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,smul_sub]; rw [mul_comm t s]
lemma ride_h(p:duty_H F)(e:∀ i:ℕ, (coeff i (derivative _ F)).val=Sault.rind ((if i=0 then Q else 0)+bump Q (coeff i F).val+(∑ j∈ antidiagonal i,(2:ℝ)⁻¹ • bump (bump Q (coeff j.1 F).val) (coeff j.2 F).val)))(t:ℝ)(ht:|t|<3/2): (read_Y (derivative _ F) t).val=Sault.rind (Q+bump Q (read_Y F t).val+(2:ℝ)⁻¹ • bump (bump Q (read_Y F t).val) (read_Y F t).val):=by
 let S(i:ℕ):=(coeff i F).val; let T (i:ℕ):=t^i • S i; have hp:Summable fun i=>‖T i‖:=go_p F t ht p
 let V(i:ℕ):=bump Q (T i); let z:=crave (Q) T hp
 let Z(i):= ∑ j∈antidiagonal i,bump (V j.1) (T j.2); let W(i:ℕ):=if i=0 then Q else 0; have hb : Summable W:=summable_of_ne_finset_zero (s:={0}) (fun i v=>if_neg fun s=> v (mem_singleton.mpr s)); have hw:∑' i,W i=Q:=by rw [tsum_eq_single 0]; exact if_pos rfl; intro i p; exact if_neg p
 obtain ⟨h₁,h₂⟩:= bum_L V T z.1 hp
 let c:ℝ:=2⁻¹; let r:= (Pastry.cane ι).eval.toContinuousLinearMap.restrictScalars ℝ; let L:= (Dough ι).val.toLinearMap.toContinuousLinearMap
 have he(i:ℕ): L (t^i • coeff i (derivative _ F))= r ((W+V) i + c • Z i):=by
    change t^i • (coeff i (derivative _ F)).val= _; rw [show (coeff i (derivative _ F)).val=_ from e i,← rime_z]; -- tune
    suffices H:t^i • ((if i=0 then Q else 0)+bump Q (S i)+(∑ j∈ antidiagonal i,(2:ℝ)⁻¹ • bump (bump Q (S j.1)) (S j.2)))= (W+V) i + c • Z i from congrArg (fun v:FC ι=>r v) H -- may unknown
    rw [smul_add,smul_add,Pi.add_apply]; refine congrArg₂ (·+·) (congrArg₂ (·+·) ?_ ?_) ?_
    · unfold W; by_cases h:i=0 <;> simp [h]
    · have h:= εr Q (S i) 1 (t^i); rw [one_smul, one_mul] at h; exact h.symm
    unfold Z; rw [smul_sum,smul_sum]; apply sum_congr rfl; rintro ⟨x,y⟩ u; have hu':x+y=i:=mem_antidiagonal.mp u; dsimp only; rw [smul_comm (t^i), ←hu',pow_add]; have hx:= εr Q (S x) 1 (t^x); rw [one_smul,one_mul] at hx; unfold V T; rw [hx, εr]
 have hv: L (read_Y F t)=∑' i,T i:=L.map_tsum (go_p _ _ ht p).of_norm
 change L (read_Y (derivative _ F) t) = _; rw [read_Y,L.map_tsum (hf_v _ _ ht p).1]; simp_rw [he]
 have gu: Summable Z:= h₁; have hu: Summable V:=z.1.of_norm; let A(i:ℕ):= W i+V i+c • Z i; change ∑' i,r (A i)= r _; rw [← r.map_tsum (show Summable A from (hb.add hu).add (gu.const_smul c))]; apply congrArg r
 unfold A; rw [(hb.add hu).tsum_add (gu.const_smul c),hb.tsum_add hu,gu.tsum_const_smul c,hw,show ∑' i,Z i=_ from h₂, show ∑' i,V i=_ from z.2, ← hv]; rfl
end YM.CF.Leaf
