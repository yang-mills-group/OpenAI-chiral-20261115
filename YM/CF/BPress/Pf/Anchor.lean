import YM.CF.BPress.Pf.Frame
import YM.CF.BPress.Ledger
/-! Per-entry, in particular per-site performance by the supplied diagonal expansions. Can sum per-site traces for invariant sectors; covariance under true gauge, trace doesn't require invariant matrix pieces. Anchor sign for loss survives; will use in reference patch. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Spin Spin.Pledge Spin.Quad Spin.Cellar Spin.Cellar.Pass Helm Thera Bridge Branch Eye
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {I:Type}[Fintype I][LinearOrder I][Nonempty I]{P Q:Finset I}{A T K L B:Op I}{C C':ℝ→Op I}{r ε a:ℝ}
namespace Frame
lemma helm_conv (c:ℝ)(p:‖c⁻¹ • A-1‖ <1)(V:UNI I): helm c (twist V A)=twist V (helm c A):=by
 unfold helm; rw [←map_smul, show twist V _-1=twist V (c⁻¹ • A-1) from by rw [map_sub,map_one], reflect p,map_add,map_smul,map_one]
lemma trueH (h:ε • (1:Op I)≤ A)(t:A≤(3:ℝ) • (1:Op I))(p:0<ε)(q:ε≤1)(V:UNI I): (1/2:ℝ) • helm 3 (twist V A) = twist V ((1/2:ℝ) • helm 3 A):=by
 have ht:= Helm.affords p (q.trans_lt (by norm_num)) h t; rw [map_smul,helm_conv _ (ht.1.trans_lt ht.2)]
lemma staticH (h:‖T‖≤1)(V:UNI I): permit (twist V A) (twist V T)=twist V (permit A T):= by unfold permit; rw [show (1+star (twist V T)*twist V T)= twist V (1+star T*T) by simp only [map_add,map_mul,map_star,map_one]]; exact trueH (RealBook.embrace T h).1 (RealBook.embrace T h).2 zero_lt_one le_rfl _
lemma permit_f (V:UNI I)(R:IsStarProjection A)(S:TagG A T)(X: Pass (cutM P) (cutM Q) (shun I P Q) (mood A T) ε)(p:twist V (cutM P)=cutM P)(q:twist V (cutM Q)=cutM Q): permitX P (twist V A) (twist V T)=twist V (permitX P A T) ∧ permitY P Q (twist V A) (twist V T)=twist V (permitY P Q A T):=by
 let a:= mood A T; let P':=cutM P; let Q':=cutM Q; let T':=rent0 P' a; have h : mood (twist V A) (twist V T)=twist V a:=rotate_tilt R S 1 V; have ht: rent0 P' (twist V a) = twist V T':=by have he:=(comes V X 0 (by simp)).2.1; rw [p] at he; exact he
 have he:= Issued.price1 X.p X.a X.payP X.pos X.small; have hg:= Issued.price1 X.q X.r0.one_sub X.pay0 X.pos X.small
 unfold permitX permitY; rw [h,← p, ter_frame,p,ht, show 1-twist V T'=twist V (1-T') by rw [map_sub,map_one], ← q, ter_frame,q]; exact ⟨trueH he.1 he.2 X.pos X.small V,trueH hg.1 hg.2 X.pos X.small V⟩ -- p occurrences both issue tune
lemma billZ_f(V:UNI I)(X: Issued P Q A T C C' r ε)(p:twist V (cutM P)=cutM P)(q:twist V (cutM Q)=cutM Q): billZ P Q (twist V A) (twist V T) (congrC V (C 2))=twist V (billZ P Q A T (C 2)) :=by
 let K:=mood A T; let Z:=shun I P Q; let f:=twist V; let P':=cutM P; have ht:mood (twist V A) (twist V T)=twist V K:= rotate_tilt X.proj X.she 1 V
 let F:=rent0 P' K; let R:=ramp Z P' K; let A:=cutM Q
 have hu:=X.rails.gate0.shine V; have hv:rent0 P' (f K)=f F:=by have he:=(comes V X.rails 0 (by simp)).2.1; rw [p] at he; exact he
 have hh:ramp Z P' (f K)=f R:=by rw [ramp,hv,show Z*f F=f (Z*F) by rw [map_mul,s_fixed V p q]]; exact hu
 unfold billZ; rw [ht,hh,loss, X.drum.backB.lot,← map_neg, reflect (by rw [norm_neg]; exact Issued.normL X.drum.backB),map_smul]; rfl
end Frame

namespace Anchor
variable {G Y D:Type}[Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D G}
-- on any Stage.
def homeF (b:Stage Y I D G)(A:Op I)(o:Y): ℂ:=∑ i:I with b.home i=o,A i i
lemma act_here (A:Op I)(v:Y):homeF b A v=(strip b {v}*A).trace :=by unfold homeF Matrix.trace; simp [Matrix.diag,Branch.stripL, sum_filter]
lemma invariant (A:Op I)(v:Y)(σ:Tag b)(γ:G):homeF b (twist (σ.run γ) A) v=homeF b A v:=by
 rw [act_here,act_here,show strip b _*twist (σ.run γ) A=twist (σ.run γ) (strip b {v}*A) from ?_,trace_twist]; rw [map_mul,show twist _ (strip b {v})=strip b _ from ?_]; rw [twist_formula,← strip_tag,mul_assoc,(σ.run γ).property.2,mul_one]
lemma truth (b:Stage Y I D G)(A:Op I): A.trace= ∑ i:Y,homeF b A i:=by simp_rw [homeF,sum_filter]; rw [sum_comm]; simp; rfl
lemma sign (b:Stage Y I D G)(T:Op I)(v:Y)(A:Op I)(p:T≤A): (homeF b T v).re≤(homeF b A v).re:=by
 unfold homeF; simp_rw [Complex.re_sum]; refine sum_le_sum (fun i _=> ?_); have ht:= Quad.e_mono p (basisKet i); unfold Quad.energy at ht; simpa using ht

variable {b:Stage Y I D Empty}
structure Homes (P:Pledge)(b:Stage Y I D Empty)(F : Raw D I)(X: Y→ Seal Y→ D→ℂ)(B:Y→ Seal Y→ℝ):Prop where
 handles(o:Y)(t:Seal Y):Element b t (B o t) (X o t)
 pins{o t}:B o t≠ 0 → o ∈t
 purchases: YM.CF.BPress.Ledger.Cash (fun i:Y × Seal Y=>i.2) (fun i=>B i.1 i.2) P.rate P.price
 bill(o:Y)(t:D): homeF b (F t) o=∑ s:Seal Y,X o s t

theorem site (P:Pledge)(v:0≤a):∃ C:Pledge,∀ {I D Y: Type}[Fintype I][LinearOrder I][Nonempty I][Fintype Y][DecidableEq Y][TopologicalSpace D]{b:Stage Y I D Empty}{F:Raw D I}, Capacity b a→ P.Costs b F→ ∃ X B,Homes C b F X B:=by
 let M:=(∑' i:ℕ, Real.exp (-P.rate/2*i)*(a*((i:ℝ)+1)^4))*P.price; refine ⟨⟨P.rate/2,max 1 M,half_pos P.pos,lt_max_of_lt_left zero_lt_one⟩,?_⟩; intro I D Y _ _ _ _ _ _ b F p h
 obtain ⟨f,C,w,L,q⟩:=h; let H(o:Y):=univ.filter fun i:I=> b.home i=o; let B(o:Y)(t:Seal Y):=∑ i∈ H o,C t i i; have ht o s:0≤ B o s:=sum_nonneg (fun i _=> (w s).nonn i i); refine ⟨fun o s t=>homeF b (f s t) o,B,⟨fun o s=>?_ ,fun {o t} p=>?_, ⟨fun _=>ht _ _, fun i=>?_⟩,fun o t=>?_⟩⟩
 · refine ⟨ht o s,fun p=>?_,fun i x=> Empty.elim i, by unfold homeF; exact continuous_finsetSum _ fun i _=>(w s).cont.matrix_elem ..,fun i=>(norm_sum_le ..).trans (sum_le_sum (fun i' _=> ((w s).expo _ _).bounded i)),fun x y=>?_⟩
   · obtain ⟨i,v,h⟩:= exists_ne_zero_of_sum_ne_zero p; exact (((w s).expo _ _).triggered h).1
   unfold homeF B; rw [←sum_sub_distrib,sum_mul]; exact (norm_sum_le ..).trans (sum_le_sum fun i _=> ((w s).expo i i).variation x y)
 · obtain ⟨i,v,h⟩:= exists_ne_zero_of_sum_ne_zero p; rw [←(mem_filter.mp v).2]; exact (((w t).expo _ _).triggered h).2.1
 · let s := YM.CF.BPress.Ledger.score (fun i:Y × Seal Y=>i.2) (fun i=>B i.1 i.2) (P.rate/2) i; refine ⟨fun x=> ite_nonneg (mul_nonneg (Real.exp_pos _).le (ht ..)) le_rfl, (summable_of_finite_support (f:=s) (Set.toFinite _)),?_ ⟩; rw [tsum_fintype];
   change ∑ z: Y× Seal Y,s z ≤ max 1 M; have he(t:Seal Y): ∑ o:Y,B o t ≤ ledgerV (C t):=by
      unfold B H; simp_rw [sum_filter]; rw [sum_comm]; simp only [sum_ite_eq, mem_univ,ite_true]; exact sum_le_sum fun i _=> single_le_sum (fun j _=> (w t).nonn i j) (mem_univ i)
   apply le_trans ?_ ((tall w L P.pos p v i).trans (le_max_right ..)); rw [Fintype.sum_prod_type,sum_comm]; unfold hitE hit0 s; rw [sum_filter]; apply sum_le_sum; intro j _; unfold YM.CF.BPress.Ledger.score; by_cases h:i∈j; simp only [h,ite_true,← mul_sum]; exact mul_le_mul_of_nonneg_left (he j) (Real.exp_pos _).le; simp only [h,ite_false,sum_const_zero]; exact le_rfl
 rw [q]; unfold homeF; simp_rw [Matrix.sum_apply]; rw [sum_comm] -- tune
end Anchor
end YM.CF.BPress.Pf
