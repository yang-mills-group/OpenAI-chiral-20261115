import YM.SU5.FiniteGaugeData.CodaT.Lyra
import YM.SU5.FiniteGaugeData.Cuprite.Fist
/-! # Sparsity ledger: called by MANY body stamps.
 No uniform HS of the unregularized Gram any further than one power needed here.
 WP23.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.flexible false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 420000
noncomputable section
namespace YM.CF.Fock.Reduction
open Function Filter Finset Brique NormedSpace MeasureTheory Pastry Scree Cascade Hutch Drama
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology
attribute [local instance] opCStarAlgebra
namespace Dinar
variable {n:Type*} [Fintype n]
section common
variable [DecidableEq n]{A T B P Y S D:Op n}{a r b:ℝ}
abbrev Trunk(A:Op n)(t:ℝ):Prop:= ∀ X:Op n, ‖X‖≤1 → |TrR (A*X)|≤t
namespace Trunk
variable (h:Trunk A a)(u:Trunk B b)
include h
lemma nn : 0≤a:= le_trans (abs_nonneg _) (h 0 (by simp))
lemma reach(X:Op n) : |TrR (A*X)|≤ ‖X‖*a:=by
 by_cases q:X=0
 · simp [q, TrR]
 let c:= ‖X‖⁻¹; have he: 0<‖X‖:= norm_pos_iff.mpr q; have ha:0<c:= inv_pos.mpr he
 let Y:=c • X; have hr:‖Y‖=1:=by rw [show Y=c • X from rfl,norm_smul,Real.norm_of_nonneg ha.le, show c*‖X‖=1 from inv_mul_cancel₀ he.ne']; -- tune
 have hv:=h Y hr.le; change |TrR (A*(c • X))|≤ a at hv; rw [Algebra.mul_smul_comm,TrR_smul,abs_mul,abs_of_nonneg ha.le] at hv
 have hx:c*|TrR (A*X)|≤c*(‖X‖*a):=hv.trans_eq (by rw [←mul_assoc, show c*‖X‖=1 from inv_mul_cancel₀ he.ne',one_mul]); exact le_of_mul_le_mul_left hx ha
lemma grist(u:Trunk B b) : Trunk (A+B) (a+b):=by intro X l; rw [add_mul,TrR_add]; exact (abs_add_le ..).trans (add_le_add (h _ l) (u _ l))
lemma neg : Trunk (-A) a:=by
 intro X l; rw [neg_mul]; unfold TrR; rw [Matrix.trace_neg]; change |-TrR (A*X)|≤ a; rw [abs_neg]; exact h X l
lemma stars : Trunk (star A) a:=by intro X l; rw [←TrR_star,star_mul,star_star,TrR_comm]; exact h _ ((norm_star _).trans_le l)
lemma rit(p: ‖B‖≤ b): Trunk (A*B) (a*b):=by
 intro X l; rw [mul_assoc]; refine (reach h _).trans ?_; rw [mul_comm a]; exact mul_le_mul_of_nonneg_right ((norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) l).trans p)) (nn h) -- tune
lemma lft (p: ‖B‖ ≤ b): Trunk (B*A) (a*b):=by
 have hz:= stars (rit (stars h) ((norm_star _).trans_le p)); rwa [star_mul,star_star,star_star] at hz
lemma advance_v (p:a≤ b): Trunk A b:=fun X l=>(h X l).trans p
omit h
lemma nil_x : Trunk (0:Op n) 0:=by simp [Trunk,TrR]
lemma from_kg (h: kg A ≤ r)(p:0<a): Trunk A (a*Fintype.card n + a⁻¹*r):=by
 intro X l; refine (TrR_c p).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr p.le))); exact (kg_b ..).trans ((mul_le_of_le_one_right (kgN _) (by nlinarith [norm_nonneg X])).trans h)
lemma twist (V: UNI n) (h:Trunk A a): Trunk (CF.twist V A) a:=by
 intro X l; obtain ⟨Y,rfl⟩:=(CF.twist V).surjective X; change |TrR (CF.twist V A * CF.twist V Y)|≤a; change ‖CF.twist V Y‖≤1 at l; rw [←map_mul,TrR,trace_twist]; rw [twist_norm] at l; exact h Y l
end Trunk
abbrev cellZ (A:Op n)(i:n):ℝ:=‖acts A (basisKet i)‖
lemma cellZ_nn(A:Op n)(i:n):0≤cellZ A i:= norm_nonneg _
lemma cellZ_norm(A:Op n)(i:n): cellZ A i ≤ ‖A‖:= ((acts A).le_opNorm _).trans_eq (by rw [show ‖basisKet i‖=(1:ℝ) from by simp [basisKet],mul_one]; rfl)
lemma cellZ_mul (A B:Op n)(i:n):cellZ (A*B) i ≤ ‖A‖*cellZ B i:= by unfold cellZ; rw [act_mul]; exact (acts A).le_opNorm _
lemma cellZ_add(A B:Op n)(i:n): cellZ (A+B) i ≤ cellZ A i+cellZ B i:=by unfold cellZ; rw [act_add]; exact norm_add_le ..
lemma cellZ_sub(A B:Op n)(i:n):cellZ (A-B) i ≤ cellZ A i+cellZ B i:=by unfold cellZ; rw [act_sub]; exact norm_sub_le ..
lemma cellZ_neg(A:Op n)(i:n):cellZ (-A) i=cellZ A i:=by unfold cellZ; rw [act_neg,norm_neg]
abbrev cellU (S:Finset n) (A:Op n)(t:ℝ):Prop:=∀ i∈S,cellZ A i≤ t
namespace cellU
variable {L:Finset n}(h:cellU L A a)(u:cellU L B b)
include h
lemma mono(v:a≤b):cellU L A b:= fun _ e=>(h _ e).trans v
lemma trim{K:Finset n}(v:K⊆L):cellU K A a:= fun i l=>h i (v l)
lemma blend(u:cellU L B b) :cellU L (A+B) (a+b):=fun i l=>(cellZ_add ..).trans (add_le_add (h i l) (u i l))
lemma offset_cost(u:cellU L B b) :cellU L (A-B) (a+b):=fun i l=>(cellZ_sub ..).trans (add_le_add (h i l) (u i l))
lemma hegemon (l: ‖B‖≤b):cellU L (B*A) (b*a):=fun i v=>(cellZ_mul ..).trans (mul_le_mul l (h i v) (cellZ_nn ..) ((norm_nonneg _).trans l))
lemma robe_neg :cellU L (-A) a:= fun i v=> (cellZ_neg ..).trans_le (h i v)
lemma kg_core : kg (A*cutM L) ≤ a^2*L.card:=by
 rw [kg_I,←sum_subset (subset_univ L) (f:=fun i:n=> ‖acts (A*cutM L) (basisKet i)‖^2) ?_]; refine (sum_le_sum (g:=fun _=>a^2) ?_).trans_eq ?_
 · intro i v; rw [act_mul,cut_basis,if_pos v]; exact pow_le_pow_left₀ (norm_nonneg _) (h i v) _
 · rw [sum_const,nsmul_eq_mul,mul_comm]
 intro i _ v; rw [act_mul,cut_basis,if_neg v,map_zero,norm_zero]; norm_num
lemma trunk : Trunk (A*cutM L) (a*L.card):=by
 intro X v; rw [TrR_comm _ X,←mul_assoc]; set F:=(X*A)*cutM L; refine (trace_diag F).trans ?_; unfold LDiag; rw [←sum_subset (subset_univ L) (f:=fun i:n=> ‖F i i‖) ?_]; refine (sum_le_sum (g:=fun _=>a) ?_).trans_eq ?_
 · intro i e; rw [basis_b F]; refine (norm_inner_le_norm ..).trans ?_; rw [show ‖basisKet i‖=(1:ℝ) from by simp [basisKet], one_mul,show F=(X*A)*cutM L from rfl,act_mul,cut_basis,if_pos e]; simpa only [one_mul] using (hegemon h v i e) -- F set rw bug
 · rw [sum_const,nsmul_eq_mul,mul_comm]
 · intro i _ e; rw [basis_b F i]; unfold F; rw [act_mul,cut_basis,if_neg e,map_zero,inner_zero_right,norm_zero] -- set
omit h in
lemma of_norm (h:‖A‖≤a):cellU L A a:=fun i _=>(cellZ_norm ..).trans h
end cellU
lemma kg_negA(A:Op n):kg (-A)=kg A:=by unfold kg; rw [star_neg,neg_mul_neg]
lemma kg_rit(h:kg A≤r)(p:‖B‖≤b):kg (A*B) ≤ r*b^2:= (kg_b ..).trans (mul_le_mul h (pow_le_pow_left₀ (norm_nonneg _) p _) (sq_nonneg _) ((kgN _).trans h))
lemma kg_lft(h:kg A≤r)(p:‖B‖≤b):kg (B*A)≤r*b^2:=by rw [← kgt,star_mul]; exact kg_rit ((kgt _).trans_le h) ((norm_star _).trans_le p)
lemma kg_plus(h:kg A≤r)(p:kg B≤b):kg (A+B) ≤2*(r+b):=(kgs ..).trans (mul_le_mul_of_nonneg_left (add_le_add h p) zero_le_two)
lemma kg_doff(h:kg A≤r)(p:kg B≤b):kg (A-B)≤2*(r+b):=by rw [sub_eq_add_neg]; apply kg_plus h ((kg_negA _).trans_le p)
/-- Combine everywhere nuclear expenditure with Schatten regular-flag expense. -/
structure Priced(A:Op n)(t k:ℝ):Prop where
 nu: Trunk A t
 sc : kg A ≤ k
namespace Priced
variable {e c d l:ℝ}(h:Priced A a b)(g:Priced B c d)
include h
lemma monotoneP (p:a≤c)(v:b≤d): Priced A c d:=⟨Trunk.advance_v h.nu p,h.sc.trans v⟩
lemma plusP(g:Priced B c d): Priced (A+B) (a+c) (2*(b+d)):=⟨Trunk.grist h.nu g.nu,kg_plus h.sc g.sc⟩
lemma negativeP: Priced (-A) a b:=⟨Trunk.neg h.nu,(kg_negA _).trans_le h.sc⟩
lemma subP(g:Priced B c d): Priced (A-B) (a+c) (2*(b+d)):=by rw [sub_eq_add_neg]; exact h.plusP g.negativeP
lemma rP(p: ‖B‖≤c): Priced (A*B) (a*c) (b*c^2):=⟨Trunk.rit h.nu p,kg_rit h.sc p⟩
lemma lP(p:‖B‖≤c): Priced (B*A) (a*c) (b*c^2):=⟨Trunk.lft h.nu p,kg_lft h.sc p⟩
lemma starP :Priced (star A) a b:=⟨Trunk.stars h.nu,(kgt _).trans_le h.sc⟩
lemma twistP (V:UNI n):Priced (twist V A) a b:=⟨Trunk.twist V h.nu,by unfold kg; rw [←map_star,←map_mul,trace_twist]; exact h.sc⟩ -- tune
omit h
lemma fromKg(h:kg A ≤ r)(p:0<a): Priced A (a*Fintype.card n+a⁻¹*r) r:=⟨Trunk.from_kg h p,h⟩
lemma curtain{L:Finset n}(h:cellU L A a): Priced (A*cutM L) (a*L.card) (a^2*L.card):=⟨cellU.trunk h,cellU.kg_core h⟩
end Priced
end common
-- Determinant price convenience
section
variable [DecidableEq n]{A B P:Op n}{a b:ℝ}
lemma rue_fix(h:lit A)(u:lit B)(v:‖B⁻¹‖≤b)(q:Trunk (A-B) a):rueD A≤rueD B+b*a:=by
 have he:= route_log h u; rw [TrR_comm] at he; exact he.trans (add_le_add le_rfl ((abs_le.mp ((Trunk.reach q _).trans (mul_le_mul_of_nonneg_right v (Trunk.nn q)))).2))
lemma rue_pair(h:lit A) (u:lit B): rueD (A*B)=rueD A+rueD B:=by
 unfold rueD; rw [Matrix.det_mul,norm_mul]; exact Real.log_mul (norm_ne_zero_iff.mpr (def_beam h).ne') (norm_ne_zero_iff.mpr (def_beam u).ne')
lemma rue_inv (h:lit A): rueD A⁻¹ = -rueD A:=by unfold rueD; rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,norm_inv, Real.log_inv]
-- Aux star projection income
lemma TrR_proj (h:IsStarProjection P)(A:Op n): TrR (P*A)=TrR (P*A*P):=by conv_rhs=> rw [TrR_comm,←mul_assoc,h.1]
lemma TrR_proj_le(h:IsStarProjection P)(l:A≤B): TrR (P*A) ≤ TrR (P*B):=by rw [TrR_proj h, TrR_proj h B]; exact TrR_le (IsSelfAdjoint.conjugate_le_conjugate l h.2)
-- eig-price. none of it needs det unit threshold.
lemma core_law (h:IsStarProjection P)(v:Trunk B b)(hp:‖A‖≤1)(r:kg B≤a):TrR (P*(star (A+B)*(A+B)-1)) ≤ b + b + a:=by
 have he:star A*A≤1:= by
    apply le_trans (CStarAlgebra.star_mul_le_algebraMap_norm_sq ..); -- syntax
    rw [←map_one (algebraMap ℝ (Op n))]; apply algebraMap_mono _; nlinarith only [norm_nonneg A,hp]
 have hh: TrR (P*(star A*A-1)) ≤ 0:=by
    simpa only [mul_zero,TrR,Matrix.trace_zero,Complex.zero_re] using (TrR_proj_le h (sub_nonpos.mpr he)); -- `TrR`
 have ht: TrR (P*(star A*B)) ≤ b:= by
    rw [←mul_assoc,TrR_comm]; exact (abs_le.mp (v (P*star A) (by exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (h.norm_le _)).trans ((norm_star _).trans_le hp))))).2 -- nonempty tune
 have hc: TrR (P*(star B*A)) ≤ b:= by rw [←TrR_star (P*_ ),star_mul,star_mul,star_star,h.2,TrR_comm]; exact ht
 have hk: TrR (P*(star B*B)) ≤ a:= by
    rw [TrR_comm P]; -- positive increments
    rw [TrR_comm _ P]; refine le_trans ?_ r; -- show equals kg(BP) exactly ≤ kg B by oper
    have he: TrR (P*(star B*B))=kg (B*P):=by rw [TrR_proj h]; unfold kg; rw [star_mul,h.2]; simp only [mul_assoc]
    rw [he]; simpa only [one_pow,mul_one] using kg_rit (le_refl (kg B)) (h.norm_le _)
 rw [show star (A+B)*(A+B)-1=(star A*A-1)+(star A*B)+(star B*A)+(star B*B) by simp only [star_add,add_mul,mul_add]; abel,mul_add,mul_add,mul_add,TrR_add,TrR_add,TrR_add]; exact (add_le_add (add_le_add ((add_le_add hh ht).trans_eq (zero_add _)) hc) hk)
lemma fooP (U:UNI n)(S:Finset n)(d:n→ℝ): TrR ((twist U (cutM S))*spectral U d)= ∑ i∈ S,d i:=by
 -- filter simpl
 unfold spectral; rw [←map_mul]; unfold TrR; rw [trace_twist,cutM,Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,Complex.re_sum,← sum_subset (subset_univ S) (f:=fun i:n=> (((if i∈S then 1 else 0):ℂ)*(d i:ℂ)).re)]; -- notation may defeq
 · exact sum_congr rfl fun i v=>by rw [if_pos v,one_mul]; rfl
 intro i _ v; rw [if_neg v,zero_mul]; rfl
end
section
variable [LinearOrder n]{A B P:Op n}{a b:ℝ}
lemma jewel(p:∀ Q:Op n,IsStarProjection Q → TrR (Q*(star A*A-1))≤a): ‖quant A‖ ≤ Real.exp (a/2):=by
 let C:=star A*A; have h:0≤C := star_mul_self_nonneg _; obtain ⟨U,d,H⟩:= spectral_exists C (IsSelfAdjoint.of_nonneg h); rw [H] at h; let D:= spectral U d; have hx:0≤d:=by rw [←spectral_zero U] at h; exact (spectral_le U ..).mp h
 have he(S:Finset n): ∑ i∈S,(d i-1) ≤ a:=by
    have he:= p _ ((cutM_idp S).map (twist U)); let T:= twist U (cutM S); change TrR (T*(C-1))≤ _ at he; rw [H, ← spectral_one U,spectral_sub] at he; rwa [fooP U S] at he -- tune
 have hp: ‖star (quant A)*(quant A)‖ ≤ Real.exp a:=by
    rw [←quant_star,←quant_mul]; change ‖quant C‖ ≤_; rw [H,spectral,quant_twist,quant_diag,twist_norm,Matrix.l2_opNorm_diagonal]; apply (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).mpr; intro i; change ‖∏ j∈i,(d j:ℂ)‖≤_; rw [norm_prod]; let f(j:n):= d j-1
    apply (prod_le_prod (g:=fun j=>Real.exp (f j)) (fun _ _=> norm_nonneg _) ?_).trans; swap; · intro j l; rw [Complex.norm_of_nonneg (hx j)]; exact (by unfold f; have h:= Real.add_one_le_exp (d j-1); linarith)
    rw [←Real.exp_sum]; exact Real.exp_monotone (he i)
 have hx:Real.exp a=(Real.exp (a/2))^2:=by rw [sq, ←Real.exp_add, add_halves]
 rw [hx,CStarRing.norm_star_mul_self] at hp; nlinarith only [hp,norm_nonneg (quant A),Real.exp_pos (a/2)]
lemma volupt(p:Priced B a b)(h:‖A‖≤1): ‖quant (A+B)‖ ≤ Real.exp (a+b/2):= (jewel (a:=a+a+b) (A:=A+B) fun _ o=>core_law o p.nu h p.sc).trans_eq (by rw [show (a+a+b)/2=a+b/2 by ring]) -- `$‖..≤exp`,
end
end Dinar
end YM.CF.Fock.Reduction
