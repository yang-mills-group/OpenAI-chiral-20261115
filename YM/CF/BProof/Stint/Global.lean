import YM.CF.BProof.Stint.Area

/-! Globalize B-Pproj norm tests with uniform margin. See Stint/Area. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Stint
open Function Filter Fock Finset Branch Lattice Tenant
open scoped Topology BigOperators Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I Z G:Type*}[Fintype I][DecidableEq I] [Nonempty I] {s:Side}{b:Stage (Site s) I Z G} {A:Op I}
theorem actuarial (A:Op I)(x:Ket I): ‖acts A x‖≤ ‖A‖*‖x‖:=by unfold acts; rw [←Matrix.l2_opNorm_toEuclideanCLM]; exact ContinuousLinearMap.le_opNorm ..
lemma norm_bound_act {a:ℝ}(h:0≤a)(g:∀ x:Ket I, ‖acts A x‖≤a * ‖x‖): ‖A‖≤a := by rw [← Matrix.l2_opNorm_toEuclideanCLM]; exact ContinuousLinearMap.opNorm_le_bound _ h g
lemma range_crop {w:ℕ} (h:FiniteOp b w A)(g:b.F=terr s)(r:ℕ)(z:Site s): let V:=fun r=>strip b (bay (terr s) z r); V r * A = V r*A*V (r+w):=by
 intro V; ext i j; rw [show V= _ from rfl,stripR] -- tune
 split; rfl; rw [stripL]; split; swap; rfl; rename_i t u; apply h i j; by_contra! e; apply t; rw [g] at e; apply (bay_mem _).mpr; exact ((terr s).tri ..).trans (Nat.add_le_add ((bay_mem _).mp u) e) -- name
lemma rice {a:ℝ} {w:ℕ} (h:FiniteOp b w A)(g:b.F=terr s)(r:ℕ)(z:Site s) (q:‖A*strip b (bay (terr s) z (r+w))‖≤a)(x:Ket I): let V:=fun r=>strip b (bay (terr s) z r); ‖acts (V r) (acts A x)‖≤a*‖acts (V (r+w)) x‖:=by
 intro V; let L:=V r; let T:=V (r+w); have ht:T*T=T:=(cutM_idp _).isIdempotentElem; have hu:L*A*T=L*A:= (range_crop h g r z).symm
 let K:=L*A*T; have hv: acts L (acts A x)= acts K (acts T x):=by rw [←act_mul,←act_mul,show K*T=L*A from hu ▸ hu] -- tune
 rw [hv]; refine (actuarial _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)); unfold K; rw [mul_assoc]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (stripPaid ..)).trans q)
lemma crop_bound {a c:ℝ} {r w:ℕ} (ha:0≤c)(h:FiniteOp b w A)(g:b.F=terr s)(q:∀ z, ‖A*strip b (bay (terr s) z (r+w))‖≤a)(u:a^2 * area s (r+w) ≤ area s r *c^2): ‖A‖≤c:=by
 apply norm_bound_act ha; intro x; apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1; apply le_of_mul_le_mul_left _ (area_pos s r)
 rw [←areas b r,mul_pow,←mul_assoc]; have hx:∑ z:Site s, ‖acts (strip b (bay (terr s) z r)) (acts A x)‖^2 ≤ ∑ z:Site s,(a*‖acts (strip b (bay (terr s) z (r+w))) x‖)^2:= Finset.sum_le_sum (fun i _=>pow_le_pow_left₀ (norm_nonneg _) (rice h g r i (q i) x) _)
 apply hx.trans; simp_rw [mul_pow]; rw [←mul_sum,areas,←mul_assoc]; exact mul_le_mul_of_nonneg_right u (sq_nonneg _)
lemma crop_pay {a c:ℝ}(ha:0<a)(hv:a<c)(w:ℕ): ∃ K:ℕ,∀ s:Side,∃ r:ℕ,r+w≤K∧a^2*area s (r+w) ≤ area s r*c^2:=by
 let k:= (c/a)^2; have hh:a^2*k=c^2:=by unfold k; field_simp
 have he: 1<k:=one_lt_pow₀ ((one_lt_div ha).mpr hv) (by decide)
 obtain ⟨K,T⟩:=gentle he w; refine ⟨K,fun s=>?_⟩; obtain ⟨r,q,e⟩:=T s; exact ⟨r,q,(mul_le_mul_of_nonneg_left e (sq_nonneg a)).trans_eq (by rw [←mul_assoc,hh,mul_comm])⟩
lemma purchases {a c:ℝ} (ha:0≤a)(hp:a<c)(p:Pay) : ∃ K:ℕ, ∀ {I Z G: Type} [Fintype I] [Nonempty I] [DecidableEq I] [TopologicalSpace Z]{s:Side}{b:Stage (Site s) I Z G}{t v:Tag b}{A:Raw Z I}, Earn p t v A → b.F=terr s→ ∀ x:Z, (∀ z, ‖A x * strip b (bay (terr s) z K)‖≤a)→ ‖A x‖ ≤ c :=by
 obtain ⟨l,g,ht⟩:= exists_between hp; obtain ⟨k,hv,hk⟩:=exists_between ht; let d:= min (l-a) (c-k); obtain ⟨w,h⟩:= ((tailPaid p).eventually (gt_mem_nhds (show 0<d from lt_min (sub_pos.mpr g) (sub_pos.mpr hk)))).exists; obtain ⟨K,T⟩:= crop_pay (ha.trans_lt g) hv w; refine ⟨K,?_⟩; intro I Z G _ _ _ _ s b t v A P H x X; obtain ⟨R,S,u,L,q⟩:= P.holds; obtain ⟨r,hR,hx⟩:=T s
 let f:=lop R w x; have hy : ‖A x-f‖ ≤ d:= (tailEarn u L q w x).trans h.le
 have hw(z:Site s): ‖f * strip b (bay (terr s) z (r+w))‖≤ l:=by
    let U:=strip b (bay (terr s) z (r+w)); let p:=A x; have hl: ‖p*U‖≤a:= (strip_low_norm (show bay (terr s) z (r+w) ⊆ bay (terr s) z K from fun y k=> (bay_mem _).mpr (((bay_mem _).mp k).trans hR)) p).trans (X z)
    change ‖f*U‖≤_; rw [show f*U=p*U-(p-f)*U by rw [sub_mul,sub_sub_cancel]]; apply (norm_sub_le ..).trans; exact (add_le_add hl ((stripCheap ..).trans hy)).trans (by unfold d; grind)
 apply (norm_le_norm_sub_add _ f).trans; exact (add_le_add hy (crop_bound (ha.trans ((g.trans hv).le)) (lop_rad R S u x) H hw hx)).trans (by unfold d; grind) -- check direction
end YM.CF.BProof.Stint
