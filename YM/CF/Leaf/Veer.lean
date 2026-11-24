import YM.CF.Leaf.Milt
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Leaf
open Function Filter Topology Lattice Finset Palot Cadre PowerSeries
open scoped Classical Topology
variable {A:Type*}[Fintype A][DecidableEq A]{B:Type*}[AddCommMonoid B]
variable (o:A)(F:leaf A→ PS)(P: leaf A→ℝ)(X:leaf A)(y z s a b R K N0 N1 N2:ℝ)(v:leaf A→ℝ)
abbrev μhcp (s a c d e:ℝ):= d*a+e*a*a+(c+2*a*d)*(s*a)
namespace Tax_R
variable {F P v} {ℓ w' s a c d e b':ℝ}(T:Tax_R F P v b' ℓ w' a c d e)
include T
lemma kite(X:leaf A): Summable fun i:ℕ=> (2:ℝ)^i*coeff i (F X):=by
 let V:=loom_v ℓ w' v 2; have ht: 0<V X:=Real.exp_pos _; obtain ⟨t,y⟩:=X.property
 have hp(i:ℕ):mintL i 2 (F X) ≤ a/V X:= (le_div_iff₀ ht).mpr (le_trans (single_le_sum (fun i' (_:i'∈spark t)=>mul_nonneg ((T.grade i').negℜ (2:ℝ) (by norm_num) i) (show 0 ≤V i' from Real.exp_pos _|>.le)) (show X∈spark t from mem_filter.mpr ⟨mem_univ _,y⟩)) (ρlife T t 2 (by norm_num) i).le)
 refine summable_of_sum_range_le (c:= max 0 (a/V X)) (fun i=>mul_nonneg (by positivity) (T.grade _ _)) (fun i=>?_); cases i; · simp
 exact (hp _).trans (le_max_right ..)
variable {r:ℝ}(hp:0≤r)(hμ:r+1 ≤ ℓ-w')
include hp hμ
lemma mint_V(o:A)(i:ℕ) : let X:=loom_v r 0 v 0; let V:=ϕV F 1 i; nook (mintL3 P V * X) o ≤ μhcp b' a c d e:=by
 intro X V; let Y:=loom_v ℓ w' v 1; have hx:0 ≤ X:=fun t=>Real.exp_pos ..|>.le; have hv0:V≥0:=fun i=> (T.grade _).negℜ _ zero_le_one _
 have hp':r ≤ ℓ-w'*1:=by linarith
 have hm:Y ≤ loom_v ℓ w' v 0:= tap ℓ w' v T.veil T.vita.le zero_le_one
 have hg:X≤ Y:=fun i=>Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by rw [zero_mul,sub_zero]; exact hp') (zero_le_one.trans (T.veil.pos _)))
 have hu:0 ≤ V*X:=mul_nonneg hv0 hx; have hl:T.grade=T.grade:=rfl
 have hv(j):nook (V*Y) j ≤ a:=(ρlife T _ 1 (by norm_num) i).le
 have hc(j): nook (V*X) j ≤ a:=le_trans (sum_le_sum fun i _=> (show V*X ≤ V*Y from mul_le_mul_of_nonneg_left hg hv0) i) (hv j)
 have hZ:0 ≤ P:=T.merits; have he:P*X ≤ P*loom_v ℓ w' v 0:=mul_le_mul_of_nonneg_left (hg.trans hm) hZ
 have hr(j:A):nook (P*X) j ≤ c:= (sum_le_sum fun X _=> he X).trans (T.cash _)
 have hd(j:A):shelfR (P*X) j ≤ d:=(sum_le_sum (fun i _=> mul_le_mul_of_nonneg_right (he i) (Nat.cast_nonneg _))).trans (T.town _)
 have hh:Hiκ P X o≤e:= (sum_le_sum (fun i _=>mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (he i) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))).trans (T.bill _)
 let S:= V*X; have hb:0 ≤ b':=T.height
 have hs:shelfR (V*X) o ≤ b'*a:=by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (hv o) T.height); unfold shelfR nook; rw [mul_sum]; apply sum_le_sum; intro j h
    have he: v j * X j ≤Y j:=by
       have ht:v j ≤ Real.exp (v j):=le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp _); refine (mul_le_mul_of_nonneg_right ht (hx j)).trans ?_ ; unfold X Y loom_v; rw [←Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [T.veil.pos j]
    apply (mul_le_mul_of_nonneg_left (T.veil.rate j) (hu j)).trans; refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (hv0 j)) hb); change V j*X j*_ ≤ _; exact le_of_eq (by ring)
 have hU:=meet_K v T.veil r 0 0 (by simpa);
 have h1:= (bud_V o P V X hZ hv0 hx hU hc).trans (add_le_add (mul_le_mul_of_nonneg_right (hd o) T.ignite.le) ((ζpay _ _ (mul_nonneg T.merits hx) hu c hr o).trans (mul_le_mul_of_nonneg_right hs T.ask2))) -- pi nonneg
 have hX(i:leaf A):0≤ HiΦ P X i:=mul_nonneg (mul_nonneg (hZ _) (hx _)) (Nat.cast_nonneg _)
 have h2:= (trio_X o P V X hZ hv0 hx hU hc T.ignite.le).trans (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hh T.ignite.le) T.ignite.le) (mul_le_mul_of_nonneg_left ((ζpay _ _ hX hu d hd o).trans (mul_le_mul_of_nonneg_right hs T.ask)) (mul_nonneg (by norm_num) T.ignite.le)))
 unfold mintL3; rw [add_mul]; refine le_trans ?_ ((add_le_add h1 h2).trans_eq (by unfold μhcp; ring)); unfold nook; rw [←sum_add_distrib]; rfl
-- remainder χ holder PS.P.Shift.F
variable (R:leaf A→ PS)(hR:∀ X,cent (R X))(qr:∀ X:leaf A, coeff 0 (R X)=0∧∀ i:ℕ,coeff i (derivative ℝ (R X)) ≤ coeff i (ΦD F P X))
include hR qr
lemma era_V(o:A)(i:ℕ): nook (ϕV R 1 i * loom_v r 0 v 0) o ≤ μhcp b' a c d e:=by
 let L:=loom_v r 0 v 0; let U:=mintL3 P (ϕV F 1 i); have ht(X:leaf A): mintL i 1 (R X)≤ U X:=by
    apply le_trans ((hR X).kind (Nat.le_succ _) zero_le_one); apply le_trans _ ((Cadre.trend zero_le_one ((qr X).2) i).trans (Φcash F P X 1 i T.grade T.merits zero_le_one))
    unfold mintL; rw [sum_range_succ',one_pow,one_mul,(qr _).1,add_zero]; apply sum_le_sum; intro j _; rw [one_pow,one_pow,one_mul,one_mul, coeff_derivative]; exact le_mul_of_one_le_right (hR _ _) (le_add_of_nonneg_left (Nat.cast_nonneg _))
 exact le_trans (sum_le_sum fun X _=>mul_le_mul_of_nonneg_right (ht X) (show 0 ≤ L X from Real.exp_pos _|>.le)) (mint_V T hp hμ o i)
lemma born(X:leaf A) : Aqua (R X):=by
 obtain ⟨t,p⟩:=X.property; let L:= loom_v r 0 v 0; have hz:0 < L X:= Real.exp_pos _; let U:=μhcp b' a c d e; have ht(i): mintL i 1 (R X)≤ U/L X:=(le_div_iff₀ hz).mpr ((single_le_sum (fun i' (_:i'∈spark t)=>mul_nonneg ((hR i').negℜ _ zero_le_one i) (show 0≤ L i' from Real.exp_pos _|>.le)) (show X∈spark t from mem_filter.mpr ⟨mem_univ _,p⟩)).trans (era_V T hp hμ R hR qr t _))
 refine summable_of_sum_range_le (c:= max 0 (U/L X)) (fun _=>norm_nonneg _) (fun i=>?_); cases i; · simp
 rename_i i; refine le_trans ?_ ((ht i).trans (le_max_right ..)); exact sum_le_sum fun j _=>le_of_eq (by rw [Real.norm_of_nonneg (hR _ _),one_pow,one_mul])
lemma toll_V(o:A) : nook ((hitU ∘ R)* loom_v r 0 v 0) o ≤ μhcp b' a c d e:=by
 refine le_of_tendsto (show Tendsto (fun n=> nook (ϕV R 1 n*loom_v r 0 v 0) o) atTop _ from ?_) (Eventually.of_forall fun i=>era_V T hp hμ R hR qr o i); apply tendsto_finsetSum; intro i _; apply Tendsto.mul _ tendsto_const_nhds; have hp':= (((born T hp hμ R hR qr i).of_norm).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1); change Tendsto (fun n=> ϕV R 1 n i) atTop _; simpa only [ϕV,mintL,one_pow,one_mul, Function.comp_def,add_comm 1] using hp'
end Tax_R
end YM.CF.Leaf
