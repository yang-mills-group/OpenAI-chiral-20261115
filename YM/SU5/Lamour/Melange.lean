import YM.SU5.Lamour.Feast
/-!
# A matinee. localized Wick gauge. Individual normal order centered.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 180000
noncomputable section
namespace YM.CF.Lamour
open Fock Finset NormedSpace Flare Pannier.Chancel Velvet Pannier.Damask
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra
variable {I n ι:Type*}[LinearOrder n][Fintype n][Fintype I][LinearOrder I] (C A:I → FC n)(K: Op I)
structure Grant (S : Finset I)(v Y:ℝ)(X: FC n): Prop where
 bank: 0≤Y
 bill: ∀ (U:ℝ), 0 ≤ U→∀ L:FC n→ₗ[ℂ] Wave n,(∀ T⊆ S,‖L (wake C A K T)‖≤v^T.card*U)→ ‖L X‖≤ Y*U
variable {C A K}{U X Y: FC n}{S T W:Finset I}{z v w R B:ℝ}{P:Op I}
namespace Grant
lemma up (h:Grant C A K S v R X)(p:R≤z): Grant C A K S v z X:=⟨h.bank.trans p,fun t ht l u=>(h.bill t ht l u).trans (mul_le_mul_of_nonneg_right p ht)⟩
lemma sub (h:Grant C A K S v R X)(p:S ⊆ T): Grant C A K T v R X:=⟨h.bank,fun _ q l u=> h.bill _ q l (fun t e=>u t (Finset.Subset.trans e p))⟩
lemma plus(h:Grant C A K S v R X)(p:Grant C A K S v B Y): Grant C A K S v (R+B) (X+Y) :=by refine ⟨add_nonneg h.bank p.bank,fun i q L t=>?_⟩; rw [map_add,add_mul]; exact (norm_add_le ..).trans (add_le_add (h.bill _ q L t) (p.bill _ q L t))
lemma haze(h:Grant C A K S v R X)(z:ℂ): Grant C A K S v (‖z‖*R) (z•X) :=by refine ⟨mul_nonneg (norm_nonneg _) h.bank,fun i q L t=>?_⟩; rw [map_smul,norm_smul,mul_assoc]; apply mul_le_mul_of_nonneg_left (h.bill _ q L t) (norm_nonneg _)
lemma nil: Grant C A K S v 0 0:= ⟨le_rfl,fun _ _ l _=> by rw [map_zero,norm_zero,zero_mul]⟩
lemma one: Grant C A K S v 1 1:=⟨zero_le_one,fun _ _ l u=> by simpa using u ∅ (empty_subset _)⟩
lemma sumC (F:ι→FC n)(d:ι→ℝ)(S':Finset ι)(h:∀ i∈ S',Grant C A K S v (d i) (F i)): Grant C A K S v (∑ i∈ S', d i) (∑ i∈ S', F i):=by
 classical
 induction S' using Finset.induction_on with
 | empty=> simpa using Grant.nil (C:=C) (A:=A) (K:=K) (S:=S) (v:=v)
 | @insert i S' e ih=> rw [sum_insert e,sum_insert e]; exact (h _ (mem_insert_self ..)).plus (ih (fun i u=> h _ (mem_insert_of_mem u)))
lemma times (h:Grant C A K S v R X)(p:Grant C A K T v B Y)(e:0≤v)(q:Kᵀ= -K)(d:Grass S T)(a:Cross K C A S T)(f:Furl K T): Grant C A K (S∪T) v (R*B) (X*Y):=by
 refine ⟨mul_nonneg h.bank p.bank,?_⟩; intro t u L H
 let Z(D):= wake C A K D; let x:= LinearMap.mul ℂ (FC n); rw [mul_assoc]; change ‖(L.comp (x.flip Y)) X‖≤_; refine h.bill _ (mul_nonneg p.bank u) (L.comp (x.flip Y)) ?_; intro w e'
 change ‖L (Z w * Y)‖ ≤ v^w.card*(B*t); rw [mul_left_comm]; change ‖(L.comp (x (Z w))) Y‖ ≤ _; refine p.bill (v^w.card*t) (by positivity) (L.comp (x (Z w))) ?_; intro D d';
 change ‖L (wake C A K w *wake C A K D)‖ ≤v^D.card*(v^w.card*t); have he:= grass_sub d e' d'; rw [wake_free q (furl_sub f d'),←wake_concat q he (cross_sub a e' d') (furl_sub f d')]; apply (H (w∪D) (union_subset_union e' d')).trans_eq; rw [card_union_of_disjoint (grass_freed he),pow_add,mul_comm (v^w.card),mul_assoc]
private lemma stirred (h:T∈ S.powerset.erase S)(q:Kᵀ= -K)(f:Furl K S)(p:Pᵀ= -P)(b:Bun P S S B)(u:1≤ B)(z:0≤v)(w:v≤1): Grant C A K S v (v*B^S.card) (stir C A P S T):=by
 have hx:0≤ B:= le_trans zero_le_one u; let X:= S\ T; have hw:T⊆ S:= mem_powerset.mp (mem_of_mem_erase h); have hg:X⊆S:=sdiff_subset; have hv:1≤X.card:=by
    apply card_pos.mpr; exact sdiff_nonempty.mpr (fun w=> (mem_erase.mp h).1 (le_antisymm hw w))
 refine ⟨by positivity,?_⟩; intro Y y l H; rw [stir,←wake_free q (furl_sub f hg),map_smul,norm_smul,norm_mul,bow_limit,one_mul]; apply (mul_le_mul ((nest_lane p b hw hx).trans (pow_le_pow_right₀ u (card_le_card hw))) (H _ hg) (norm_nonneg _) (by positivity)).trans; change B^S.card*(v^X.card*Y)≤_; nth_rw 2 [←pow_one v]; rw [mul_comm _ (B^S.card),mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one z w hv) y) (by positivity)
/-- buy across different Wick reference. price linear in WIDTH v, regardless of u paid for annih unpaired. -/
lemma turn (q:Kᵀ= -K)(f:Furl K S)(p:Pᵀ= -P)(b:Bun P S S B)(u:1≤ B)(z:0≤v)(w:v≤1): Grant C A K S v (v*(2*B)^S.card) (wake C A P S-pf P S • 1):=by
 have hx :0≤B:=le_trans zero_le_one u
 let U:=S.powerset; let d:= U.erase S; let y:=v*B^S.card; have he:= Grant.sumC (stir C A P S) (fun _=>y) d (fun i (ti:i ∈ d)=> stirred ti q f p b u z w)
 have hv: stir C A P S S= pf P S • 1:=by simp [stir];
 rw [← hv,wake,← sum_erase_add _ _ (mem_powerset.mpr subset_rfl), add_sub_cancel_right]; apply he.up; rw [sum_const,nsmul_eq_mul]; apply (mul_le_mul_of_nonneg_right (show (d.card:ℝ) ≤ ↑(S.powerset.card) from Nat.cast_le.mpr (card_le_card (erase_subset ..))) (show 0≤y from mul_nonneg z (by positivity))).trans_eq; rw [card_powerset]; push_cast; unfold y; ring
lemma turnRaw (q:Kᵀ= -K)(f:Furl K S)(p:Pᵀ= -P)(g:Cross P C A S S ∨ ∀ i∈ S,∀ j∈ S,i < j → antiB (A i) (C j)=P i j • 1 ∧ antiB (A i) (A j)=0)(b:Bun P S S B)(u:1≤ B)(z:0≤v)(w:v≤1): Grant C A K S v (v*(2*B)^S.card) (prime C A S-pf P S • 1):=by
 rw [←full_rip C A p (g.elim (fun ℓ i ti j tj _=>ℓ i ti j tj) id)]; exact turn q f p b u z w
lemma gathers [Fintype ι][LinearOrder ι](y:ι→Finset I)(t:ι→ℝ)(F:ι→FC n)(L:Finset ι)(h:∀ i∈L,Grant C A K (y i) v (t i) (F i))(e:0≤v)(q:Kᵀ= -K)(f:∀ i∈ L,Furl K (y i))(d:∀ i∈ L,∀ j∈ L,i < j → Grass (y i) (y j) ∧ Cross K C A (y i) (y j)): Grant C A K (L.biUnion y) v (∏ i∈L,t i) (fo F (L.sort (· ≤ ·))):=by
 induction L using Finset.induction_on_max with
 | empty=> simpa [fo] using Grant.one (C:=C) (A:=A) (S:=∅) (K:=K) (v:=v)
 | insert i S g ih =>
    let Y:= S.biUnion y; let x:=ih (fun _ w=>h _ (mem_insert_of_mem w)) (fun _ w=>f _ (mem_insert_of_mem w)) (fun _ w _ u=>d _ (mem_insert_of_mem w) _ (mem_insert_of_mem u))
    have hv:i∉ S:=fun w=>lt_irrefl _ (g _ w)
    have he:Grass Y (y i):=by intro j w; obtain ⟨k,w,b⟩:=mem_biUnion.mp w; exact (d k (mem_insert_of_mem w) i (mem_insert_self ..) (g k w)).1 j b
    have hp:Cross K C A Y (y i):=by intro j w; obtain ⟨k,w,b⟩:=mem_biUnion.mp w; exact (d k (mem_insert_of_mem w) i (mem_insert_self ..) (g k w)).2 j b
    let f':=fun _:ι=>(0:FC n); have ht(T:Finset ι):prime F f' T = fo F (T.sort (·≤·)):= by unfold prime; rw [show f'=0 from rfl,add_zero]
    rw [biUnion_insert,union_comm,prod_insert hv,mul_comm (t i),← ht,prime_last _ _ (show Grass S {i} from fun j tj k tk=>(by rw [mem_singleton.mp tk]; exact g _ tj)),show f' i=0 from rfl,add_zero,ht]; exact x.times (h i (mem_insert_self ..)) e q he hp (f _ (mem_insert_self ..))
end Grant
lemma bun_sub (h:Bun K S S v)(p:T⊆ S): Bun K T T v:=fun j h'=>le_trans (sum_le_sum_of_subset_of_nonneg p (fun _ _ _=>by positivity)) (h _ (p h'))
-- Ward for actual tilt. combine UNTIL and KeepSeparate maybe dirty on left pay norm before Tilt (but not T f after); require ‖modifyB Dirty‖ directly. expose abstract operator
variable {v u U Z:ℝ}{y x:Wave n}{F G W:FC n}{J P T':Op n}{W':Finset n}
def viewer (X:Wave n):FC n →ₗ[ℂ] Wave n where
 toFun F:=acts F X
 map_add' F G:=act_add ..
 map_smul' _ F:= act_smul ..
theorem Work [Nonempty n](h:0≤v)(p:1≤u)(t:Kᵀ= -K)(g:Bun K S S v)(c:∀ i∈ S,‖C i‖≤ v)(a:∀ i∈ S,‖A i‖≤v*u)(R:Grant C A K S (4*v) U F)(e:IsStarProjection P)(k:Sea P x)(q:T'=cutM W')(M:Sea T' y)(s:0<z)(w:z≤1)(ℓ:modifyB T' z G=W*F)(ξ:∀ i,Letter (A i))(μ:∀ (i:I)(x:Wave n),Sea (draft P T' z) x→ acts (A i) x=0): Yep (u*flowCost z) (acts (star G) y) x (‖W‖*U* Real.exp (trade P T' z)) := by
 subst T'; let T:=cutM W'; let D:=quant (castV T z); let S':= draft P T z
 intro L; obtain ⟨y', q,r⟩:= gate_trace e (cutM_idp W') s w x k; let f:=rollC (readB T z); let v':=acts (f L) y'
 have hu:0≤u:=le_trans zero_le_one p; have he(Y:List (Token n)): Pause A Y.length (acts (f Y) y'):=by
    induction Y with
    | nil=> change Pause A _ (acts _ _); simpa [f,rollC] using startPause A (fun i=> μ i y' q)
    | cons i Y ih=>
       rw [show f (i::Y)=readB T z i * f Y from rfl, act_mul,List.length_cons]; apply pause_one ⟨_,_,rfl⟩ ξ ih
 let m:=u^L.length; let M':=ante T z; let X:=‖acts D x‖; have hz:0≤U:=R.bank; let B:=flowCost z^L.length
 have hm : 0 ≤ m:=pow_nonneg hu _; have hg: ‖acts F v'‖≤ U*(m*‖v'‖):= R.bill _ (mul_nonneg hm (norm_nonneg _)) (viewer v') fun Y p=> by rw [←mul_assoc]; exact power_price t (bun_sub g p) (he L) ‹1≤u› h (fun i ti=>a i (p ti)) (fun i ti=>c i (p ti)) -- shadow p (‹›)
 have hh:‖v'‖≤B:=le_trans (operate_f ..) (by rw [q.2,mul_one]; exact credits (cutM_idp W') s w L)
 rw [wager M s, trace_price e (cutM_idp _) s w x k, ℓ, act_mul, r,RCLike.real_smul_eq_coe_smul (K:=ℂ),map_smul,inner_smul_right,norm_mul,norm_mul, costs,mul_pow]; change ‖(M':ℂ)‖*(‖(X:ℂ)‖* ‖inner ℂ y (acts (_*_) _)‖)≤ ‖W‖*U*(M'*X)*(m*B)
 have hM:0≤M':= Real.exp_pos _|>.le; have hX : 0≤X:= norm_nonneg _; rw [act_mul (W*_),act_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg hM,Real.norm_of_nonneg hX, ←mul_assoc M', show ‖W‖*U*(M'*X)*(m*B)=(M'*X)*(‖W‖*(U*(m*B))) from (by ring)]; apply mul_le_mul_of_nonneg_left _ (by positivity); apply (norm_inner_le_norm ..).trans; rw [M.2,one_mul]; exact (operate_f ..).trans (mul_le_mul_of_nonneg_left (hg.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hm) hz)) (norm_nonneg _))
end YM.CF.Lamour
#print axioms YM.CF.Lamour.Work
#print axioms YM.CF.Lamour.Grant.turn
#print axioms YM.CF.Lamour.Grant.gathers
