import YM.SU5.FiniteGaugeData.Pannier.ShelfFog
import YM.CF.Thera.Hang
/-! Sea-letter-fuel. Compare before using norm costs. Use m OUTGOING particles, not holes
 at the observation reference which would cost a rank hypothesis. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 980000
noncomputable section
namespace YM.CF.Papyrus.Granat
open Function Filter NormedSpace Finset Lattice Lat Cube Skye Scree Drapes Fock Thera Laic Rush Tulip Peaks Pastry Fir Nacre Scroll Spire
open CF.Pannier CF.Pannier.Chancel CF.Pannier.Damask
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
variable {n : Type*} [LinearOrder n][Fintype n] {s S T:Finset n} {P B:Op n} {V U: UNI n} {a b :ℝ} {k l m : ℕ} {A F: FC n}{x y:Wave n}
-- frame diagonal birth
def Tithe (s: Finset n)(k:ℕ)(x:Wave n):Prop:= ∀ j:Finset n, k < (j\s).card → x.ofLp j=0
def Lode (U: UNI n)(S:Finset n)(m:ℕ)(x:Wave n): Prop:= Tithe S m (acts (quant (star U.val)) x)
def JumpCost (k:ℕ)(A:FC n):Prop:=∀ (U: UNI n) (S:Finset n)(m:ℕ) (x:Wave n), Lode U S m x→ Lode U S (k+m) (acts A x)
lemma Lode.low (h:Lode U S m x)(p:m≤k): Lode U S k x:=fun j z=>h j (p.trans_lt z)
lemma Lode.origin (g:Sea (twist U (cutM S)) x): Lode U S 0 x:=by
 let A:=twist U (cutM S); let q:=quant U.val; let Q:=cutM S.powerset
 have he: acts (quant A) x=x:=by nth_rw 1 [←g.1]; rw [←act_mul,line_quant (IsStarProjection.mk (by unfold A IsIdempotentElem; rw [←map_mul,(cutM_idp S).isIdempotentElem]) (by unfold A IsSelfAdjoint; rw [←map_star,(cutM_idp S).isSelfAdjoint])),g.1] -- tune lines
 rw [show quant A = q * Q * star q from (by unfold A q Q; rw [twist_formula,quant_mul,quant_mul,quant_star,quantCut])] at he
 rw [Lode,quant_star]; let y:=acts (star q) x; have hv: acts Q y=y:=by
    conv_rhs=>unfold y; rw [← he]; -- tune he recursive
    rw [←act_mul (star q),←mul_assoc _ (q*Q),←mul_assoc,show star q*q=1 from (quantU U).property.1,one_mul,act_mul]
 intro j p; change y.ofLp j=0; rw [← hv,show Q=cutM _ from rfl,cutM,diag_apply,if_neg (fun h=> ?_),zero_mul] -- bad binder
 obtain ⟨i,u⟩:=card_pos.mp p; exact (mem_sdiff.mp u).2 (mem_powerset.mp h (mem_sdiff.mp u).1)
private lemma Tithe.putc (p: Tithe s m x) (i:n) : Tithe s (m+1) (acts (put i) x):=by
 intro j h; rw [put_row]; split_ifs with e; swap; · rfl
 have he : j\s ⊆ insert i ((j.erase i)\s):=fun k a=> by
    obtain ⟨z,g⟩:=mem_sdiff.mp a; by_cases h:k=i; exact mem_insert.mpr (Or.inl h); exact mem_insert.mpr (Or.inr (mem_sdiff.mpr ⟨mem_erase.mpr ⟨h,z⟩,g⟩))
 rw [p _ ?_,mul_zero]
 exact lt_of_add_lt_add_right (h.trans_le ((card_le_card he).trans (card_insert_le ..)))
private lemma Tithe.remc (p:Tithe s m x)(i:n): Tithe s (m+1) (acts (takeF i) x):=by
 intro j h; rw [take_row]; split_ifs; · rfl
 rw [p _ ((Nat.lt_succ_self m).trans (lt_of_lt_of_le h (card_le_card (sdiff_subset_sdiff (subset_insert i j) (Subset.refl s))))),mul_zero] -- tune
private lemma Tithe.roll {ι:Type*}(F:ι→ Wave n)(D:Finset ι)(p:∀ i∈D,Tithe s m (F i)): Tithe s m (∑ i∈D,F i):=by
 intro j g; rw [WithLp.ofLp_sum,Finset.sum_apply]; apply sum_eq_zero; intro i h; exact p i h j g
private lemma Tithe.χ (p:Tithe s m x)(c:ℂ): Tithe s m (c • x) :=by intro j h; rw [WithLp.ofLp_smul,Pi.smul_apply,p j h,smul_zero]
private lemma Tithe.next (p:Tithe s m x)(h:Letter A): Tithe s (m+1) (acts A x):= by
 obtain ⟨b,v,rfl⟩:= h; cases b with
 | false=> rw [show creed false _=create v from rfl,create_def,act_sum]; simp_rw [act_smul]; exact Tithe.roll _ _ (fun i _=>(p.putc i).χ _)
 | true=> rw [show creed true _=remove v from rfl,remove_def,act_sum]; simp_rw [act_smul]; exact Tithe.roll _ _ (fun i _=>(p.remc i).χ _)
lemma Lode.next (p:Lode U S m x)(h:Letter A): Lode U S (m+1) (acts A x):=by
 obtain ⟨b,v,rfl⟩:=h; let V:=star U; let Y:=quantU V; let u:=acts Y.val x; change Tithe S (m+1) (acts Y.val _); rw [Fock.swivel]
 let z:=acts V.val v
 have hv: twist Y (creed b v)=creed b z:=by cases b; exact twist_create ..; exact twist_remove ..
 rw [hv]; exact Tithe.next p ⟨b,z,rfl⟩
lemma JumpCost.low (p:JumpCost k A)(h:k≤ m): JumpCost m A:= fun U V i x t=>(p U V i x t).low (Nat.add_le_add_right h _)
lemma JumpCost.one : JumpCost 0 (1:FC n):=fun U S m x p =>by rwa [act_one,zero_add]
lemma JumpCost.letter (p:Letter A): JumpCost 1 A:=fun U S m x h=>by rw [Nat.add_comm 1]; exact h.next p
lemma JumpCost.mul (p:JumpCost k A)(q: JumpCost l F): JumpCost (k+l) (A*F):=fun U S m x h=>by rw [act_mul, Nat.add_assoc]; exact p U S _ _ (q U S _ _ h)
lemma JumpCost.scale (p:JumpCost k A)(c:ℂ):JumpCost k (c • A):=by intro U S m x h; rw [act_smul,Lode,map_smul]; exact Tithe.χ (p U S _ x h) _
lemma JumpCost.add (p:JumpCost k A)(q:JumpCost k F): JumpCost k (A+F):=by
 intro U S m x h i w; rw [act_add,map_add,WithLp.ofLp_add,Pi.add_apply,p U S _ x h i w,q U S _ x h i w,zero_add]
variable {ι:Type*}{Y:ι→FC n}
lemma JumpCost.roll (p:∀ i,JumpCost k (Y i))(L:List ι): JumpCost (k*L.length) (fo Y L):=by
 induction L with
 | nil=> simp only [List.length_nil,mul_zero,Pannier.Chancel.fo,List.map_nil,List.prod_nil]; exact one
 | cons i l ih=> rw [List.length_cons,Nat.mul_add, Nat.mul_one,Nat.add_comm]; exact (p i).mul ih
-- bridge projection measure smooth. positive even when empty (note x rank independent)
def Bolt (B P:Op n)(η:ℝ) := B*(P+(η^2:ℝ) • (1-P))* B+(1-B)
def crater (B P:Op n)(η:ℝ) := Real.log (Bolt B P η).det.re/2
private def harass (P:Op n)(a:ℝ) : Op n:= P+a • (1-P)
private lemma h_m (p:IsStarProjection P):harass P a*harass P b= harass P (a*b):=by
 unfold harass; rw [add_mul,mul_add,mul_add,Algebra.mul_smul_comm,Algebra.smul_mul_assoc,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,p.isIdempotentElem.eq,Porth p, p.one_sub.isIdempotentElem.eq, show (1-P)*P=0 by rw [sub_mul,one_mul,p.isIdempotentElem.eq,sub_self]]; simp only [smul_zero,zero_add,add_zero,mul_smul]
private lemma h_s (p:IsStarProjection P):star (harass P a)=harass P a:=by rw [harass,star_add, p.isSelfAdjoint,star_smul,star_sub,star_one,p.isSelfAdjoint,star_trivial]
private lemma nest (P:Op n): harass P 1=1:=by unfold harass; rw [one_smul,add_sub_cancel]
lemma crater_val (p:IsStarProjection P)(g:IsStarProjection B)(e:0<a) (h:Sea B x):
    ‖acts (quant (harass P a)) x‖=Real.exp (crater B P a):=by
 let Q:=quant (harass P a); have hv: acts (quant (harass P a⁻¹)) (acts Q x)=x:=by rw [←act_mul,show Q= _ from (show Q=quant (harass P a) from rfl),← quant_mul,h_m p,inv_mul_cancel₀ e.ne',nest,quant_one,act_one]
 let K:= ‖acts Q x‖; have ht:0<K:= norm_pos_iff.mpr fun y=> (norm_pos_iff.mp (h.2.symm ▸ zero_lt_one): x≠0) (by rwa [y,map_zero,eq_comm] at hv)
 let R:= Bolt B P a; have hm :(↑(K^2):ℂ) =R.det:=by
    rw [← show B*(star (harass P a)* harass P a)*B+(1-B)=R from (by unfold R Bolt; rw [h_s p,h_m p,pow_two]; rfl), ← meadow g x h]; unfold skyGlow; rw [quant_mul,quant_star,act_mul,←act_inner,star_star,inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]; rfl
 change K=_; unfold crater; rw [← show (↑(K^2):ℂ)= (Bolt B P a).det from hm,Complex.ofReal_re,Real.log_pow]; push_cast; rw [show 2*Real.log K/2=Real.log K by ring,Real.exp_log ht]
private lemma dart (s T:Finset n)(a:ℝ):
    (∏ i∈T, (if i∈s then (1:ℂ) else a))=(a:ℂ)^(T\s).card:=by
 let F(i:n):ℂ:= if i∈s then 1 else a
 have he:= prod_sdiff (f:=F) (inter_subset_left :T∩s ⊆ T) -- name types?
 rw [show T \ (T∩s) = T\s by ext; simp, prod_congr (s₁:=T∩s) (g:=fun _=>1) rfl (fun i hi=>if_pos (mem_inter.mp hi).2), prod_const_one, mul_one] at he
 rw [← (show ∏ x∈T\s,F x=∏ x∈T,F x from he),prod_congr (g:=fun _=>(a:ℂ)) rfl (fun i h=>if_neg (mem_sdiff.mp h).2),prod_const]
private lemma pit_l (p:P=twist U (cutM s))(h:Lode U s m x)(e:0<a)(g:a ≤ 1):
    ‖acts (quant (harass P a⁻¹)) x‖≤ a⁻¹^m * ‖x‖:=by
 let d :ℝ:=a⁻¹; have hk:1 ≤ d:= (one_le_inv₀ e).mpr g
 let R:= quantU U; let z:=acts (star R.val) x; have hp:Tithe s m z:=by unfold z R; rwa [show star (quantU U).val=quant (star U.val) from (quant_star _).symm]
 let c(i:n):ℂ:=if i∈s then 1 else d; let W:=Matrix.diagonal c; have hu:harass P a⁻¹=twist U W:=by rw [p]; unfold harass; rw [←map_one (twist U),←map_sub (twist U) 1,←map_smul _,←map_add]; congr 1; ext i j; by_cases h:i=j; subst j; by_cases h:i∈s <;> simp [W,c,d,cutM,h,Complex.real_smul]; simp [W,Matrix.diagonal,c,cutM,h] -- smul_R
 rw [hu,quant_twist,twist_formula]; change ‖acts (R.val*quant W*star R.val) x‖≤ d^m * _; rw [mul_assoc,act_mul,act_unit_norm,act_mul,quant_diag]
 let y:=acts (Matrix.diagonal fun i=>∏ j∈i,c j) z; change ‖y‖≤_
 have he(i:Finset n):‖y.ofLp i‖ ≤ d^m*‖z.ofLp i‖:=by
    unfold y; rw [diag_apply]; by_cases g:m < (i\s).card; · rw [hp i g,mul_zero,norm_zero,mul_zero]
    rw [norm_mul,dart s i d,norm_pow,Complex.norm_real,Real.norm_of_nonneg (zero_le_one.trans hk)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hk (by omega)) (norm_nonneg _)
 have hz:‖z‖=‖x‖:=act_unit_norm (star R) _
 rw [←hz]; apply le_of_sq_le_sq _ (mul_nonneg (pow_nonneg (zero_le_one.trans hk) _) (norm_nonneg _))
 rw [mul_pow,EuclideanSpace.norm_sq_eq,EuclideanSpace.norm_sq_eq,mul_sum]; apply sum_le_sum; intro i _; exact (pow_le_pow_left₀ (norm_nonneg _) (he i) _).trans_eq (mul_pow ..)
-- combine without saying rank equality or det phase
lemma tried (p:P=twist U (cutM s))(H:IsStarProjection P)(g:IsStarProjection B)(f:0<a)(q:a ≤ 1)
    (h:Sea B x)(w:Lode U s m y): ‖inner ℂ x y‖≤ Real.exp (crater B P a)*a⁻¹^m*‖y‖:=by
 let Q:= quant (harass P a); let R:= quant (harass P a⁻¹); have hu:star Q*R=1:=by unfold Q R; rw [←quant_star,←quant_mul,h_s H,h_m H,mul_inv_cancel₀ f.ne',nest,quant_one]
 have hh: inner ℂ x y=inner ℂ (acts Q x) (acts R y):=by nth_rw 1 [←star_star Q]; rw [act_inner,← act_mul,hu,act_one] -- check occurrence
 rw [hh,mul_assoc]; exact (norm_inner_le_norm ..).trans ((mul_le_mul ((crater_val H g f h).le) (pit_l p w f q) (norm_nonneg _) (Real.exp_pos _).le))
end YM.CF.Papyrus.Granat
#print axioms YM.CF.Papyrus.Granat.tried
#print axioms YM.CF.Papyrus.Granat.JumpCost.letter
