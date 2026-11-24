import YM.CF.Fixed.SpinSlice

/-! `timed` stage after partial Fourier. Time site still `Per N`, spatially
uniform diagonal link angles can still vary by time. Directed positive basis on
halo uses gauge frame product. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Fixed.Rift
open Function NormedSpace Matrix Lattice Finset Filter Fock BZ Mir Lat Scroll Bulk
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ComplexOrder
attribute [local instance] opCStarAlgebra

section cut
variable {n m : Type*}[Fintype n][DecidableEq n][Fintype m][DecidableEq m]{b e:ℝ}
abbrev blockE (x y:n)(A:Op (n×m)):Op m:=A.submatrix (x,·) (y,·)
omit [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
lemma blockEq (A B:Op (n×m))(h:∀ i j:n,blockE i j A=blockE i j B): A=B:=by ext ⟨x,i⟩ ⟨y,j⟩; exact Matrix.ext_iff.mpr (h x y) i j
omit [Fintype n] [Fintype m] [DecidableEq m] in
lemma block_jump (f:Equiv.Perm n)(g:n→ Op m) (x y:n):blockE x y (jump f g)=if f x=y then g x else 0:=by by_cases h:f x=y<;> ext i j <;> simp [h,blockE,jump_apply]
omit [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n] in
lemma block_add (x y:n)(A B:Op (n×m)):blockE x y (A+B)=blockE x y A+blockE x y B:=rfl
omit [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n] in
lemma block_star (x y:n)(A:Op (n×m)):blockE x y (star A)= star (blockE y x A):=rfl
omit [DecidableEq n] [DecidableEq m] in
lemma block_mul (x y:n)(A B:Op (n×m)):blockE x y (A*B) = ∑ k,blockE x k A * blockE k y B:=by ext i j; simp only [blockE,Matrix.sum_apply,Matrix.submatrix_apply,Matrix.mul_apply,Fintype.sum_prod_type]
omit [DecidableEq n] [DecidableEq m] in
lemma block_trace (A:Op (n×m)):trR A=∑ i,trR (blockE i i A):=by simp only [trR,Matrix.trace, Fintype.sum_prod_type,Complex.re_sum]; apply sum_congr rfl; intro x _; rfl

abbrev spot (x:n) (M:Op m): Op (n×m):=jump (Equiv.refl n) (fun y=> if y=x then M else 0)
omit  [DecidableEq m] in
lemma spot_left (A: Op (n×m))(M:Op m)(x y z:n): blockE x y (spot z M*A)=if x=z then M*blockE z y A else 0:=by
  rw [block_mul]; simp_rw [spot,block_jump, Equiv.refl_apply]; rw [sum_eq_single x]; · by_cases h:x=z <;> simp [h]
  · intro j _ h; simp [Ne.symm h]
  simp
omit  [DecidableEq m] in
lemma spot_right (A: Op (n×m))(M:Op m)(x y z:n): blockE x y (A * spot z M)=if y=z then blockE x y A*M else 0:=by
  rw [block_mul]; simp_rw [spot,block_jump, Equiv.refl_apply]; rw [sum_eq_single y]; · by_cases h:y=z <;> simp [h]
  · intro j _ h; simp [h]
  simp
omit  [DecidableEq m] in
lemma spot_mix (x y:n)(M W:Op m)(p:x≠y): spot x M*spot y W=0:=by apply blockEq; intro i j; rw [spot_left]; by_cases h:i=x <;> simp [h,spot,block_jump,p, show ∀ i j:n, blockE i j (0:Op (n×m))=0 from fun _ _=>rfl]

omit  [DecidableEq m] in
lemma cut_shoot (x y:n) (M W:Op m)(A B:Op (n×m)): trR (spot x M*A*spot y W*B)=trR (M*blockE x y A * W*blockE y x B):=by
  rw [block_trace]; simp_rw [block_mul _ _ (spot x M*A*spot y W) B, spot_right,spot_left]; simp [apply_ite (trR), ite_mul]; rw [sum_eq_single x]; · simp
  · intro i _ g; simp [g,trR]
  simp

lemma spot_norm (x:n)(A:Op m): ‖spot x A‖ ≤ ‖A‖:= jump_bound _ _ (norm_nonneg _) (fun i=>by split_ifs; exact le_rfl; rw [norm_zero]; exact norm_nonneg _)
lemma trace_bump (A X Y:Op n)(p:X*Y=0)(h:Y*X=0): trR (bump A X*bump A Y)=2*trR (X*A*Y*A):=by
  have ht(A B X Y:Op n)(p:A*B=0): X*A*(B*Y)=0:=by rw [mul_assoc,←mul_assoc A,p,zero_mul,mul_zero]
  rw [show bump A X*bump A Y = (A*X)*(A*Y) + A*X*(Y*(A+Y)) + X*(A* (A*Y))+(X*X)*(A*Y)+X*A*(Y*A)+(X*X)*(Y*A) + X*(A+X)*(Y*Y) from by unfold bump; noncomm_ring]
  have hu: trR (A*X*(A*Y))=trR (X*A*Y*A):=by rw [mul_assoc,comm_t, ←mul_assoc X]
  have he(B:Op n) : trR (X* B *Y)=0:=by rw [comm_t,←mul_assoc Y X,h,zero_mul]; simp [trR]
  have hv: trR (X*A*(Y*A))=trR (X*A*Y*A):=by rw [←mul_assoc]
  simp only [plus_t,hu,ht _ _ _ _ p,hv]
  rw [show X * (A*(A*Y))=X*(A*A)*Y from by noncomm_ring,he,show X*X*(A*Y)=X*(X*A)*Y from by noncomm_ring,he,show X*(A+X)*(Y*Y) = X*((A+X)*Y)*Y from by noncomm_ring,he,show trR (0:Op n)=0 from by simp [trR]]; ring
lemma influence_spot (x:n)(A:Op m)(h:‖A‖≤b):Influence (Fintype.card m * b) (spot x A):=by
  unfold Influence; intro B; rw [block_trace]
  rw [sum_eq_single x]; swap; · intro i _ hi; rw [spot_left,if_neg hi]; simp [trR]
  swap; · simp
  unfold trR; rw [Matrix.trace,Complex.re_sum]; refine (Finset.abs_sum_le_sum_abs ..).trans ?_; refine le_trans (sum_le_sum (g:=fun _=> b*‖B‖) fun i _=>?_ ) (by simp [mul_assoc]); exact le_trans (Complex.abs_re_le_norm _) ((norm_entry (spot x A*B) _ _).trans ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right ((spot_norm x A).trans h) (norm_nonneg _))))
end cut
variable {N:Side}
abbrev Stage (N : Side):= Per N × SpinIdx
local notation "M" => Op (Stage N)
def diagonalS (x:Per N→ Spin): Op (Stage N):=jump (Equiv.refl _) x
def trunkZ(x:Per N):ℂ:= if x= -1 then -1 else 1
def plusTime (N: Side) := Equiv.addRight (1:Per N)
def shotF (N: Side) : Op (Stage N):=jump (plusTime N) (fun x=> trunkZ x • incoming)
def timely (N: Side) : Op (Stage N):=shotF N+star (shotF N)
def timed (v:Per N→Three) : Op (Stage N):= timely N + diagonalS (fun i=> phaseS (v i))

lemma diagonal_self (x:Per N→Spin)(h:∀ i,IsSelfAdjoint (x i)): IsSelfAdjoint (diagonalS x):=by rw [diagonalS,isSelfAdjoint_iff,jump_star, Equiv.refl_symm]; simp only [Equiv.refl_apply,(h _).star_eq]
lemma time_self : IsSelfAdjoint (timely N):=by unfold timely; rw [isSelfAdjoint_iff,star_add,star_star,add_comm]
lemma diagonal_norm (w:Per N→Three)(z:ℝ)(h:0≤z)(p:∀ i j,|w i j|≤z):‖diagonalS (fun i=>phaseS (w i))‖≤6*z:= jump_bound _ _ (by positivity) fun i=>small_phase _ _ (p i)
lemma time_block (w:Per N→Three)(x y:Per N): blockE x y (timed w)= (if x+1=y then trunkZ x • incoming else 0)+(if y+1=x then trunkZ y • star incoming else 0)+(if x=y then phaseS (w x) else 0):=by
  have ht(x:Per N): star (trunkZ x)=trunkZ x:=by unfold trunkZ; split_ifs<;>simp
  unfold timed timely shotF diagonalS; rw [block_add,block_add,Rift.block_star,block_jump,block_jump,block_jump,apply_ite (Star.star)]; rw [star_smul,ht,star_zero]; rfl
lemma time_unit (N:Side) : timely N∈ unitary (Op (Stage N)):=by
  have h1:star (shotF N)*shotF N=diagonalS (fun _=>minusS):=by unfold shotF diagonalS; rw [jump_star,jump_mul, Equiv.symm_trans_self]; apply congrArg; funext i; unfold trunkZ; split_ifs <;> simp [incoming_link]
  have h2:shotF N *star (shotF N)=diagonalS (fun _=>plusS):=by unfold shotF diagonalS; rw [jump_star,jump_mul, Equiv.self_trans_symm]; apply congrArg; funext i; rw [Equiv.symm_apply_apply]; unfold trunkZ; split_ifs <;> simp [outgoing_link]
  have he:shotF N*shotF N=0:=by
    unfold shotF; rw [jump_mul]; ext i j; rw [jump_apply]; split_ifs
    · rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm,incoming_nil]; simp
    rfl
  have hs: timely N * timely N=1:=by unfold timely; rw [mul_add,add_mul,add_mul,h1,h2,he,←star_mul,he,star_zero,add_zero,zero_add]; unfold diagonalS; rw [←jump_add,← jump_id]; congr 1; funext i; change minusS + plusS = _; unfold minusS; rw [sub_add_cancel]
  rw [Matrix.mem_unitaryGroup_iff,time_self.star_eq]; exact hs

@[simp] lemma tick (x:Per N): (plusTime N) x=x+1:=rfl
lemma base_bound (z:ℝ)(u:0≤z)(X:Per N→Three)(p:∀ i j, |X i j| ≤ z):‖timed X-timely N‖≤6*z:=by rw [timed,add_sub_cancel_left]; exact diagonal_norm _ _ u p
lemma pole_bound (A:M)(z:ℝ)(u:0≤z)(h:‖A-timely N‖≤z) : ‖1-A^2‖≤2*z + z*z:=by
  let B:=A-timely N; let C:=timely N; have he:C*C=1:=by have ht:star C*C=1:=(time_unit N).1; rw [show star C=C from time_self] at ht; exact ht
  have hz:1-A^2= -(C*B+B*C+B*B):=by rw [←he,show A=C+B from (by unfold B C; abel)]; noncomm_ring -- A in B automatically? tune
  have hv: ‖C‖=1:= CStarRing.norm_of_mem_unitary (time_unit N); have hb:‖B‖ ≤ z:=h
  rw [hz,norm_neg]; refine (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans ?_) ((norm_mul_le ..).trans ?_))) ((norm_mul_le ..).trans (mul_le_mul hb hb (norm_nonneg _) u))).trans_eq (show z+z+z*z=_ from by ring)); all_goals rw [hv]; linarith
abbrev chip : ℝ:=(10:ℝ)^(-14:ℤ)
lemma chip_p:0<chip:=by unfold chip; positivity
lemma chip_u : chip≤1/4:=by unfold chip; norm_num
lemma away_W (p:2<N.val) : (0:Per N)≠ -1 ∧ ((1: Per N) ≠-1):=by
  have h: (1:Per N)≠0:=by intro h; have hA: (1:Per N)=0:=h; rw [← Nat.cast_one] at hA; have hB:=congrArg ZMod.val hA; rw [ZMod.val_natCast_of_lt (by omega),ZMod.val_zero] at hB; norm_num at hB
  refine ⟨fun g=>h ?_,fun g=>?_⟩; · rw [eq_neg_iff_add_eq_zero] at g; simpa using g
  have he : 1+1=(0:Per N):= by nth_rw 1 [g]; rw [neg_add_cancel];
  have ht:= congrArg ZMod.val he; rw [show (1:Per N)+1=↑(2:ℕ) from (by push_cast; ring), ZMod.val_natCast_of_lt p,ZMod.val_zero] at ht; norm_num at ht

lemma between (p:2<N.val)(X:Per N→Three) : blockE (0:Per N) (-1) (timed X)= -star incoming ∧ blockE (-1:Per N) (0:Per N) (timed X)= - incoming:=by rw [time_block,time_block]; simp only [neg_add_cancel,zero_add]; simp [trunkZ,(away_W p).1,(away_W p).2,Ne.symm ((away_W p).1)]
lemma bump_form {n:Type*}[Fintype n][DecidableEq n](A X:Op n): bump A X = -(A*X+X*A+X*X):=by unfold bump; noncomm_ring
variable (N)
lemma bump_price (A X:M) (z:ℝ)(u:0≤z)(h:‖X‖≤2*z)(hx:‖A‖≤2)(p:2*z≤1)(i:Influence (8*z) X): ‖bump A X‖≤10*z ∧ Influence (40*z) (bump A X):=by
  rw [bump_form]; constructor
  · rw [norm_neg]; refine le_trans ((norm_add_le ..).trans (add_le_add_left ((norm_add_le ..).trans (add_le_add (norm_mul_le ..) (norm_mul_le ..))) _)) ?_
    linarith [mul_le_mul hx h (norm_nonneg _) (by norm_num),mul_le_mul h hx (norm_nonneg _) (by positivity), (norm_mul_le X X).trans (mul_le_mul h (h.trans p) (norm_nonneg _) (by positivity))]
  let K:=A*X+X*A+X*X; have hp:Influence (40*z) K:= increase K (inf_add _ _ (inf_add _ _ (inf_left _ _ (by positivity) i hx) (inf_right _ _ (by positivity) i hx)) (inf_right _ _ (by positivity) i (h.trans p))) (by linarith); exact fun B=> by rw [neg_mul,debit_t,abs_neg]; exact hp B

variable {N}
def ages (x y:ℝ)(t:Per N): ℝ:= if t=0 then x else if t= -1 then y else 0
def spread (N:Side)(u v:ℝ)(p:Three): Per N→Three:= fun i=> update p 0 (p 0+ages u v i)
lemma deposit (p:2<N.val)(u v: ℝ)(x:Three): let A:=timed (N:=N) fun _=>x
 let W (t:Per N) (z:ℝ):= spot t (varS 0 (x 0 + z) - varS 0 (x 0)); timed (spread N u v x)= A+ W 0 u +W (-1) v := by
  intro A W; unfold A W timed diagonalS spot; rw [add_assoc,add_assoc, ←jump_add,←jump_add]; congr 2; funext i; simp only [spread,differ]; unfold ages; by_cases p':i=0; · subst i; simp [(away_W p).1]
  split_ifs <;> simp_all
lemma spread00 (x:Three): spread N 0 0 x=fun _ => x:=by funext i j; unfold spread ages; by_cases h:j=0 <;> by_cases p:i=0 <;> by_cases v:i= -1 <;> simp [h,p,v,update_of_ne]

lemma warmer (x:Three)(y:ℝ)(p:2< N.val)(t:‖y‖≤chip)(s:∀ i, |x i|≤chip)(z:0<y) :
    let V(u v:ℝ):=timed (spread N u v x)
    Safe (V 0 0) → Safe (V y 0) → Safe (V 0 y) → Safe (V y y) → y^2/16 ≤ energy (V y y)+energy (V 0 0)-energy (V y 0)-energy (V 0 y) := by
  intro V; let A:=V 0 0; rw [show V y y=_ from deposit p ..]; -- tune handle definition
  let B:=varS 0 (x 0+y)-varS 0 (x 0); let X:=spot (0:Per N) B; let Y:= spot (-1: Per N) B
  have hg(k:Per N): spot k (varS 0 (x 0 + 0)-varS 0 (x 0))=0:=by simp; ext ⟨i,j⟩ ⟨k',l⟩; simp [spot,jump_apply]
  have hE: timed (N:=N) (fun _=>x)=A:=by unfold A V; rw [spread00]
  rw [hE,show V y 0= A+X from by rw [show V y 0=_ from deposit p ..,hE]; dsimp only; rw [hg,add_zero],show V 0 y=A+Y from by rw [show V 0 y=_ from deposit p ..,hE]; dsimp only; rw [hg,add_zero]]; change Safe A → Safe (A+X) → Safe (A+Y) → Safe (A+X+Y) → _ ≤ energy (A+X+Y)+energy A-_-_
  intro K V1 V2 V3
  have hb: ‖B‖≤2*y:=by unfold B; refine (diff_vS ..).trans_eq ?_; rw [add_sub_cancel_left,abs_of_pos z] -- trans_eq bug maybe
  have hc(k:Per N): ‖spot k B‖≤2*y ∧ Influence (8*y) (spot k B):= ⟨(spot_norm ..).trans hb,increase _ (influence_spot _ B hb) (by norm_num [SpinIdx]; linarith)⟩
  let T:= timely N; let κ:=chip; have h0:=chip_p; have h1:=chip_u; have he: y ≤ chip:= le_trans (le_abs_self _) t
  have ht:‖A-T‖≤6*chip:=by rw [←hE]; exact base_bound _ h0.le _ (fun _ => s)
  let r:ℝ:=1/10^6; have hp(T': M)(h':‖T'-T‖≤10*κ): ‖1-T'^2‖≤r:= le_trans (pole_bound _ (10*κ) (by unfold κ; positivity) h') (by unfold κ chip r; norm_num)
  have hm: ‖A‖ ≤2:= by
    apply le_trans (norm_le_norm_sub_add A T); have hh : ‖T‖=1:= CStarRing.norm_of_mem_unitary (time_unit _); have hz:6*chip≤1:=by unfold chip; norm_num
    linarith
  have hx: ‖X‖≤2*y ∧ Influence (8*y) X:= (hc 0); have hy: ‖Y‖≤2*y ∧ Influence (8*y) Y:= hc (-1); let c:= varS 0 (x 0)
  have hW:X*Y=0:=spot_mix _ _ _ _ ((away_W p).1); have hQ:Y*X=0:=spot_mix _ _ _ _ ((Ne.symm ((away_W p).1))) -- syntax
  have hZ := mix_raise A K V1 V2 V3 hW (bump_price N A X y z.le hx.1 hm (by linarith only [le_trans he h1]) hx.2|>.2) (bump_price N A Y y z.le hy.1 hm (by linarith only [le_trans he h1]) hy.2|>.1) (show r≤1/4 from by unfold r; norm_num) (show 0≤40*y from by positivity) (hp A (by unfold κ; linarith)) (hp (A+X) (by rw [show A+X-T=A-T+X from by abel]; unfold κ; linarith only [ht,he,norm_add_le (A-T) X,hx.1,h0])) (hp (A+Y) (by rw [show A+Y-T=A-T+Y from by abel]; unfold κ; linarith only [ht,he,norm_add_le (A-T) Y,hy.1,h0])) (hp (A+X+Y) (by rw [show A+X+Y-T=A-T+X+Y from by abel]; unfold κ; linarith only [ht,he,norm_add_le (A-T+X) Y,norm_add_le (A-T) X,hy.1,hx.1,h0]))
  · rw [trace_bump A X Y hW hQ] at hZ; rw [show trR (X*A*Y*A)= _ from cut_shoot _ _ B B A A, show blockE (0:Per N) (-1) A= -star incoming from hE ▸ (between p _).1,show blockE (-1) 0 A= -incoming from hE ▸ (between p _).2] at hZ; simp only [mul_neg,neg_mul,neg_neg] at hZ
    let b:= Real.sin (x 0+y) - Real.sin (x 0); have het:B=(Real.cos (x 0)-Real.cos (x 0+y)) • grading + b • angleM 0:=by unfold B varS b; module -- tune
    rw [show trR (B*star incoming*B*incoming) = _ from het ▸ winter (Real.cos (x 0)-Real.cos (x 0+y)) b (0:Fin 3)] at hZ; have hh: y/2 ≤ b:=by
      obtain ⟨a,h,e⟩:= exists_deriv_eq_slope Real.sin (lt_add_of_pos_right (x 0) z) (Real.continuous_sin.continuousOn) Real.differentiable_sin.differentiableOn -- tune
      have hp:= abs_le.mp (s 0); have ht: |a| ≤1/2:=by have v:=h.2; have ht:=h.1; exact abs_le.mpr ⟨by linarith only [le_trans (neg_le_neg h1) hp.1, ht],by linarith only [hp.2.trans h1, v, le_trans he h1]⟩
      have hf : 1/2 ≤ Real.cos a := by have he:=Real.abs_cos_sub_cos_le a 0; rw [Real.cos_zero,sub_zero] at he; linarith [abs_le.mp (he.trans ht)]
      rw [show deriv Real.sin a= Real.cos a from by simp, add_sub_cancel_left] at e; unfold b; rw [eq_div_iff z.ne'] at e; nlinarith
    unfold r at hZ; nlinarith

end YM.CF.Fixed.Rift
