import YM.SU5.Velvet.LowTide
import YM.SU5.FiniteGaugeData.Pannier.Blizzard
/-!
 # subscribed kernels within clear halos; cost via a resolvent
 clean areas need be paid only through field geometry. kernel tails AFTER buying the tiling
-/
set_option linter.unusedVariables false
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option maxHeartbeats 250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Velvet
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye Pannier.Chancel Brace
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
variable {N:Side} {j n w d:ℕ} {u v η ζ δ:ℝ}
structure Procurement (j n:ℕ)(δ:ℝ) : Prop where
 insp : 0≤δ
 audit {N:Side}{M:Tulip.Male} (p:n≤N.val) : Sparkle N δ M j
 haloC (v:ℝ)(p:0<v) :∃ u:ℝ,0<u ∧ ∃ w:ℕ,∀ (N:Side), n≤N.val→ Winter j δ N u w v
-- in all clean & all Limit N
abbrev Rails:= Set.Icc (0:ℝ) (1:ℝ)
abbrev LedgerK:= (r:Rails)→ (N:Side) → Tulip.Male→ Pane N→ Op (Single N)
def London (n:ℕ)(δ:ℝ)(X:LedgerK)(C:ℝ):Prop:= ∀ (r:Rails)(N:Side),∀ (P:Pane N), n ≤ N.val → Guard P δ →∀ M, ‖X r N M P‖≤ C
def Strands (n:ℕ)(δ:ℝ) (A:LedgerK) (C:ℝ)(u:ℝ)(w:ℕ):Prop:=∀ (r:Rails)(N:Side)(M:Tulip.Male),∀ (P:Pane N), n≤N.val → Guard P δ →
 (∀ S T:Finset (Seat N), Distant w S T → ‖Vo S*A r N M P*Vo T‖≤C) ∧
 (∀ S:Finset (Seat N), Rightful (Lattice.halo w S) P 1 u → ‖(A r N M P-A r N M 1)*Vo S‖ ≤ C)
structure Prudence(n:ℕ)(δ:ℝ)(A:LedgerK):Prop where
 price : ∃ C:ℝ,0≤C ∧ London n δ A C
 clean (e:ℝ)(p:0<e) :∃ u:ℝ,0<u ∧∃ w:ℕ, Strands n δ A e u w
local notation "Ⲙ" => London n δ
local notation "🛟" => Prudence n δ
variable {A B:LedgerK}
lemma London.up (v:Ⲙ A u)(q:u≤η): Ⲙ A η:= fun r N P t e M=> (v r N P t e M).trans q -- spacing parser
lemma loft_rightful {S T:Finset (Seat N)} {P:Pane N} (h:Rightful S P 1 u)(p:u≤v)(e:T⊆S): Rightful T P 1 v := fun i y=> (h i (mem_filter.mpr ⟨mem_univ _,e (mem_filter.mp y).2.1,e (mem_filter.mp y).2.2⟩)).trans p
lemma Distant.drop {S T:Finset (Seat N)}(h:Distant d S T)(p:w≤d): Distant w S T:=fun _ hx _ hy=> p.trans (h _ hx _ hy)
lemma Strands.up (c:Strands n δ A u v d) (p:d≤w) (h:ζ≤v)(e:u≤η): Strands n δ A η ζ w:=fun r N M P s q=>
 ⟨fun S T z=> ((c r N M P s q).1 _ _ (Distant.drop z p)).trans e,fun S z=> ((c r N M P s q).2 _ (loft_rightful z h (Corona.halo_mono p le_rfl))).trans e⟩
lemma London.neg' (v: Ⲙ A u): Ⲙ (-A) u:=fun r N P t e M=> norm_neg _|>.trans_le (v r N P t e M)
lemma London.add' (a: Ⲙ A u)(b: Ⲙ B v): Ⲙ (A+B) (u+v):=fun r N P t e M=> (norm_add_le ..).trans (add_le_add (a r N P t e M) (b r N P t e M))
lemma London.mul' (a: Ⲙ A u)(b: Ⲙ B v): Ⲙ (A*B) (u*v):=fun r N P t e M=> (norm_mul_le ..).trans (mul_le_mul (a r N P t e M) (b r N P t e M) (norm_nonneg _) ((norm_nonneg _).trans (a r N P t e M)))
lemma Strands.neg' (p:Strands n δ A u v w): Strands n δ (-A) u v w:=by
 intro r N M P s q; simp only [Pi.neg_apply,mul_neg,neg_mul, neg_sub_neg,norm_neg]; refine ⟨(p r N M P s q).1,fun S h=>?_⟩; rw [←neg_sub (A _ _ _ _) (A _ _ _ _),neg_mul,norm_neg]; exact (p r N M P s q).2 S h
lemma Strands.add' {y:ℝ}(p:Strands n δ A u v w)(q:Strands n δ B y v w):Strands n δ (A+B) (u+y) v w:=by
 intro r N M P t h; let X:=p r N M P t h; let Y:=q r N M P t h; simp only [Pi.add_apply, mul_add,add_mul]; refine ⟨fun S T p=> (norm_add_le ..).trans (add_le_add (X.1 S T p) (Y.1 S T p)),fun S ht=>?_⟩
 rw [add_sub_add_comm,add_mul]; exact (norm_add_le ..).trans (add_le_add (X.2 S ht) (Y.2 S ht))
lemma Prudence.add' (a: 🛟 A)(b: 🛟 B): 🛟 (A+B):=by
 obtain ⟨x,v,ht⟩:=a.price; obtain ⟨y,w,hs⟩:= b.price; refine ⟨⟨x+y,add_nonneg v w,ht.add' hs⟩,fun e t=>?_⟩
 obtain ⟨u,p,j,Q⟩:=a.clean _ (half_pos t); obtain ⟨q,r,k,W⟩:= b.clean _ (half_pos t);
 exact ⟨min u q,lt_min p r,j+k,(by nth_rw 1 [←add_halves e]; exact (Q.up (Nat.le_add_right ..) (min_le_left ..) le_rfl).add' (W.up (Nat.le_add_left ..) (min_le_right ..) le_rfl))⟩
lemma Prudence.sub' (p: 🛟 A)(q: 🛟 B): 🛟 (A-B):=by
 rw [sub_eq_add_neg]; apply p.add'; obtain ⟨x,v,t⟩:=q.price; refine ⟨⟨x,v,t.neg'⟩,fun e t=>?_⟩; obtain ⟨u,v,d,Q⟩:=q.clean e t; exact ⟨u,v,d,Q.neg'⟩ -- tune
lemma Vo_board {S T:Finset (Seat N)} {Q:Op (Single N)} (p:∀ i j,Q i j≠0→ node i.1.1=node j.1.1) (h:Disjoint S T) : Vo S*Q*Vo T=0:=by
 ext i j; unfold Vo cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]; split_ifs with u v; rotate_left; all_goals first| rfl| simp only [one_mul,mul_one,mul_zero,zero_mul,Matrix.zero_apply]; -- tune
 by_contra k; exact disjoint_left.mp h ((p i j k).symm ▸ (show node i.1.1∈ S from (modes_at ..).1 u)) ((modes_at ..).1 v)
lemma Prudence.chart (Q:(r:Rails)→(N:Side)→Op (Single N))(C:ℝ) (p:0≤C)(q:∀ r N,‖Q r N‖≤C)(g:∀ r N (i j:Single N),Q r N i j≠0→ node i.1.1=node j.1.1): 🛟 fun r n _ _=> Q r n:=by
 refine ⟨⟨C,p,fun r N P t e M=> q r N⟩,fun e t=> ⟨1,by norm_num,1,fun r N M P x y=>⟨fun S T v=>?_,fun S _=>?_⟩⟩⟩
 · rw [Vo_board (g r N) (disjoint_left.mpr fun i f q=>?_),norm_zero]; exact t.le
   have hv:= v i f i q; simp at hv
 rw [sub_self,zero_mul,norm_zero]; exact t.le
lemma Prudence.id : 🛟 1:= Prudence.chart _ 1 zero_le_one (fun _ _=> norm_one.le) (fun r N i j p=> congrArg (fun t:Single N=> node t.1.1) (not_ne_iff.mp fun e=> p (Matrix.one_apply_ne e)))
lemma Prudence.tick : 🛟 (fun _ N _ _=>tickA N):=by
 apply Prudence.chart _ 1 zero_le_one (fun _ _=> (by rw [touchP]; exact (cutM_idp _).norm_le _)); intro r N i k p; rw [touchP N] at p; have h:i=k:= not_ne_iff.mp (fun e=> p (Matrix.diagonal_apply_ne _ e)); rw [h] -- cut_t open
lemma Prudence.scalar (f:Rails→ℝ)(K:ℝ) (u:0≤K)(q:∀ t,|f t|≤K): 🛟 (fun r N _ _=> f r • 1):= by
 refine Prudence.chart _ _ u (fun r N=> ?_) (fun r N i j p=> ?_);
 · rw [norm_smul,norm_one,mul_one]; exact q r
 have h:i=j:= not_ne_iff.mp (fun c=> p (by rw [Matrix.smul_apply,Matrix.one_apply_ne c,smul_zero])); rw [h]
lemma Prudence.covers (p:Procurement j n δ): 🛟 (fun _ N M P=> spar j M P):=by
 refine ⟨⟨1,zero_le_one,fun _ _ _ t q M=> ((p.audit t).projection _ q).norm_le _⟩,fun e h=>?_⟩; obtain ⟨u,v,w,V⟩:= p.haloC _ h
 exact ⟨u,v,w,fun r N M P t q=> ⟨fun S T d=> hearthB_cross (V N t) false _ q d, fun S d=> hearthB_wind (b:=false) (V N t) p.insp q d⟩⟩
lemma voL (S:Finset (Seat N))(P:Op (Single N)) : ‖Vo S*P‖ ≤ ‖P‖:= (norm_mul_le ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((cutM_idp _).norm_le _))
lemma voR (S:Finset (Seat N))(P:Op (Single N)) : ‖P*Vo S‖ ≤ ‖P‖:= (norm_mul_le ..).trans (mul_le_of_le_one_right (norm_nonneg _) ((cutM_idp _).norm_le _))
-- normal-scale product proofs
local notation "🥣" => Lattice.halo
lemma halo_encompass (w:ℕ)(S:Finset (Seat N)):Distant w (🥣 w S)ᶜ S:=fun x hx y hy=> le_of_not_gt fun p=> (mem_compl.mp hx) (halo_spec.mpr ⟨y,hy,(separation_comm x y) ▸ p.le⟩)
lemma halo_below {S T:Finset (Seat N)} (h:Distant (w+w) S T): Distant w S (🥣 w T):= by
 intro x hx y hy; obtain ⟨t,p,l⟩:= halo_spec.mp hy; have he: w+w≤ _:= h x hx t p; have hu:= separation_triangle x y t; have ht:=separation_comm y t; omega
lemma halo_twice (w:ℕ)(S:Finset (Seat N)): 🥣 w (🥣 w S) ⊆ 🥣 (w+w) S:=by
 intro x h; obtain ⟨y,p,l⟩:=halo_spec.mp h; obtain ⟨z,t,v⟩:=halo_spec.mp p; exact halo_spec.mpr ⟨z,t,(separation_triangle ..).trans (add_le_add v l)⟩
lemma vo_sum (S:Finset (Seat N)) (A B:Op (Single N)): A*Vo S*B+A*(Vo Sᶜ*B)=A*B:=by rw [Vo_neg,sub_mul,one_mul,mul_sub,mul_assoc]; abel
lemma Scruples_prod {C:ℝ} (p:Ⲙ A C)(h:Strands n δ A u v w)(q: Ⲙ B C)(g:Strands n δ B u v w)(hs:0≤C)(e:0≤u)(t:0≤δ): Strands n δ (A*B) (u*(4*C)) v (w+w):=by
 intro r N M P f ℓ; let X:=A r N M; let Y:= B r N M; have hp:= p r N P f ℓ M; have hy:= q r N P f ℓ M; have hF:= guard0 (N:=More N) t; have x:= h r N M P f ℓ; have y:= g r N M P f ℓ; simp only [Pi.mul_apply]; constructor
 · intro S T z; let V:= X P; let U:=Y P; let J:= 🥣 w T; let A':= Vo S * V; let B':= U * Vo T; change ‖Vo S * (V*U)*Vo T‖≤ _; rw [←mul_assoc, mul_assoc _ U,←vo_sum (N:=N) J A' B']; have he:= x.1 S _ (halo_below z); have ht:= y.1 _ T (halo_encompass w T); refine (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul he ((voR T _).trans hy) (norm_nonneg _) e)) ((norm_mul_le ..).trans (mul_le_mul ((voL S _).trans hp) (show ‖Vo Jᶜ*B'‖≤ u from ?_) (norm_nonneg _) hs))).trans ?_); unfold B'; rw [← mul_assoc (Vo Jᶜ)]; exact ht; nlinarith only [mul_nonneg e hs]
 intro S z; let T:= 🥣 w S; let K:= X P-X 1; have he: ‖K*Vo T‖ ≤ u:= x.2 T (loft_rightful z le_rfl (halo_twice ..)); have hx: ‖(Y P-Y 1)*Vo S‖ ≤ u:= (g.up (Nat.le_add_right w w) le_rfl le_rfl r N M P f ℓ).2 S z -- tune .up binder
 let L:= Vo S; have ht: ‖Vo Tᶜ*(Y 1*L)‖ ≤ u:= by rw [←mul_assoc]; exact (g r N M 1 f hF).1 _ _ (halo_encompass w S)
 change ‖(X P*Y P-X 1*Y 1)*L‖ ≤ _; rw [show (X P*Y P-X 1*Y 1)*L=X P*((Y P-Y 1)*L)+ K*(Y 1*L) from (by unfold K; rw [sub_mul,sub_mul, sub_mul,mul_sub]; simp only [mul_assoc]; abel), ←vo_sum T K (Y 1*L)]
 refine (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul hp hx (norm_nonneg _) hs)) ((norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul he ((voR S _).trans (q r N 1 f hF M)) (norm_nonneg _) e)) ((norm_mul_le ..).trans (mul_le_mul ((norm_sub_le ..).trans (add_le_add hp (p r N 1 f hF M))) ht (norm_nonneg _) (add_nonneg hs hs)))))).trans (Eq.le (by ring)))
lemma Prudence.mul' (p: 🛟 A)(q: 🛟 B)(e:0≤δ): 🛟 (A*B):=by
 obtain ⟨x,v,hx⟩:=p.price; obtain ⟨y,h,hy⟩:=q.price; refine ⟨⟨x*y,mul_nonneg v h,hx.mul' hy⟩,fun ε β=>?_⟩
 let C:=1+(x+y); have hp:0<C:=by unfold C; positivity
 let η:= ε/(4*C); have hs:0<η:=by unfold η; positivity
 obtain ⟨u,v',w,a⟩:=p.clean _ hs; obtain ⟨t,e',d,b⟩:=q.clean _ hs; let T:=min u t; let A:=w+d; refine ⟨min u t,lt_min v' e', A+A,?_⟩; have Hε:η*(4*C)= ε:= div_mul_cancel₀ _ (by positivity); rw [← Hε]; refine Scruples_prod (hx.up (by unfold C; linarith)) (a.up (Nat.le_add_right ..) (min_le_left ..) le_rfl) (hy.up (by unfold C; linarith)) (b.up (Nat.le_add_left ..) (min_le_right ..) le_rfl) hp.le hs.le e
lemma Prudence.closeL (E:ℝ)(h:0≤E)(x:Ⲙ A E)(t:0≤δ)(p:∀ v:ℝ,0<v →∃ X:LedgerK, 🛟 X∧ Ⲙ (A-X) v): 🛟 A:=by
 refine ⟨⟨E,h,x⟩,fun e ht=>?_⟩
 obtain ⟨X,hX,V⟩:=p _ (show 0<e/4 by positivity); obtain ⟨u,hU,w,q⟩:= hX.clean _ (half_pos ht)
 refine ⟨u,hU,w,fun r N M P v z=>?_⟩
 let L:=X r N M; let H:= A r N M; have hp:=guard0 (N:=More N) t; have he(Q:Pane N)(y:Guard Q δ): ‖H Q-L Q‖≤e/4:= V r N Q v y M; let g:=q r N M P v z;
 constructor
 · intro S T x; change ‖Vo S * H P*Vo T‖≤ _; rw [show H P=H P-L P+L P from (sub_add_cancel ..).symm,mul_add,add_mul]; exact (norm_add_le ..).trans ((add_le_add ((voR T _).trans ((voL S _).trans (he P z))) (g.1 S T x)).trans (by linarith only [ht]))
 intro S y; let K:= Vo S
 have hv: ‖((H P-L P)-(H 1-L 1))*K‖ ≤ e/4+e/4:=by apply (voR S _).trans; exact (norm_sub_le ..).trans (add_le_add (he P z) (he 1 hp))
 change ‖(H P-H 1)*K‖ ≤ _; rw [show H P-H 1=(L P-L 1)+((H P-L P)-(H 1-L 1)) from (by abel),add_mul]; exact (norm_add_le ..).trans ((add_le_add (g.2 S y) hv).trans (by linarith only [ht]))
lemma Prudence.zeroL : 🛟 0:= Prudence.chart (fun _ _=>0) 0 le_rfl (fun _ _=>norm_zero.le) (fun r N i j p=> False.elim (p rfl))
lemma Prudence.tat (F:ℕ→LedgerK) (p:∀ i, 🛟 (F i))(k): 🛟 (∑ i∈ range k,F i):=by induction k with| zero=> rw [range_zero,sum_empty]; exact Prudence.zeroL| succ k ih=> rw [sum_range_succ]; exact ih.add' (p _)
lemma Prudence.powerL (x: 🛟 A)(u:0≤δ)(k:ℕ): 🛟 (A^k):=by induction k with| zero=> rw [pow_zero]; exact Prudence.id| succ k ih=> rw [pow_succ]; exact ih.mul' x u
lemma Prudence.scaleL (x: 🛟 A)(u:0≤δ)(f:Rails→ℝ)(K:ℝ) (p:0≤K)(q:∀ t,|f t|≤K): 🛟 (fun r N M P=>f r • A r N M P):= by
 convert (Prudence.scalar (δ:=δ) (n:=n) f K p q).mul' x u using 1; funext r N M P; simp only [Pi.mul_apply, Algebra.smul_mul_assoc,one_mul]
lemma Prudence.scalec (x: 🛟 A)(u:0≤δ)(c:ℝ): 🛟 (fun r N M P=>c • A r N M P):=x.scaleL u _ _ (abs_nonneg _) (fun _=> le_rfl)
lemma geometric (t: Ⲙ (1-A) u)(v:u<1)(w:0≤u): let B:=fun r N M P=> (A r N M P)⁻¹; Ⲙ B (1-u)⁻¹ ∧ ∀ k:ℕ, Ⲙ (B - ∑ i∈range k,(1-A)^i) (u^k*(1-u)⁻¹):=by
 intro B; have he:0<1-u:=sub_pos.mpr v
 have hg: Ⲙ B (1-u)⁻¹:=by
    intro r N P f q M; let Y:= B r N M P; let X:= A r N M P; let Z:= 1-X; have hp: ‖Z‖ ≤u:=t r N P f q M; have hz:IsUnit X:=nearOne (hp.trans_lt v); have hV: Y = 1+Z*Y:=by rw [show Z=_ from rfl,sub_mul,one_mul,(live hz).1]; abel
    change ‖Y‖≤ _; rw [inv_eq_one_div,le_div_iff₀ he]; have hu:=norm_add_le (1:Op (Single N)) (Z*Y); rw [←hV,norm_one] at hu; nlinarith only [hu,(norm_mul_le ..).trans (mul_le_mul_of_nonneg_right hp (norm_nonneg Y))] -- tune
 refine ⟨hg,fun k r N P f q M=>?_⟩; let Y:= B r N M P; let X:= A r N M P; let Z:= 1-X; have hp: ‖Z‖ ≤u:=t r N P f q M; have hz:IsUnit X:=nearOne (hp.trans_lt v);
 simp only [Pi.sub_apply, Finset.sum_apply, Pi.one_apply, Pi.pow_apply]; change ‖Y-_‖ ≤ _; let F:= (∑ i∈range k,Z^i); have hu: Y-F=Z^k*Y:=by
    have ht: F*X=1-Z^k:=by
       conv_lhs=> rhs; rw [show X=1-Z from (by unfold Z; abel)]; -- ensure
       exact geom_sum_mul_neg Z k
    rw [←show F*X*Y=F from (by rw [mul_assoc, (live hz).1,mul_one]),ht,sub_mul,one_mul]; abel
 change ‖Y-F‖≤ _; rw [hu]; exact (norm_mul_le ..).trans (mul_le_mul ((norm_pow_le ..).trans (pow_le_pow_left₀ (norm_nonneg _) hp _)) (hg r N P f q M) (norm_nonneg _) (pow_nonneg w _))
lemma Prudence.revere (p: 🛟 A)(t: Ⲙ (1-A) u)(v:u<1)(w:0≤u)(z:0≤δ): 🛟 (fun r N M P=> (A r N M P)⁻¹):=by
 have h:0<1-u:=sub_pos.mpr v; obtain ⟨U,W⟩:=geometric t v w
 refine Prudence.closeL _ (by positivity) U z fun x hx=>?_; have ht:Tendsto (fun i:ℕ=>u^i*(1-u)⁻¹) atTop (𝓝 0):= by simpa only [zero_mul] using (tendsto_pow_atTop_nhds_zero_of_lt_one w v).mul_const (1-u)⁻¹
 obtain ⟨i,x⟩:= (ht.eventually (ge_mem_nhds hx)).exists; exact ⟨_,Prudence.tat _ (fun j=>(Prudence.id.sub' p).powerL z j) _,(W i).up x⟩
end YM.CF.Velvet
#print axioms YM.CF.Velvet.Prudence.mul'
#print axioms YM.CF.Velvet.Prudence.revere
