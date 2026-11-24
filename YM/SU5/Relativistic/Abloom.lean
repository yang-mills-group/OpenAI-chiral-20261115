import YM.SU5.Relativistic.Foment
/-! # finite column choice. No dimension penalty. Each captured ray is cleanly marked.
(Ignore near-dependence through projection bounds and vary price across finite additions.) -/
set_option autoImplicit false
set_option synthInstance.maxSize 12000
set_option maxHeartbeats 360000
noncomputable section
namespace YM.CF.Papyrus.Franc.Omelet
open Function Filter NormedSpace Fock Finset Thera Pea
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
variable {I:Type*}[LinearOrder I][Fintype I][Nonempty I]
def rang(x:Ket I): Op I:= Matrix.of fun i j=> (x.ofLp i)*star (x.ofLp j)
variable (x: Ket I) {v:Ket I}{P:Op I}(p:IsStarProjection P)(g:‖x‖=1) (A:Pea I) (h:A.robe*P=P)
lemma manF (v:Ket I):acts (rang x) v= inner ℂ x v • x:=by
 apply PiLp.ext; intro i; rw [act_at]; unfold Matrix.mulVec dotProduct; -- tune inner ket
 simp only [rang, Matrix.of_apply, PiLp.inner_apply, RCLike.inner_apply', WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul]; -- tune
 rw [sum_mul]; apply sum_congr rfl; intro j _; simp [mul_assoc,mul_comm,mul_left_comm]
lemma rng_sa: IsSelfAdjoint (rang x):=by ext i j; rw [Matrix.star_apply]; simp [rang,mul_comm]
include g
lemma rng_id : IsStarProjection (rang x):=by
 constructor
 · unfold IsIdempotentElem; apply op_columns; intro i; rw [act_mul,manF x (basisKet i),map_smul, manF,inner_self_eq_norm_sq_to_K,g]; simp
 exact rng_sa _
def sun (i:Bool): Pea I:=if i then ⟨rang x,0,rng_id x g,⟨mul_zero _,star_zero _⟩,mul_zero _⟩ else ⟨0,rang x,⟨mul_zero _,star_zero _⟩,rng_id x g,zero_mul _⟩
lemma sun_ro (i:Bool): (sun x g i).robe=rang x:=by unfold sun; split <;> simp [Pea.robe]
lemma sun_non : acts (rang x) x=x:=by rw [manF,inner_self_eq_norm_sq_to_K,g]; simp
omit g
def clasp(A:Pea I)(P:Op I): Prop:= A.robe*P=P
-- casing: earmarked fill/pour near P
abbrev Fair (A:Pea I)(P:Op I) (δ:ℝ):Prop:= ‖(1-P)*A.fill‖ ≤ δ ∧ ‖P*A.pour‖ ≤δ ∧ A.leak P ≤δ
lemma col_one (P:Op I) : Matrix.trace (rang x * P)= inner ℂ x (acts P x):=by
 rw [Matrix.trace_mul_comm]; unfold Matrix.trace; -- replace via bases
 apply Eq.trans (b:=∑ i:I, inner ℂ (basisKet i) (acts (P*rang x) (basisKet i))) (sum_congr rfl fun i _=>?_)
 · nth_rw 2 [←basis_expand x];
   rw [sum_inner]; apply sum_congr rfl; intro i h; rw [act_mul,manF,map_smul,inner_smul_right,inner_smul_left,←inner_conj_symm x (basisKet i),basis_inner] -- tune
 rw [basis_inner,basis_act]; rfl
include g
lemma bornF (P:Op I): ‖P*rang x‖≤ ‖acts P x‖:=by
 rw [← Matrix.l2_opNorm_toEuclideanCLM]; apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _); intro y
 change ‖acts (P*rang x) y‖≤_; rw [act_mul,manF,map_smul,norm_smul]; exact (mul_le_mul_of_nonneg_right (norm_inner_le_norm x y) (norm_nonneg _)).trans_eq (by rw [g,one_mul,mul_comm])
abbrev repay (A:Op I)(u:Bool):=if u then 1-A else A
lemma frost_pen (u:Bool){δ:ℝ}(t:‖acts (repay P u) x‖ ≤ δ) : Fair (sun x g u) P δ:=by
 let B:=rang x; let A:=repay P u
 have h:0 ≤ δ:=(norm_nonneg _).trans t; have hf:‖A*B‖≤δ:=(bornF x g A).trans t
 have hx: (B*A).trace.re ≤ δ:=by rw [show B=rang x from rfl,col_one x]; apply le_trans ((le_abs_self _).trans (Complex.abs_re_le_norm ..)); exact (norm_inner_le_norm ..).trans (by rwa [g,one_mul])
 unfold B A at hx
 cases u with
 | false=> refine ⟨?_,hf,?_⟩; dsimp [sun]; simpa using h; unfold Pea.leak Pea.frost; simpa [sun,repay] using hx -- tune
 | true=> refine ⟨hf,?_,?_⟩; dsimp [sun]; simpa using h; unfold Pea.leak Pea.frost; simpa [sun,repay] using hx
omit g
variable {A B:Pea I}
-- Control rough correlation on last vector
lemma flick{e:ℝ}(h:Fair A P e): Fair A P e:= h
include p
private lemma laneF {v:ℝ} (h: Fair A P v): ‖A.robe*P-A.fill‖ ≤2*v:=by
 let B:= A.fill; let Q:=A.pour; rw [show A.robe*P-A.fill=Q*P -B*(1-P) from (by unfold robe B Q; noncomm_ring)]
 apply (norm_sub_le ..).trans; have ht:‖Q*P‖≤ v:=by rw [←norm_star,star_mul,p.isSelfAdjoint,A.water.isSelfAdjoint]; exact h.2.1
 have hf:‖B*(1-P)‖≤v:=by rw [←norm_star,star_mul,p.one_sub.isSelfAdjoint,A.home.isSelfAdjoint]; exact h.1
 linarith
lemma eruv {v:ℝ}(h:Fair A P v)(i:Bool): ‖A.robe*repay P i - repay P i * A.robe‖ ≤ 4*v:=by
 have he:=laneF p h; let M:=A.fill
 have hv:‖P*A.robe-M‖≤2*v:=by rw [←norm_star,star_sub,star_mul,A.robe_p.isSelfAdjoint,p.isSelfAdjoint, A.home.isSelfAdjoint]; exact he
 have hx: ‖A.robe*P-P*A.robe‖≤4*v:=by rw [←sub_sub_sub_cancel_right _ _ M]; exact (norm_sub_le ..).trans (by linarith)
 cases i; exact hx
 unfold repay; dsimp; rw [mul_sub,mul_one,sub_mul,one_mul,sub_sub_sub_cancel_left, norm_sub_rev]; exact hx
omit p
lemma polo {A B:Pea I}(h:A.Zones B) : B.robe * h.fuse.robe=B.robe:=by rw [h.fuse_robe,mul_add,h.partner.fares,B.robe_p.isIdempotentElem.eq,zero_add]
lemma fair_fuse {A B:Pea I} (x:A.Zones B) (e v:ℝ) (p:Fair A P e)(q:Fair B P v): Fair x.fuse P (e+v):=by
 rw [Fair,added]; dsimp [Zones.fuse]; rw [mul_add,mul_add]; exact ⟨(norm_add_le ..).trans (add_le_add p.1 q.1), (norm_add_le ..).trans (add_le_add p.2.1 q.2.1),add_le_add p.2.2 q.2.2⟩
-- marks u supported, nearly P or Q
private abbrev LetterI(I:Type*)[LinearOrder I][Fintype I]:= Bool × Ket I
variable {S:Finset I}
abbrev spoken (S:Finset I) (u:List (LetterI I)) (P:Op I) (b e:ℝ):= ∀ x∈u, ‖acts (repay P x.1) x.2‖ ≤ e ∧ acts (cutM S) x.2=x.2 ∧‖x.2‖ ≤ b
abbrev met (s:Pea I)(X:Ket I)(e:ℝ):Prop:=‖acts (1-s.robe) X‖ ≤e
private lemma metae{v:ℝ}(h:A.Zones B)(g:met B x v): met h.fuse x v:=by
 apply le_trans _ g; let K:=1-h.fuse.robe; let V:=acts (1-B.robe) x; have hz:h.fuse.robe*B.robe=B.robe:=by rw [h.fuse_robe,add_mul,h.fares,B.robe_p.isIdempotentElem.eq,zero_add]
 change ‖acts K x‖≤_
 rw [show acts K x=acts K V from (by unfold V; rw [←act_mul,mul_sub,mul_one,show K*B.robe=0 from by unfold K; rw [sub_mul,one_mul,hz,sub_self], sub_zero])]; exact (Flare.opy ..).trans (mul_le_of_le_one_left (norm_nonneg _) (h.fuse.robe_p.one_sub.norm_le _))
include p
private lemma afford {i:Bool}{B:Pea I}{e δ C:ℝ} (u: Shell B S)(h:Fair B P δ)(sP:acts (cutM S) x=x)(hx: ‖x‖ ≤ C)(g:0≤δ)(v:‖acts (repay P i) x‖ ≤ δ)(t:0<e)(ht: e ≤ ‖acts (1-B.robe) x‖)(he: δ+ 4*δ*C ≤ (e/2)*e) : ∃ T:Pea I,T.Zones B ∧ Shell T S∧ Fair T P (e/2)∧ acts (1-(T.robe+B.robe)) x=0:=by
 let X:=1-B.robe; let U:=acts X x; let R:=cutM S; have hp:t= t:=rfl
 have hU:0< ‖U‖:=t.trans_le ht; let V:=((‖U‖:ℂ)⁻¹) • U
 have hw:‖V‖=1:=by unfold V; rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hU.le,inv_mul_cancel₀ hU.ne']
 let Z:=sun V hw i
 have hf: acts B.robe V=0:=by unfold V U; rw [map_smul,←act_mul,show B.robe*X=0 from Porth B.robe_p,act_zero,smul_zero]
 have hb: acts R U=U:=by unfold U X; rw [act_sub,act_one,map_sub,sP,←act_mul,u]
 have hk: acts R V=V:=by unfold V; rw [map_smul,hb]
 have hv: B.Zones Z:=by constructor; rw [sun_ro]; apply op_columns; intro i; rw [act_mul,manF, map_smul,hf,act_zero,smul_zero]
 refine ⟨Z,hv.partner, (show Shell Z S from ?_),frost_pen V hw i  ?_,?_⟩
 · unfold Shell; unfold Z; rw [sun_ro]; apply op_columns; intro i; rw [act_mul,manF,map_smul,hk]
 · -- tolerance
   let Q:=repay P i; have hu: ‖acts Q U‖ ≤δ+4*δ*C:=by
      unfold U; rw [←act_mul]; rw [show Q*X=X*Q+(B.robe*Q-Q*B.robe) from (by unfold X; noncomm_ring),act_add]; apply (norm_add_le ..).trans; refine add_le_add ?_ ((Flare.opy ..).trans (mul_le_mul (eruv p h i) hx (norm_nonneg _) (by linarith)))
      rw [act_mul]; exact ((Flare.opy ..).trans (mul_le_of_le_one_left (norm_nonneg _) (B.robe_p.one_sub.norm_le _))).trans v
   unfold V; rw [map_smul,norm_smul,norm_inv,Complex.norm_real,Real.norm_of_nonneg hU.le]; apply (inv_mul_le_iff₀ hU).mpr; apply (hu.trans he).trans; rw [mul_comm]; exact mul_le_mul_of_nonneg_right ht (half_pos t).le -- comm
 have hx:x= U+acts B.robe x:=by unfold U X; rw [act_sub,act_one]; abel
 have hy: acts Z.robe U= U:=by
    have he:U=(‖U‖:ℂ) • V:=by unfold V; rw [smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hU.ne'),one_smul]
    unfold Z; nth_rw 2 [he]; nth_rw 1 [he]; rw [sun_ro,map_smul,sun_non _ hw] -- tune occurrence
 have hc:Z.robe*B.robe=0:=hv.partner.fares; rw [act_sub,act_one,act_add]; rw [show acts Z.robe x=U from by nth_rw 1 [hx]; rw [map_add,hy,←act_mul,hc,act_zero,add_zero]]; rw [sub_eq_zero]; exact hx
omit p
lemma theca (C:ℝ)(M:ℕ)(p:0<C):∀ e>(0:ℝ),∃ δ>(0:ℝ),∀ {I:Type*} [LinearOrder I][Fintype I][Nonempty I]{S:Finset I}{P:Op I}(h:IsStarProjection P)(L:List (Bool× Ket I)),L.length=M →spoken S L P C δ→∃ s:Pea I,Shell s S∧ Fair s P e∧ ∀ i∈ L, met s i.2 e:=by
 induction M with
 | zero=>
    intro e h; refine ⟨_,h,fun {I} _ _ _ {S P} g L l _=> ⟨slept I,by unfold Shell; rw [slept_r,mul_zero],?_,?_⟩⟩; · unfold Fair leak Pea.frost slept; simp [h.le]
    rw [List.length_eq_zero_iff.mp l]; simp
 | succ M ih=>
   intro e h; let ν:=min (e/2) ((e/2)*e/(1+4*C)); have hx:0<ν:=lt_min (half_pos h) (by positivity); obtain ⟨δ,t,X⟩:= ih ν hx; refine ⟨_,lt_min t hx,?_⟩; intro I _ _ _ S P g L l w; cases L with
   | nil=>simp at l
   | cons i L=>
     have ht:= w _ List.mem_cons_self; obtain ⟨s,hp,hc,hS⟩:=X g L (by simpa using l) (fun i v=> by have he:=w i (List.mem_cons_of_mem _ v); exact ⟨he.1.trans (min_le_left ..),he.2⟩)
     have hv:ν≤e/2:= min_le_left ..; have hE:ν≤e:=hv.trans (half_le_self h.le); obtain ⟨v,x⟩:=i; by_cases he: met s x e
     · refine ⟨s,hp,⟨hc.1.trans hE,hc.2.1.trans hE,hc.2.2.trans hE⟩,fun i v=>?_⟩; rcases List.mem_cons.mp v with g|g; subst i; exact he; exact (hS i g).trans hE -- qualifier trans
     obtain ⟨T,d,y,u,b⟩:=afford x g hp hc ht.2.1 ht.2.2 hx.le (ht.1.trans (min_le_right ..)) h (lt_of_not_ge he).le (by have v_:= (le_div_iff₀ (show 0<1+4*C by positivity)).mp (show ν≤(e/2)*e/(1+4*C) from min_le_right ..); linarith) -- name
     · have hu:=fair_fuse d _ _ u hc; have he' : e/2+ν ≤e:=by linarith
       refine ⟨d.fuse, (Finset.union_idempotent S) ▸ Shell.double d y hp, ⟨hu.1.trans he', hu.2.1.trans he', hu.2.2.trans he'⟩,fun i v=>?_⟩ -- tune
       rcases List.mem_cons.mp v with g'|g'; subst i; change ‖acts _ x‖≤_; rw [d.fuse_robe,b,norm_zero]; exact h.le
       exact (metae i.2 d (hS i g')).trans hE
end YM.CF.Papyrus.Franc.Omelet
#print axioms YM.CF.Papyrus.Franc.Omelet.theca
