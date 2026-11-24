import YM.CF.BPress.Spin.Stride
/-! `HolePass` for P,Q at the tilted A with micro-read cost. Have already factored out offset. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter NormedSpace Finset Fock Lattice SU Lat Cube Tenant Branch Tulip Scroll Dial Thera Nacre Laic Stride Quad Blank Eye Pledge
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
namespace Hole
variable {N:Side}{j:ℕ}{A:Op (Single N)}{S:Support N}{d c η:ℝ}{B: BandWidth}{X: Bands (More N) B}

lemma small_cut {I:Type}[Fintype I][DecidableEq I](S T:Finset I)(p:S⊆T): cutM T * cutM S = cutM S:=by rw [cutM,cutM,Matrix.diagonal_mul_diagonal]; apply congrArg Matrix.diagonal; ext i; by_cases h:i∈S; simp [h,p h]; simp [h]
lemma inside (S:Support N)(u:Bool): tenureP N u*Lock S u=Lock S u:=small_cut _ _ (filter_subset ..)
def Meets (c:ℝ)(S:Support N)(A:Op (Single N)):Prop:= ∀ u:Bool, let T:=Lock S u; c • T ≤ T * sideP u A*T
lemma wage (g:0<c)(p:0≤η)(w:η≤ c) (H: Meets c S A): Meets η S A:= by intro u T; exact (smul_le_smul_of_nonneg_right w (IsStarProjection.nonneg (cutM_idp _))).trans (H u)
-- independent of w.
theorem free_budget (j:ℕ)(p:1≤j)(D:Side): ∃ c:ℝ,0<c∧ ∀{N:Side}{B:BandWidth}{X:Bands (More N) B}, B.D=D.val→ ∀ S:Support N, Dark X S→∀M:Jill.Male, Meets c S (spar j M (1:Bkg (More N))) := by
 obtain ⟨k,h,H⟩:= blank_difference j p; let m:ℝ:= (D.val:ℝ)^2; have hm:0<m:= pow_pos (Nat.cast_pos.mpr D.property) _; refine ⟨k/m,div_pos h hm,?_⟩; intro N B X v S L M u T
 let P:=tenureP N u; let W:=deltaX N; let A:=sideP u (spar j M (1:Bkg (More N))); let t:=H N M u; have hx:IsStarProjection T:=cutM_idp _; have hk:IsStarProjection P:=cutM_idp _; have eP : P*T=T:=inside ..; have eT:T*P=T:=by have ht:= congrArg star eP; rwa [star_mul,hx.isSelfAdjoint,hk.isSelfAdjoint] at ht
 have hd:T*(star (W*P)*(W*P))*T=star (W*T)*(W*T):=by nth_rw 1 [←hx.isSelfAdjoint]; rw [←mul_assoc (star _), ←star_mul, mul_assoc W,eP, mul_assoc,mul_assoc W,eP]
 have he: k • (star (W*T)*(W*T))≤ T*A*T:=by
    have hp:k • (star (W*P)*(W*P)) ≤P*A*P:= H N M u; have he:= s_mono hx.isSelfAdjoint hp; rwa [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, hd, ←mul_assoc T, ←mul_assoc T, eT,mul_assoc (T*A),eP] at he
 refine le_trans (e_le (by rw [isSelfAdjoint_iff,star_smul,hx.isSelfAdjoint,star_trivial]) (by rw [isSelfAdjoint_iff,star_smul, (IsSelfAdjoint.star_mul_self _).star_eq,star_trivial]) (fun i=>?_)) he
 rw [e_scale,e_scale,e_pow,e_proj hx,act_mul]; have hv:= Δ_bound X L u i; change ‖acts T i‖^2≤ (B.D:ℝ)^2*‖acts W (acts T i)‖^2 at hv; rw [v] at hv; refine (mul_le_mul_of_nonneg_left hv (div_pos h hm).le).trans_eq ?_; rw [←mul_assoc]; unfold m; rw [div_mul_cancel₀ _ hm.ne']

def wings (S:Support N): Support (More N):=S.image node
lemma lock_looks (u:Bool) : Lock S u*look (home N) (wings S)=Lock S u:=by
 let T:=Lock S u; have ht:= small_cut (Locks S u) (univ.filter fun i:Single N=> home N i ∈ wings S) (fun i p=> mem_filter.mpr ⟨mem_univ _, mem_image_of_mem node (mem_filter.mp p).2⟩); have hp:= congrArg star ht; rwa [star_mul,(cutM_idp _).isSelfAdjoint,(cutM_idp _).isSelfAdjoint] at hp
lemma energy_e (A:Op (Single N))(i: Ket (Single N)) : |energy A i|≤‖A‖*‖i‖^2 := (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left (norm_act ..) (norm_nonneg _)).trans_eq (by ring)))
lemma clay (u:Bool){R:Op (Single N)}(H:IsSelfAdjoint R): IsSelfAdjoint (Lock S u*(sideP u R)*Lock S u):=by let h:IsStarProjection (Lock S u):=cutM_idp _; have ht:IsSelfAdjoint (sideP u R):= by cases u; exact (show IsSelfAdjoint (1-R) from by rw [isSelfAdjoint_iff,star_sub,star_one,H]); exact H
                                                                                                           rw [isSelfAdjoint_iff, star_mul,star_mul,ht,h.isSelfAdjoint,mul_assoc]
lemma perturb (H:Meets (c+d) S A) {R:Op (Single N)}(p:IsSelfAdjoint R)(a:‖look (home N) (wings S) *(A-R)‖≤d): Meets c S R:=by
 intro u T; let D:= sideP u A; let B:= sideP u R; have he: IsStarProjection T:=cutM_idp _; have hp:=e_s (P:=T) he.isSelfAdjoint; refine e_le ?_ (clay u p) (fun i=>?_); · rw [isSelfAdjoint_iff,star_smul,he.isSelfAdjoint,star_trivial]
 let v:=acts T i; have hg: acts T v=v:=by rw [show acts T v= acts (T*T) i from (act_mul ..).symm,he.isIdempotentElem.eq]
 let A':=look (home N) (wings S)
 have hh: ‖A'*(D-B)‖ ≤ d:=by unfold D B sideP; split_ifs; exact a; rw [sub_sub_sub_cancel_left,←neg_sub A R,mul_neg,norm_neg]; exact a
 have hx: ‖T*(D-B)* T‖≤d:= by apply (norm_mul_le ..).trans; refine (mul_le_of_le_one_right (norm_nonneg _) (he.norm_le _)).trans ?_; rw [←  (show T*A'=T from lock_looks u),mul_assoc]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (he.norm_le _)).trans hh)
 have hl:= e_mono (P:= (c+d) • T) (H u) i; rw [e_scale, e_proj he, show energy (T*D*T) _=energy D v from hp ..] at hl
 have ht: energy (T*(D-B)*T) v≤ d*‖v‖^2:=(le_abs_self _).trans ((energy_e ..).trans (mul_le_mul_of_nonneg_right hx (sq_nonneg _))); rw [hp,hg,e_sub] at ht
 rw [e_scale,e_proj he,hp]; change c*‖v‖^2 ≤ energy B v; change (c+d)*‖v‖^2≤ energy D v at hl; linarith

-- tilted projection cost once Grant. `Finance` at free and all Guard. Require explicit c_P, R_P on all node bits there; physical proof late enforces with same gauge.
def shadow (j:ℕ)(M:Jill.Male)(R:Aim N)(x:Bkg (More N)):= let A:=spar j M x; tilt A (Ts R A x) 1
lemma shadow_zero{P:Pledge}(p:Shelf N d j P)(t:0≤d) (M:Jill.Male)(R:Aim N): shadow j M R 1=spar j M (1:Bkg (More N)):=by
 let V:OpenW N d:=⟨1, guard0 t⟩; unfold shadow; let A:= spar j M V.val; change tilt A (Ts R A 1) 1=A; rw [show Ts R A 1=0 from (by simp [Ts,Kennel.capT,aim_zero])]; exact tiltT 1 (p.proj M V)
lemma shadow_live {P:Pledge}(p:Shelf N d j P)(M:Jill.Male)(R:Aim N)(x:OpenW N d) : IsStarProjection (shadow j M R x.val):= (tiltR (p.proj M x) (tag_g (R.den x.val) (p.proj M x)) 1).starP
lemma shadow_tag {P W Q:Pledge}(p:Shelf N d j P)(M:Jill.Male)(R:Aim N)(h:R.toll W.rate Q.rate W.price Q.price) (g:Geometry N)(x:OpenW N d): shadow j M R (gauge g x.val)=twist (tradew N g) (shadow j M R x.val):=by dsimp only [shadow]; rw [p.tag M x g, show (Ts R _ (gauge g x.val))=twist (tradew N g) (Ts R (spar j M x.val) x.val) by rw [Ts,(aim_tag R h)]; change Kennel.capT _ _= twist _ (Kennel.capT _ _); simp [Kennel.capT], rotate_tilt (p.proj M x) (show TagG (spar j M x.val) (Ts R _ _) from tag_g (R.den x.val) (p.proj M x))] -- tune
lemma tuned_one {D I X:Type}[TopologicalSpace D][LinearOrder I][Fintype I][Nonempty I][Fintype X][DecidableEq X] (b: Stage X I D Empty) (v:ℝ) (u:‖v‖≤1): Trans.Tune b (fun _=>v) 1:= ⟨fun _=>u,one_pos,continuous_const,fun i _ x y=> by rw [sub_self,norm_zero,one_mul]; exact b.pos ..⟩
lemma shadow_budget (P Q W:Pledge): ∃ U:Pledge, ∀ {N:Side}{d:ℝ}{j:ℕ}, Shelf N d j P → ∀ M:Jill.Male,∀ R:Aim N, R.toll Q.rate W.rate Q.price W.price→ Form.Comes (AtW N d) U (shadow j M R ∘ Subtype.val):=by
 obtain ⟨U,H⟩:= buy_tilt P (priceS P Q W) Form.paid; refine ⟨U,?_⟩; intro N d j p M R t; exact H (AtW N d).full (tuned_one _ 1 (by simp)) (p.entries M) (CostS M p R t) (p.proj M) (fun x=> tag_g (R.den x.val) (p.proj M x))

-- holds also when empty, and licenses ALL subsets of unmarked sites.
def Uprice (u:ℕ)(a:ℝ)(S:Support N)(U:Bkg (More N)): Prop := chord.Close U 1 (Lattice.halo u (wings S)) a
theorem holes (P W Q:Pledge)(j:ℕ)(p:1≤j)(D:Side): ∃ (d:ℝ)(u v:ℕ)(c:ℝ), 0<d ∧ 0<c ∧ ∀{N:Side}{e:ℝ}, v≤ N.val→0≤e→Shelf N e j P→ ∀ {B:BandWidth}{X:Bands (More N) B}, B.D=D.val→∀ S: Support N, Dark X S→ ∀x:OpenW N e,Uprice u d S x.val →∀ M:Jill.Male,∀ R:Aim N,R.toll W.rate Q.rate W.price Q.price→ Meets c S (shadow j M R x.val) :=by
 obtain ⟨c,h,H⟩:= free_budget j p D; let a:=c/2; have ha:0<a:=half_pos h; obtain ⟨Y,Q'⟩:=shadow_budget P W Q; obtain ⟨k,b,B,X⟩:=latticeFieldEstimates_price Y ha; let K:=4* ν k^4; let d:= b/K; have hm:0<K:=by unfold K; have hp:=(vol_pos (w:=k)); positivity
 refine ⟨d,k,2*k+1,a,div_pos B hm,ha,?_⟩; intro N e n p' T B' L t S v x G M R r
 let F:=shadow j M R; let g:=AtW N e; let z:OpenW N e:=⟨1,guard0 p'⟩; let u:= T.proj M z
 refine perturb (A:=F z.val) (d:=a) ?_ (shadow_live T M R x).isSelfAdjoint (X (Q' T M R r) z x (wings S) ?_); · change Meets _ _ (shadow j M R 1); rw [shadow_zero T p', show a+a=c from (by unfold a; ring)]; exact H t S v M
 intro i hi; let S':=bay (terr (More N)) i k; have hl:S'⊆Lattice.halo k (wings S):=fun j hh=> halo_spec.mpr ⟨i,hi,bay_mem _ |>.1 hh⟩
 change invitation S' 1 x.val≤b; have hv:0<d:=div_pos B hm; apply (invitation.size hv.le ?_).trans; swap
 · intro r p q; rw [chord.comm]; exact G r (hl p) (hl q)
 have hx: (S'.card:ℝ)= ν k^4:= by unfold S' ν; rw [volume i (by change 2*k < N.val*2; omega)]; push_cast; ring
 rw [hx]; exact (mul_div_cancel₀ b hm.ne').le
end Hole
end YM.CF.BPress.Spin
