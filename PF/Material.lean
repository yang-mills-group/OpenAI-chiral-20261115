import PF.Pigment
/-! Matrix costs in LZ.5-- in particular must be licensed also for all endpoints (δ(node) inputs retained). Supports sizes duplicate allowed. We lump all at fixed support even in Mercator series; allows finite number at domain, price with actual l=card support even merged. Based on Branch.RootedK. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 18000
set_option maxHeartbeats 80000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.PureForce
namespace Material
open Function Filter Finset NormedSpace Fock Branch
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
attribute [local instance] opCStarAlgebra
-- E domain of linked queries at one oriented connection (allow variable past background).
variable {D I X:Type*}[TopologicalSpace D][Fintype X][Fintype I][DecidableEq X][DecidableEq I]
structure Host (X I D:Type*) where
 space : Branch.Field X
 port : I→X
 advert : Finset X→D→D→Prop
 relay {x y:Finset X}{u v:D}:x⊆y→ advert y u v→ advert x u v
-- `Bit` property keeps smooth amplitudes? continuous at least.
structure Bit (H:Host X I D)(ν:D→ℝ)(pad S:Seal X)(i j:I)(c:ℝ)(f:D→ℂ) : Prop where
 pos : 0 ≤ c
 stake : c≠0 → pad⊆S ∧ Grove H.space S ∧ H.port i∈ S ∧ H.port j∈ S
 load x:‖f x‖ ≤ c*ν x
 inputs (x y:D):H.advert S x y → f x=f y
 listens : Continuous f

structure Endor (H:Host X I D)(ν:D→ℝ)(pad S:Seal X)(M:Toll I)(A:Raw D I):Prop where
 block (i j:I): Bit H ν pad S i j (M i j) (fun x=> A x i j)

def Shot (H:Host X I D)(ν:D→ℝ)(pad:Seal X)(a r:ℝ)(A:Raw D I):Prop:=
    ∃ (Y:Seal X→Raw D I) (L:Seal X→Toll I),(∀ s:Seal X,Endor H ν pad s (L s) (Y s)) ∧ Ledger a L r ∧ ∀ x,A x=∑ s,Y s x
variable {H:Host X I D}{ν Δ:D→ℝ}{pad pad₂ S T:Seal X}{i j k:I}{a r c d:ℝ}
namespace Bit
variable {f g:D→ℂ}
lemma swap (h:Bit H ν pad S i j c f):Bit H ν pad S j i c (star ∘ f):=by
 refine ⟨h.pos,fun q=> ⟨(h.stake q).1,(h.stake q).2.1, (h.stake q).2.2.2,(h.stake q).2.2.1⟩,fun t=>?_,fun x y v=>congrArg star (h.inputs _ _ v), h.listens.star⟩
 rw [comp_apply,norm_star]; exact h.load _
lemma discount (h:Bit H ν pad S i j c f)(z:ℂ):Bit H ν pad S i j (‖z‖*c) (fun t=> z • f t):=
 ⟨mul_nonneg (norm_nonneg _) h.pos, fun v=>h.stake (right_ne_zero_of_mul v),fun t=> (norm_smul z (f t)).le.trans ((mul_le_mul_of_nonneg_left (h.load _) (norm_nonneg _)).trans_eq (mul_assoc ..).symm),fun x y v=>congrArg (z • ·) (h.inputs _ _ v),h.listens.const_smul z⟩
lemma charge (h:Bit H ν pad S i j c f)(r:Bit H ν pad S i j d g) : Bit H ν pad S i j (c+d) (fun t=>f t + g t) :=
 ⟨add_nonneg h.pos r.pos,fun v=> by by_cases t:c=0; rw [t,zero_add] at v; exact r.stake v; exact h.stake t,fun x=>by rw [add_mul]; exact (norm_add_le ..).trans (add_le_add (h.load _) (r.load _)),fun x y v=>congrArg₂ (·+·) (h.inputs _ _ v) (r.inputs _ _ v), h.listens.add r.listens⟩
lemma join (h:Bit H ν pad S i j c f)(v: Bit H Δ pad₂ T j k d g): Bit H (ν*Δ) (pad∪pad₂) (S∪T) i k (2*(c*d)) (fun x=>f x*g x):=by
 refine ⟨by have hx:=h.pos; have hg:=v.pos; positivity,?_,fun x=> ?_,fun x y p=> congrArg₂ (·*·) (h.inputs _ _ (H.relay Finset.subset_union_left p)) (v.inputs _ _ (H.relay subset_union_right p)),h.listens.mul v.listens⟩
 · intro p; obtain ⟨hs,hj,y,z⟩:= h.stake (left_ne_zero_of_mul (right_ne_zero_of_mul p)); obtain ⟨he,hv,u,w⟩:= v.stake (right_ne_zero_of_mul (right_ne_zero_of_mul p)); exact ⟨union_subset_union hs he,hj.unite hv z u,mem_union_left _ y,mem_union_right _ w⟩
 rw [norm_mul, Pi.mul_apply]; have he := h.load x; have ho:= v.load x; have hp:0≤ c*ν x:= (norm_nonneg _).trans he; have hv:0≤d*Δ x:= (norm_nonneg _).trans ho
 refine (mul_le_mul he ho (norm_nonneg _) hp).trans ?_
 linarith only [mul_nonneg hp hv]
lemma trivial: Bit H ν pad S i j 0 0:=⟨le_rfl, False.elim ∘ fun h=> h rfl,fun _=>by simp,fun _ _ _=>rfl,continuous_const⟩
lemma sumK {Y:Type*}(A:Finset Y)(c:Y→ℝ)(f:Y→ D→ℂ)(h:∀ t∈A,Bit H ν pad S i j (c t) (f t)):Bit H ν pad S i j (∑ y∈A,c y) (fun x=>∑ y∈A,f y x):=by
 classical
 induction A using Finset.induction_on with
 | empty => simp only [sum_empty]; exact trivial
 | insert a A u ih=> simp_rw [sum_insert u]; exact (h _ (mem_insert_self ..)).charge (ih (fun y p=> h y (mem_insert_of_mem p)))
end Bit
section Shot
variable {Y F:Raw D I}
namespace Shot
lemma relax (h:Shot H ν pad a r Y)(e:r≤c): Shot H ν pad a c Y:=by obtain ⟨M,K,L,T,Q⟩:=h; exact ⟨M,K,L,T.book e,Q⟩
lemma cost_pos (h:Shot H ν pad a r Y): 0 ≤ r:=by obtain ⟨_,_,_,p,_⟩:=h; exact p.posP
lemma lower (h:Shot H ν pad a r Y)(e:c≤a): Shot H ν pad c r Y:=by obtain ⟨M,K,L,T,Q⟩:=h; exact ⟨M,K,L,T.lowers (fun S i j=>mul_le_mul_of_nonneg_right (rent_up e S) ((L S).block i j).pos),Q⟩
lemma remove (h:Shot H ν pad a r Y)(e:pad₂⊆pad): Shot H ν pad₂ a r Y:=by obtain ⟨M,K,L,T,Q⟩:=h; exact ⟨M,K,fun S=>⟨fun i j=> {(L S).block i j with stake:=fun v=> let z:=((L S).block i j).stake v; ⟨e.trans z.1,z.2⟩}⟩,T,Q⟩
lemma inflate (h:Shot H ν pad a r Y)(t:0≤c)(e:∀ x,ν x≤c*Δ x): Shot H Δ pad a (c*r) Y:=by
 obtain ⟨M,K,L,P,Q⟩:=h; refine ⟨M,fun X i j=> c*K X i j,fun S=>⟨?_⟩,P.funds t,Q⟩; intro i j; let l:=(L S).block i j; exact ⟨mul_nonneg t l.pos,fun u=> l.stake (right_ne_zero_of_mul u),fun x=> (l.load x).trans ((mul_le_mul_of_nonneg_left (e x) l.pos).trans_eq (by ring)),l.inputs,l.listens⟩
lemma free: Shot H ν pad a 0 (0:Raw D I):=by
 refine ⟨0,0,(fun _=>⟨fun i j=> Bit.trivial⟩),⟨le_rfl,fun _=>?_,fun _=>?_⟩,fun _=>?_⟩ <;> simp [saleM]
lemma plus (h:Shot H ν pad a r Y)(v:Shot H ν pad a c F):Shot H ν pad a (r+c) (fun x=> Y x+F x):=by
 obtain ⟨M,K,L,P,Q⟩:=h; obtain ⟨B,D,T,O,R⟩:=v
 exact ⟨M+B,K+D,fun S=>⟨fun i j=> ((L S).block i j).charge ((T S).block i j)⟩,P.pairT O,fun x=>by change Y x+F x= _; rw [Q,R,←sum_add_distrib]; rfl⟩
lemma scale (h:Shot H ν pad a r Y)(z:ℂ) : Shot H ν pad a (‖z‖*r) (fun x=>z • Y x):=by
 obtain ⟨M,K,L,P,Q⟩:=h; exact ⟨fun S x=> z • M S x,_, fun S=>⟨fun i j=> ((L S).block i j).discount z⟩,P.funds (norm_nonneg _),fun x=>by dsimp only; rw [Q,Finset.smul_sum]⟩
lemma mono (h:Shot H ν pad a r Y)(z:ℝ): Shot H ν pad a (‖z‖*r) (fun x=>z • Y x):=by
 convert h.scale (z:ℂ) using 1
 · rw [Complex.norm_real]
 ext1 x; ext i j; simp [Complex.real_smul]
lemma neg (h:Shot H ν pad a r Y): Shot H ν pad a r (fun x=> -Y x):=by simpa using h.scale (-1)
lemma sub (h:Shot H ν pad a r Y)(v:Shot H ν pad a c F):Shot H ν pad a (r+c) (fun x=> Y x-F x):=by simpa [sub_eq_add_neg] using h.plus v.neg
lemma starP (h:Shot H ν pad a r Y): Shot H ν pad a r (fun x=> star (Y x)) := by
 obtain ⟨M,K,L,T,Q⟩:=h; exact ⟨fun S x=> star (M S x),fun S=>Function.swap (K S),fun S=>⟨fun i j=> ((L S).block j i).swap⟩,T.flip,fun x=>by dsimp only; rw [Q,star_sum]⟩
private lemma pool {J:Type*}[Fintype J](s:J→Seal X)(f:J→Raw D I)(k:J→Toll I)(h:∀ i: J,Endor H ν pad (s i) (k i) (f i))(he:0≤r)(p:∀ i:I,∑ j:I, ∑ u:J, rent a (s u)*k u i j ≤ r)(g:∀ i:I,∑ j:I,∑ u:J, rent a (s u)*k u j i ≤ r) : Shot H ν pad a r (fun v=> ∑ i:J,f i v):=by
 let M (A:Seal X)(i j:I):= ∑ t∈dest s A,k t i j
 have hu(i j:I): saleM a M i j=∑ t:J,rent a (s t)*k t i j:=by
    rw [lump s]; unfold saleM M; apply sum_congr rfl; intro S _; rw [mul_sum]; exact sum_congr rfl fun i hi=>by rw [show s i=S from (mem_filter.mp hi).2]
 refine ⟨fun A v=>∑ i∈dest s A,f i v,M,?_,⟨he,fun i=>by simpa only [hu] using (show _≤r from p i),fun i=>?_⟩,fun v=>lump s _⟩ -- simpa using? goal with hu not at using? simpa rewrites goal too
 · intro S; refine ⟨fun i j=>?_⟩
   dsimp only; simp_rw [Matrix.sum_apply]; exact Bit.sumK (dest s S) _ _ (fun t ht=> by rw [←show s t=S from (mem_filter.mp ht).2]; exact (h t).block i j) -- rw rewrites dest?
 simpa only [hu] using g i
lemma mult (h:Shot H ν pad a r Y)(t:Shot H Δ pad₂ a c F)(p:0≤a): Shot H (ν*Δ) (pad∪pad₂) a (2*(r*c)) (fun x=> Y x*F x):=by
 have he:=h.cost_pos; have hf:=t.cost_pos; obtain ⟨B,N,U,Q,V⟩:=h; obtain ⟨C,M,T,L,R⟩:=t
 let f(i:Seal X × Seal X)(x:D):= B i.1 x*C i.2 x; have hv: (fun x=>Y x*F x)= fun x=> ∑ i,f i x:=by funext x; rw [Fintype.sum_prod_type,V,R,sum_mul]; simp_rw [mul_sum]; rw [sum_comm]
 rw [hv]; refine pool (fun i=>i.1 ∪i.2) f (fun i=>Branch.charge (N i.1) (M i.2)) ?_ (by positivity)
    ?_ ?_
 · intro i; refine ⟨fun j k=>?_⟩; have hu:= Bit.sumK Finset.univ (fun t:I=>2*(N i.1 j t*M i.2 t k)) (fun (t:I) (x:D)=> B i.1 x j t * C i.2 x t k) (fun t _=>((U i.1).block j t).join ((T i.2).block t k)); exact hu
 · intro i; have hh := Branch.slope_row (w:=N) (q:=M) (a:=a) (fun S i j=> ((U S).block i j).pos) (fun S i j=> ((T S).block i j).pos) Q L p i; exact hh
 · intro i; have hh := Branch.slope_col (w:=N) (q:=M) (a:=a) (fun S i j=> ((U S).block i j).pos) (fun S i j=> ((T S).block i j).pos) Q L p i; exact hh
-- price continuity transfer from license/Ticket with H-compatibility
lemma ofRooted {G:Type*}{b:Stage X I D G}{s t:Tag b} (p:RootedK s t a c Y)(u: b.F=H.space)(v:b.home=H.port)(w:∀ S:Seal X,∀ x y,H.advert S x y→ b.eval S x y=0) : Shot H (fun _=>1) ∅ a c Y :=by
 obtain ⟨F,L,h,t,l⟩:=p; refine ⟨F,L,fun S=>⟨fun i j=>?_⟩,t,l⟩
 let f:= (h S).expo i j; refine ⟨f.positive,fun t=>⟨empty_subset _,by rw [←u,←v]; exact f.triggered t⟩,fun i=> by rw [mul_one]; exact f.bounded i,fun x y p=>?_,f.connected⟩
 have hv:= f.variation x y; rw [w S x y p,mul_zero] at hv; exact sub_eq_zero.mp (norm_le_zero_iff.mp hv)
-- use on any H, b with zero separation
lemma one : Shot H (fun _=>1) ∅ a (Real.exp a) (1:Raw D I):=by
 let V:Stage X I D Empty:= ⟨H.space,H.port,fun z=>z.elim,fun _ _ _=>0,fun _ _ _=>le_rfl,fun _ _ _=> le_rfl⟩; let s : Tag V:=⟨fun x=>x.elim,fun g=>g.elim⟩
 exact ofRooted (RootedK.oneK s _) rfl rfl fun _ _ _ _=>rfl
-- ℓ_series. uniform continuity bound via absolute label payments; require ν≤C on whole domain. retain 
-- link tags even at limit (sums);
lemma gather (g:0≤a){M:ℕ→ Raw D I}{p:ℕ→ℝ}(h:∀ n,Shot H ν pad a (p n) (M n))(v:Summable p)
    (w:∀ x,0 ≤ ν x)(r:ℝ)(z:∀ x, ν x≤ r) : Shot H ν pad a (∑' n,p n) (fun x=>∑' n,M n x):=by
 choose F U ho ht hf using h
 have he n S i j:0 ≤ U n S i j:= ((ho n S).block i j).pos
 have hy n S i j:= (ht n).price g (he n) S i j
 have hu S i j: Summable (fun n=> U n S i j):= v.of_nonneg_of_le (fun n=> he n _ _ _) (fun n=> hy n _ _ _)
 have hr n S i j x:= ((ho n S).block i j).load x
 have hv S i j x: Summable (fun n=> ‖F n S x i j‖):= ((hu S i j).mul_right (ν x)).of_nonneg_of_le (fun _=> norm_nonneg _) (fun n=> hr n _ _ _ x)
 let R (S:Seal X) (x:D):= ∑' n,F n S x
 let K (S:Seal X)(i j:I):=∑' n,U n S i j
 have hg S x: Summable (fun n=> F n S x):=kernel_sum _ fun i j=>(hv S i j x).of_norm
 have entry S x i j: R S x i j=∑' n,F n S x i j:= kernel_entry (hg S x) i j
 have unit S : Endor H ν pad S (K S) (R S) := by
    refine ⟨fun i j=> ⟨tsum_nonneg (fun n=> he n _ _ _), fun v=>?_, fun x=>?_, fun x y p=>?_,?_⟩⟩
    · by_contra l; exact v (by unfold K; simp only [show ∀ n,U n S i j=0 from fun n=>Classical.not_not.mp (fun pp=> l (((ho n S).block i j).stake pp)),tsum_zero])
    · rw [entry]; exact (norm_tsum_le_tsum_norm (hv S i j x)).trans (((hv S i j x).tsum_le_tsum (fun n=>hr n S i j x) ((hu S i j).mul_right _)).trans_eq ((hu S i j).tsum_mul_right (ν x)))
    · rw [entry,entry]; exact tsum_congr fun n=> ((ho n S).block i j).inputs x y p
    simp_rw [entry]; exact continuous_tsum (fun n=> ((ho n S).block i j).listens) ((hu S i j).mul_right r) (fun n x=>(hr n S i j x).trans (mul_le_mul_of_nonneg_left (z x) (he n S i j)))
 have hs i j : Summable (fun n=>saleM a (U n) i j):= summable_sum fun X _=> (hu X i j).mul_left _
 have hk i j : saleM a K i j= ∑' n,saleM a (U n) i j:=by
    unfold saleM K; rw [Summable.tsum_finsetSum (f:=fun S n=> rent a S*U n S i j) (fun S _=>(hu S i j).mul_left _)]; simp_rw [tsum_mul_left]
 refine ⟨R,K,unit,⟨tsum_nonneg fun n=> (ht n).posP,fun i=>?_,fun j=>?_⟩,fun x=>?_⟩
 · simp_rw [hk]; rw [←Summable.tsum_finsetSum (f:=fun j n=> saleM a (U n) i j) (fun j _=>hs i j)]; exact (summable_sum fun j (_:j∈ (univ:Finset I))=> hs i j).tsum_le_tsum (fun n=>(ht n).rows i) v
 · simp_rw [hk]; rw [←Summable.tsum_finsetSum (f:=fun i n=> saleM a (U n) i j) (fun i _=>hs i j)]; exact (summable_sum fun i (_:i∈ (univ:Finset I))=> hs i j).tsum_le_tsum (fun n=>(ht n).cols j) v
 change ∑' n,M n x=_; simp_rw [hf]; unfold R; exact Summable.tsum_finsetSum (f:=fun S n=> F n S x) (fun S _=>hg S x)
lemma squeezed (p:Shot H ν pad a r Y)(x:D)(q:0≤ν x)(t:0≤a): ‖Y x‖ ≤ r*ν x:=by
 obtain ⟨F,U,V,Z,G⟩:=p; have hf(S i j):0 ≤ U S i j:= ((V S).block i j).pos
 refine schur (fun i j=> saleM a U i j*ν x) _ _ (mul_nonneg Z.posP q) (fun i j=>?_) (fun i=>?_) (fun j=>?_)
 · rw [G,Matrix.sum_apply]; refine (norm_sum_le ..).trans ?_; unfold saleM; rw [sum_mul]; apply sum_le_sum; intro S _; exact (((V S).block i j).load x).trans (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left (hf S i j) (rent_one t S)) q)
 · rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (Z.rows i) q
 rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (Z.cols j) q
lemma power (h:Shot H ν pad a r Y)(v: 0≤a)(q:∀ i, 0≤ν i)(K:ℝ)(p:0 ≤ K)(hb:∀ i,ν i≤K)(n:ℕ): Shot H ν pad a (r*(K*(2*r))^n) (fun i=> Y i^(n+1)) :=by
 induction n with
 | zero=>simpa using h
 | succ n ih=>
   have ht:pad ∪pad=pad:=union_idempotent pad
   have hh:= (ih.mult h v).inflate (Δ:=ν) p (fun i=>by change ν i*ν i ≤ K*ν i; exact mul_le_mul_of_nonneg_right (hb _) (q i)); rw [ht] at hh; rw [pow_succ (K*_),show r*((K*(2*r))^n*(K*(2*r)))= K*(2*(r*(K*(2*r))^n*r)) by ring]; simp_rw [pow_succ _ (n+1)]; exact hh
lemma geometric (h:Shot H ν pad a r Y)(v:0≤a)(q:∀ i, 0≤ν i)(K:ℝ)(p:0 ≤ K)(hb:∀ i,ν i≤K)(ht:K*(2*r)≤1/2)(b:ℕ→ℝ)(e:∀ i,‖b i‖ ≤1):
    Shot H ν pad a (2*r) (fun i=>∑' n,b n • Y i^(n+1)):=by
 have he:=h.cost_pos; have hs(n):= (Shot.power h v q K p hb n).mono (b n)
 have hQ(n):= (hs n).relax (show ‖b n‖*(r*(K*(2*r))^n) ≤ r*(1/2:ℝ)^n from (mul_le_of_le_one_left (by positivity) (e _)).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht n) he))
 refine (gather v hQ ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left r) q K hb).relax ?_; rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; nlinarith

lemma pencil_charge (h:Shot H ν pad a r Y)(v:0≤a)(q:∀ i,0≤ν i)(K:ℝ)(p:0≤K)(hb:∀ i, ν i≤K)(ht:K*(2*r)≤1/2): Shot H ν pad a (2*r) (Branch.pencil ∘ Y):= geometric h v q K p hb ht Branch.bcoef Branch.bc_norm
lemma expon (h:Shot H ν pad a r Y)(v:0≤a)(q:∀ i, 0≤ν i)(K:ℝ)(p:0 ≤ K)(hb:∀ i,ν i≤K)(ht:K*(2*r)≤1/2) [Nonempty I]: Shot H ν pad a (2*r) (fun i=> exp (Y i)-1):=by
  have he (B:Op I): exp B-1 = ∑' n:ℕ, (↑((n+1).factorial):ℝ)⁻¹ • B^(n+1):=by
    have h: Summable (fun i:ℕ=> (↑(i.factorial):ℝ)⁻¹ • B^i):= by simpa only [expSeries_apply_eq] using NormedSpace.expSeries_summable (𝕂:=ℝ) B
    rw [exp_eq_tsum ℝ]; dsimp only; rw [←h.sum_add_tsum_nat_add 1,sum_range_one]; simp [Nat.factorial]
  simp_rw [he]; refine geometric h v q K p hb ht _ ?_; intro i; have ht:0 < (↑((i+1).factorial):ℝ):=by positivity
  simpa [Real.norm_of_nonneg ht.le] using (inv_le_one₀ ht).mpr (show 1≤(↑((i+1).factorial):ℝ) by exact_mod_cast Nat.factorial_pos _)
-- combined receipt for all e and I. e can choose arbitrary orientation frame for the pose price. Domain allowed to depend on e. Half rate still positive.
end Shot
end Shot

variable {J : Type*}[Fintype J]{pad : J→Seal X}{o:J→X}
structure Roll (H:Host X I D)(ν:D→ℝ)(pad:J→Seal X)(a r w:ℝ)(f:J→Raw D I) (M:J→ Seal X→ Raw D I)(W:J→Seal X→Toll I):Prop where
 shapes (j:J)(s:Seal X):Endor H ν (pad j) s (W j s) (M j s)
 grant (j:J): Branch.Ledger a (W j) r
 total j x:f j x=∑ S,M j S x
 row (i:I):∑ e:J,∑ j:I,saleM (a/2) (W e) i j ≤ w
 col (j:I):∑ e:J,∑ i:I,saleM (a/2) (W e) i j ≤ w
 all (e:J): ∑ i:I,∑ j:I,saleM (a/2) (W e) i j ≤ w
-- add receipts even on small H if not contractive λ. Multiple tags.
private lemma earns {s:Seal X}{i:I} (c:ℝ)(b:X)(g:c≠0→ b∈s ∧ Grove H.space s ∧ H.port i∈s)(h:0≤a)(u:0≤c):
    rent (a/2) s*c ≤ Real.exp (-a/2 * H.space.span b (H.port i)) * (rent a s*c):=by
  by_cases t:c=0; · rw [t]; simp
  obtain ⟨v,Q,k⟩:=g t; unfold rent; rw [←mul_assoc,←Real.exp_add]; gcongr; have ht: (H.space.span b (H.port i) : ℝ) ≤ s.card:=by exact_mod_cast (Q.lim b v _ k).le
  nlinarith only [mul_le_mul_of_nonneg_left ht h]

lemma booked {f:J→Raw D I}(NN:0≤r)(c:ℝ)(h:0≤a)(x:∀ e,Shot H ν (pad e) a r (f e))(w:∀ j,o j∈pad j)
    (t:∀ i:I,∑ j:J,Real.exp (-a/2 * H.space.span (o j) (H.port i)) ≤ c)(b:∀ j:J, ∑ i:I,Real.exp (-a/2 * H.space.span (o j) (H.port i)) ≤ c): ∃ M W,Roll H ν pad a r (r*c) f M W:=by
 choose M W p L V using x
 let X(j:J)(i:I):ℝ:=Real.exp (-a/2*H.space.span (o j) (H.port i)); have hv(j i):0≤ X j i:=(Real.exp_pos _).le
 have he(j:J)(i k:I):saleM (a/2) (W j) i k≤ X j i*saleM a (W j) i k ∧ saleM (a/2) (W j) i k≤ X j k*saleM a (W j) i k:=by
   simp only [saleM,mul_sum]; have ht S:= (p j S).block i k; have hb S (v:W j S i k≠0): (o j∈ S) ∧ Grove H.space S ∧ H.port i∈ S ∧ H.port k∈ S:=⟨((ht S).stake v).1 (w j),((ht S).stake v).2⟩
   exact ⟨sum_le_sum fun S _=> earns _ _ (fun v=>let hw:= hb S v; ⟨hw.1,hw.2.1,hw.2.2.1⟩) h (ht S).pos,sum_le_sum fun S _=>earns _ _ (fun v=>let hw:= hb S v; ⟨hw.1,hw.2.1,hw.2.2.2⟩) h (ht S).pos⟩ -- j implicit stripped
 have hs(e i):∑ j:I,saleM (a/2) (W e) i j≤ r*X e i:=by refine (sum_le_sum (fun j _=>(he e i j).1)).trans ?_; rw [←mul_sum,mul_comm r]; exact mul_le_mul_of_nonneg_left ((L e).rows i) (hv ..)
 have hg(e j): ∑ i:I,saleM (a/2) (W e) i j≤r*X e j:=by refine (sum_le_sum (fun i _=>(he e i j).2)).trans ?_; rw [←mul_sum,mul_comm r]; exact mul_le_mul_of_nonneg_left ((L e).cols j) (hv ..)
 -- need r≥0 assumption even J empty. add
 refine ⟨M,W,⟨p,L,V,fun i=>?_,fun j=>?_,fun e=>?_⟩⟩
 · refine (sum_le_sum (fun j _=>hs j i)).trans ?_; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (t i) NN
 · refine (sum_le_sum (fun i _=>hg i j)).trans ?_; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (t j) NN
 refine (sum_le_sum (fun i _=>hs e i)).trans ?_; rw [←mul_sum]; exact mul_le_mul_of_nonneg_left (b e) NN
-- bridge old unshift license to ambient and increments. define γ:D→ D0; etc ; actually do specialized in next file.
end Material
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.PureForce
