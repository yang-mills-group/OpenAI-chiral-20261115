import YM.CF.BPress.Lute.Hall
/-! Connectivity of the real stabilizer. Real Stone category within Op Slot, including lifts through negative det correction. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Lute.Fort
open Function Filter Finset NormedSpace Metric Mesa Spin InnerProductSpace Fock Complex
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
namespace Oak
variable {K:Type}[Fintype K][DecidableEq K] {n:ℕ} {V:Op K}
-- real as fixed set of all coordinates
def pupil (K:Type)[Fintype K]: Submodule ℝ (Ket K) where
 carrier := {x|star x.ofLp=x.ofLp}
 zero_mem' := by simp
 add_mem' := by intro x y a b; change star _=_; rw [WithLp.ofLp_add,star_add,a,b]
 smul_mem' c x h:= by change star _=_; rw [WithLp.ofLp_smul,star_smul,h,star_trivial]; -- tune
structure Stone (A: Op K) : Prop where
 rim : trueS A
 realC : cc A=A
abbrev Fib(K:Type)[Fintype K]:= ↥(pupil K)
lemma pp0 (i:K): basisKet i ∈ pupil K:= by change _=_; funext j; by_cases h:i=j <;> simp [basisKet,h,Ne.symm,Pi.single_apply] -- inspect
lemma pp_k (u:Fib K)(j:K):star (u.val.ofLp j)=u.val.ofLp j:=congrFun u.property j
lemma school(h:Stone V)(i:K): shaft i V∈ pupil K:=by
 change star (V *ᵥ Pi.single i 1)=(V *ᵥ Pi.single i 1); rw [Matrix.mulVec_single_one]; exact funext fun j=> Matrix.ext_iff.mpr h.realC j i
lemma rotary_k (x y:Fib K): cc (rotary x.val y.val)=rotary x.val y.val:=by
 rw [r_def,cc_sub,cc_one, cc_smul,star_inv₀]; have hp:cc (plate ((x-y:Fib K):Ket K))= plate ((x-y:Fib K):Ket K):= by -- specify tune
    ext i j; rw [cc_apply]; change star (_*star ((x-y).val.ofLp j))=_; unfold plate; simp only [Matrix.of_apply]; simp_rw [pp_k,star_mul,pp_k]; ring -- order tune
 have he:star (inner ℂ (x.val-y.val) x.val)=inner ℂ (x.val-y.val) x.val:=by
    change star (inner ℂ (x-y).val x.val)=_; simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,Pi.star_apply, star_sum]; apply sum_congr rfl; intro i _; rw [star_mul]; simp_rw [pp_k]; rw [show x.val-y.val=(x-y).val from rfl, pp_k, mul_comm]
 rw [he,show x.val-y.val=(x-y).val from rfl,hp]
lemma wrap_k(j:K)(p:cc V=V) : cc (wrapR j V)=wrapR j V:=by
 have hp:star V.det=V.det:=by rw [cc] at p; rw [←Matrix.det_conjTranspose]; exact Matrix.det_transpose .. |>.symm|>.trans (congrArg Matrix.det p) -- tune
 unfold wrapR; rw [cc_mul, p]; congr 1; ext i j; by_cases h:i=j; · subst i; simp_rw [cc_apply,Matrix.diagonal_apply_eq]; split <;> simp [hp];
 simp [h]
lemma dock_k {x y:Fib K}(j:K)(h:cc V=V): cc (dock x.val y.val j V)=dock x.val y.val j V:=wrap_k j (by rw [cc_mul,rotary_k,h]) -- tune
lemma reach (i j:K)(h:i≠j)(b:Fib K)(p:‖b‖=1) : ∃ V: Op K, Stone V∧shaft i V=b.val:=by
 let a:Fib K:=⟨basisKet i,pp0 i⟩; let A:Op K:=1; have ht:trueS A:= suit_one; have he:shaft i A=a.val:=by unfold shaft A; rw [Matrix.one_mulVec]; rfl
 by_cases hk:a=b; · exact ⟨A,⟨ht,cc_one⟩,hk ▸ he⟩
 have hz:‖a.val‖=1:= by simp [a]
 obtain ⟨e,v,x⟩:=dock_ball h ht hz he (show ‖b.val‖=1 from p) (fun b=> hk (Subtype.ext b)); exact ⟨_,⟨e,dock_k (x:=a) (y:=b) j cc_one⟩,v⟩
lemma pupil_case(i j:K)(h:i≠j)(x y:Fib K): ∃ v:Fib K, ‖v‖=1 ∧ x ≠ v ∧ y≠v:=by
 let f(a:K):Fib K:=⟨basisKet a,pp0 _⟩; let A:=f i; let B:=f j; have hp(v:K):‖f v‖=1:=by change ‖basisKet v‖=1; simp
 suffices a : A ≠B ∧ -A≠B ∧ A≠ -A by
    by_cases p:x=A; swap
    · by_cases g:y=A; swap; · exact ⟨A,hp _,p,g⟩
      by_cases q:x=B; subst x; subst y; exact ⟨-A,(by rw [norm_neg]; exact hp _),a.2.1.symm,a.2.2⟩; exact ⟨B,hp _,q,g ▸ a.1⟩
    by_cases q:y=B; subst x; subst y; exact ⟨-A,(by rw [norm_neg]; exact hp _),a.2.2,a.2.1.symm⟩; exact ⟨B,hp _,p ▸ a.1,q⟩
 have C (V W:Fib K)(p:V=W):V.val.ofLp i=W.val.ofLp i:=congrArg (fun x:Fib K=> x.val.ofLp i) p
 refine ⟨?_,?_,?_⟩; all_goals intro p; have hb:= C _ _ p; norm_num [A,B,f,basisKet,h,Ne.symm h] at hb -- tune p3 B unfold
lemma first (A B:Op K)(h:Stone A)(p:Stone B)(i j:K)(u:i≠j): ∃ C:ℝ→Op K,Friendly Hotel C∧(∀ x∈Hotel,Stone (C x))∧shaft i (C 0)=shaft i A∧shaft i (C 1)=shaft i B:=by
 let a:Fib K:=⟨shaft i A,school h i⟩; let b:Fib K:=⟨shaft i B,school p i⟩; obtain ⟨v,e,t,q⟩:= pupil_case i j u a b
 have he (A:Op K)(h:trueS A):‖shaft i A‖=1:=by nth_rw 1 [show shaft i A=jet A (basisKet i) from rfl]; rw [jet_norm _ h.1]; simp
 have hx(x:ℝ)(p':x∈ Nodes): ‖plank x a b‖=1∧ plank x a b≠ v:=by
    rcases (show x=0∨x=1 by simpa [Nodes] using p') with rfl|rfl; rw [(palm ..).1]; exact ⟨he _ h.rim,t⟩; rw [(palm ..).2]; exact ⟨he _ p.rim,q⟩
 obtain ⟨F,H,g,W⟩:= Lodge.sphere_room intervalU v e (fun x=> plank x a b) (fun y p=>by unfold plank; fun_prop) hx
 obtain ⟨Q,r,f⟩:= reach i j u v e; let R(x:ℝ):=dock v.val (F x).val j Q; have hv(x)(p:x∈Hotel): Stone (R x)∧shaft i (R x)=(F x).val∧ ContDiffAt ℝ ∞ R x:=by
    obtain ⟨h,b,t⟩:=dock_ball u r.rim (show ‖v.val‖=1 from e) f (show ‖(F x).val‖=1 from (W _ p).1) (fun t=> (W _ p).2 (Subtype.ext t.symm)); exact ⟨⟨h,dock_k (x:=v) (y:=F x) j r.realC⟩,b,t.comp (g:=fun z=>dock v.val z j Q) x ((pupil K).subtypeL.contDiff.contDiffAt.comp x (H x p))⟩
 refine ⟨R,fun x h=> (hv x h).2.2,fun x h=> (hv x h).1,(hv 0 H0).2.1.trans (congrArg Subtype.val ((g (show (0:ℝ)∈Nodes by simp [Nodes])).trans (palm ..).1)),(hv 1 H1).2.1.trans (congrArg Subtype.val ((g (show (1:ℝ)∈Nodes by simp [Nodes])).trans (palm ..).2))⟩
lemma stoneP{V U:Op K}(h:Stone V)(p:Stone U): Stone (V*U):=⟨suit_mul h.rim p.rim,by rw [cc_mul,h.realC,p.realC]⟩
lemma stoneS(p:Stone V):Stone (star V):=⟨suit_star p.rim,by rw [cc_star,p.realC]⟩
lemma stoneT(K:Keys n)(p:Stone K):Stone (layer K):=by refine ⟨(suit_layer K).mpr p.rim,?_⟩; have ht:= p.realC; ext i j; refine Fin.cases ?_ (fun i=>?_) i <;> refine Fin.cases ?_ (fun j=>?_) j <;> first| exact Matrix.ext_iff.mpr ht _ _ | simp -- tune

theorem gate(n:ℕ)(A B:Keys (n+1))(h:Stone A)(p:Stone B): ∃ X:ℝ→Keys (n+1),Friendly Hotel X ∧ X 0=A∧ X 1=B∧∀ x∈ Hotel, Stone (X x):=by
 induction n with
 | zero=>
   have ht(V:Keys 1)(h:Stone V):V=1:=by have he: V.det=1:=h.rim.2; ext i j; fin_cases i; fin_cases j; simpa using he
   exact ⟨fun _=>A,fun _ _=>contDiffAt_const,rfl,(ht A h).trans (ht B p).symm,fun _ _=>h⟩
 | succ n ih=>
   let N:=n+1+1; obtain ⟨C,H,T,g,f⟩:= first A B h p 0 1 (Ne.symm (Fin.succ_ne_zero (0:Fin (n+1)))) -- tune binder order
   have ht(V U:Keys N)(p:Stone V)(t:Stone U)(h:shaft 0 U=shaft 0 V): let f:= aside (star U*V); V=U*layer f∧Stone f:=by
      intro f; let W:=star U*V; have hw:= stoneP (stoneS t) p; have hx:W=layer f:=by apply layer_flat hw.rim; rw [shaft_back,←h,←shaft_back,show star U*U=1 from t.rim.1.1]
      refine ⟨by rw [←hx]; unfold W; rw [←mul_assoc,t.rim.1.2,one_mul],(suit_layer f).mp (hx ▸ hw.rim),?_⟩; ext i j; exact Matrix.ext_iff.mpr hw.realC i.succ j.succ
   obtain ⟨g,a⟩:=ht A (C 0) h (T 0 H0) g; obtain ⟨f,b⟩:=ht B (C 1) p (T 1 H1) f; obtain ⟨X,S,u,x,hx⟩:= ih _ _ a b; exact ⟨fun i=> C i*layer (X i),fun x h=> (H x h).mul ((l_smooth _).comp x (S x h)),(by dsimp only; rw [u]; exact g.symm),(by dsimp only; rw [x]; exact f.symm),fun x h=>stoneP (T x h) (stoneT (X x) (hx x h))⟩
lemma route {V W:Op K}[Nonempty K](p:Stone V)(t: Stone W): ∃ X:ℝ→Op K,Friendly Hotel X∧ X 0=V∧ X 1=W∧∀ x∈ Hotel,Stone (X x):=by
 let n:=Fintype.card K-1; have hp: n+1=Fintype.card K:=Nat.sub_add_cancel Fintype.card_pos; let e:K≃Fin (n+1):= Fintype.equivOfCardEq (by rw [Fintype.card_fin,hp])
 have he {I J:Type}[DecidableEq I][DecidableEq J][Fintype I][Fintype J](e:I≃J)(x:Op I)(t:Stone x):Stone (refit e x):=⟨ ⟨(renU e ⟨x,t.rim.1⟩).property,(refit_ne ..).trans t.rim.2⟩,by rw [cc,←map_star,←refit_T]; exact congrArg _ t.realC⟩
 obtain ⟨G,H,g,r,h⟩:=gate n _ _ (he e V p) (he e W t); let R:=fun x=> refit e.symm (G x); refine ⟨R,fun x h=>?_ ,?_,?_,fun i t=>he _ _ (h i t)⟩; exact (Lute.mat_smooth _ _ (fun i j=> (key_entry _ _).contDiffAt:∀ i j, ContDiffAt ℝ ∞ (fun x:Keys (n+1)=> refit e.symm x i j) (G x))).comp x (H x h); rw [show R 0=refit e.symm (G 0) from rfl,g]; exact refit_back e.symm _; rw [show R 1=refit e.symm (G 1) from rfl,r]; exact refit_back e.symm _ -- defeq
end Oak
end YM.CF.BPress.Lute.Fort
