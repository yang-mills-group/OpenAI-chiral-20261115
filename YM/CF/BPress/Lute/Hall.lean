import YM.CF.BPress.Lute.Floor
/- SU smooth extension from 2d partial data. actual dictionary edges compatibility first into ambient linear coordinates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Lute.Fort
open Function Filter NormedSpace Complex Metric Spin InnerProductSpace Fock Mesa Smooth Module MeasureTheory Set
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator Kronecker InnerProductSpace Classical ENNReal
attribute [local instance] opCStarAlgebra
variable {X : Type}[NormedAddCommGroup X][NormedSpace ℝ X]
structure Lodge (s t:Set X): Prop where
 takes : s⊆ t
 room : IsCompact s
 width : dimH s<3
 offers {A:Type} [NormedAddCommGroup A][NormedSpace ℝ A](f:X→A): Friendly s f→∃ g:X→A,Friendly t g ∧ EqOn g f s
lemma squareU : Lodge sqY sqX:=by
 refine ⟨inter_subset_left,edgeC,?_ ,?_⟩; · apply (dimH_mono (subset_univ _)).trans_lt; rw [Real.dimH_univ_eq_finrank, Module.finrank_prod]; norm_num
 intros; apply cover <;> assumption
abbrev Nodes : Set ℝ:= {0,1}
lemma intervalU : Lodge Nodes Hotel:=by
 refine ⟨fun x p=>?_,?_ ,?_,?_⟩; · rcases (show x=0∨x=1 by simpa [Nodes] using p) with rfl|rfl; exact H0; exact H1
 · exact Set.Finite.isCompact (show Nodes.Finite from finite_insert.mpr (finite_singleton _))
 · rw [(show Nodes.Finite from finite_insert.mpr (finite_singleton _)).dimH_zero]; norm_num -- braces inference
 intro Y _ _ A h; refine ⟨fun x=> plank x (A 0) (A 1), fun i _=>?_ ,fun i h=>?_⟩; · unfold plank; fun_prop
 rcases (show i=0∨i=1 by simpa [Nodes] using h) with rfl|rfl; exact (palm ..).1; exact (palm ..).2
namespace Lodge
variable {s t:Set X}{n:ℕ}(P:Lodge s t) (A:X→Keys n)
include P
lemma sphere_room {E:Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E](u:E)(a:‖u‖=1) (f:X→E)(c:Friendly s f)(h:∀ x∈s,‖f x‖=1 ∧ f x≠u): ∃ g:X→ E, Friendly t g ∧ EqOn g f s ∧ ∀ x∈t,‖g x‖=1 ∧ g x≠u:=by
 let k:=stereoToFun u; let T:=(ℝ ∙ u)ᗮ; let l(v:↥T):= stereoInvFunAux u v.val
 have cx:Friendly s (k ∘ f):=by
    intro x p
    refine ContDiffAt.comp x (contDiffOn_stereoToFun.contDiffAt (?_ : {x : E|innerSL ℝ u x≠(1:ℝ)}∈𝓝 (f x))) (c _ p); apply (isOpen_ne.preimage (innerSL ℝ u).continuous).mem_nhds; intro e; change inner ℝ u (f x)=1 at e
    apply (h x p).2; apply sub_eq_zero.mp; apply norm_eq_zero.mp; have ht:= norm_sub_sq_real u (f x); rw [a,e,(h x p).1,norm_sub_rev u] at ht; nlinarith
 obtain ⟨F,H,hF⟩:= P.offers (k ∘ f) cx; refine ⟨l∘F,fun x p=>?_,fun x p=>?_,fun x _=>?_ ⟩ -- typo
 · exact ((contDiff_stereoInvFunAux.comp T.subtypeL.contDiff).contDiffAt).comp x (H _ p)
 · have hx: f x ∈ sphere 0 1:= mem_sphere_zero_iff_norm.mpr (h x p|>.1); rw [comp_apply,hF p]; exact congrArg Subtype.val (stereo_left_inv a (x:=⟨_,hx⟩) (h x p).2) -- direction
 · exact ⟨mem_sphere_zero_iff_norm.mp (stereoInvFunAux_mem a (show (F x).val∈T from (F x).property)),fun t=> stereoInvFun_ne_north_pole a (F x) (Subtype.ext t)⟩

theorem principalSU (n:ℕ)(A:X→Keys (n+1))(h:Friendly s A)(t':∀x∈s,trueS (A x)): ∃ B:X→Keys (n+1), Friendly t B∧ EqOn B A s ∧ ∀ x∈t,trueS (B x):=by
 rcases s.eq_empty_or_nonempty with hs|hs; exact ⟨fun _=>1,fun _ _=>contDiffAt_const,by simp [hs],fun _ _=>suit_one⟩
 induction n with
 | zero=>
   refine ⟨fun _=>1,fun _ _=>contDiffAt_const,fun i p=>?_,fun _ _=>suit_one⟩; have he: (A i).det=1:=(t' _ p).2; ext j k; fin_cases j; fin_cases k; simpa using he.symm
 | succ n ih=>
   let N:=n+1+1; let i:Fin N:=0; let T:= Ket (Fin N); let a:=shaft i (1:Keys N); let x:=shaft i ∘ A; have ha(T:Keys N)(h:trueS T):‖shaft i T‖=1:=shaft_norm T h i; have hd:Friendly s x:=fun y p=> (s_smooth i _).comp y (h _ p)
   obtain ⟨K,k⟩:= Smooth.lip_near P.room (fun x h=> (hd _ h).of_le (by simp)); -- tune
   obtain ⟨η,B,t₀,p⟩:=avoidance a (ha _ suit_one) s P.room K (n:=2*n+3) (by rw [← Module.finrank_mul_finrank ℝ ℂ,finrank_euclideanSpace,Fintype.card_fin,Complex.finrank_real_complex]; unfold N; ring) (P.width.trans_le (by exact_mod_cast (show 3≤2*n+3 by omega)))
   obtain ⟨u,_,q⟩:=p s (subset_refl _) hs x k (fun y hy=>ha _ (t' _ hy)); obtain ⟨R,T,ht⟩:=reachable i 1 (Ne.symm (Fin.succ_ne_zero (0:Fin (n+1)))) u.val (by simpa using u.property)
   have hu:shaft i R=u.val:=WithLp.ofLp_injective _ (by exact ht)
   have hn:‖u.val‖=1:=by simpa using u.property
   obtain ⟨F,H,u',v⟩:= P.sphere_room u.val hn x hd (fun y hy=>⟨ha _ (t' y hy),dist_pos.mp (t₀.trans_le (q _ hy))⟩); let G(y:X):=dock u.val (F y) 1 R
   have he(y)(b:y∈t):trueS (G y)∧shaft i (G y)=F y∧ContDiffAt ℝ ∞ G y:=by obtain ⟨p,h⟩:=v y b; obtain ⟨e,a,u⟩:=dock_ball (b:=F y) (j:=1) (Ne.symm (Fin.succ_ne_zero (0:Fin (n+1)))) T hn hu p (Ne.symm h); exact ⟨e,a,u.comp y (H y b)⟩
   let Y(y:X):=star (G y)*A y; have ht(y)(b:y∈s):trueS (Y y)∧ Y y=layer (aside (Y y)):=by
      obtain ⟨p,h,y'⟩:=he y (P.takes b); have f:trueS (Y y):=suit_mul (suit_star p) (t' y b); refine ⟨f,layer_flat f (show shaft i (Y y)=_ from ?_)⟩; unfold Y; rw [shaft_back,show shaft i (A y)= shaft i (G y) from (u' b).symm.trans h.symm, ←shaft_back, show star (G y)* G y=1 from p.1.1]

   obtain ⟨B,H,r,w⟩:= ih (aside∘Y) (fun y hy=> (a_smooth (Y y)).comp y (((star_smooth (G y)).comp y (he y (P.takes hy)|>.2.2)).mul (h y hy))) (fun y b=> (suit_layer _).mp ((ht y b).2 ▸ (ht y b).1)); let Z(y:X):=G y*layer (B y); refine ⟨Z,fun y b=> (he y b).2.2.mul ((l_smooth _).comp y (H y b)), fun i p=>?_ ,fun y b=>suit_mul (he y b).1 ((suit_layer _).mpr (w y b))⟩
   unfold Z; rw [r p,comp_apply,←(ht i p).2]; unfold Y; rw [←mul_assoc, show G i *star (G i)=1 from (he i (P.takes p)).1.1.2,one_mul]
-- all our SU groups sized and nonempty
variable {K:Type}[Fintype K][DecidableEq K][Nonempty K]
lemma key (A:X→Op K)(h:Friendly s A)(u:∀ x∈s,trueS (A x)) : ∃ B:X→Op K,Friendly t B ∧ EqOn B A s ∧ ∀ x∈ t,trueS (B x):=by
 let n:=Fintype.card K-1; have hp: n+1=Fintype.card K:=Nat.sub_add_cancel Fintype.card_pos
 let e:K≃Fin (n+1):= Fintype.equivOfCardEq (by rw [Fintype.card_fin,hp]); let f(V:Op K):Keys (n+1):=refit e V
 have he {I J:Type}[DecidableEq I][DecidableEq J][Fintype I][Fintype J](e:I≃J)(x:Op I)(t:trueS x):trueS (refit e x):=⟨(renU e ⟨x,t.1⟩).property,(refit_ne ..).trans t.2⟩
 have h' {I J:Type}[DecidableEq I][DecidableEq J][Fintype I][Fintype J](e:I≃J)(x:Op I): ContDiffAt ℝ ∞ (refit e) x:=Lute.mat_smooth _ _ fun i j=> (key_entry _ _).contDiffAt -- tune
 obtain ⟨G,H,g,P'⟩:=P.principalSU n (f ∘ A) (fun i p=> (h' e _).comp i (h i p)) (fun i p=>he _ _ (u i p)); refine ⟨fun i=> refit e.symm (G i),fun i p=>(h' e.symm _).comp i (H i p), fun i p=>?_,fun i t=>he _ _ (P' i t)⟩; dsimp only; rw [g p]; exact refit_back e.symm (A _)
omit P [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma key_path (A B:Op K)(h:trueS A)(g:trueS B):∃ f:ℝ→ Op K, Friendly Hotel f∧ f 0=A∧ f 1=B∧∀ x∈ Hotel,trueS (f x):=by
 let f(t:ℝ):= plank t A B; obtain ⟨F,H,T,w⟩:= intervalU.key f (fun i p=>by unfold f plank; fun_prop) (fun i p=>by rcases (show i=0∨i=1 by simpa [Nodes] using p) with rfl|rfl; rwa [show f 0=A from (palm A B).1]; rwa [show f 1=B from (palm A B).2]); exact ⟨F,H,(T (show (0:ℝ)∈Nodes by simp [Nodes])).trans (palm A B).1,(T (show (1:ℝ)∈Nodes by simp [Nodes])).trans (palm A B).2,w⟩ -- tune
end Lodge
end YM.CF.BPress.Lute.Fort
