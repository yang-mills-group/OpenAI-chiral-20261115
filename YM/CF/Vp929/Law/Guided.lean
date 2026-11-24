import YM.CF.Vp929.Law.Revolt
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.VolumeCape
open Lattice Finset Function Metric MeasureTheory Rooms Mos Mesa Cube Lat WalkBound March
open scoped Topology Classical Matrix.Norms.Frobenius
namespace Guide
variable {L:Set Rooms}{r:Rooms→ℕ}{K:ℝ}{A:Realms}{g:Elm}{C:Side}{x y z I:Rooms}{a:Cover}{i:Axis}{B:ℕ}

lemma well_room {D:Realms}(p:Agrees x.marks A D)(v:wellF x A C K): wellF x D C K:= by
 obtain ⟨y,k⟩:=v; refine ⟨y,fun a i e=>?_⟩; rw [←p _ (spanFits.mp e).1 (spanFits.mp e).2]; exact k a i e
lemma veil_loc {D:Realms}(p:Agrees x.marks A D)(v:Veil x A C g K): Veil x D C g K:= by
 intro a i e; rw [← p (a,i) (spanFits.mp e.1).1 (spanFits.mp e.1).2]; exact v a i e
protected lemma Gallery(x:Rooms):MeasurableSet {A:Realms | wellF x A C K}:=by
 have h:IsClosed {a: Realms × Elm| Seal x a.1 C a.2 K} :=by
    unfold Seal; simp_rw [Set.setOf_forall]; apply isClosed_iInter; intro a; apply isClosed_iInter; intro i; apply isClosed_iInter; intro v; exact isClosed_le (Continuous.dist (SU.group.continuous_mat.comp (by fun_prop)) (SU.group.continuous_mat.comp (by fun_prop))) continuous_const
 rw [show {A:Realms| wellF x A C K}=Prod.fst '' {a: Realms × Elm| Seal x a.1 C a.2 K} by ext; simp [wellF]]; exact (h.isCompact.image continuous_fst).isClosed.measurableSet
lemma closedCell(x:Rooms)(K:ℝ)(C:Side)(f:Elm): IsClosed {A:Realms|Veil x A C f K}:=by
 unfold Veil; simp_rw [Set.setOf_forall]; apply isClosed_iInter; intro a; apply isClosed_iInter; intro i; apply isClosed_iInter; intro v; exact isClosed_le (Continuous.dist (SU.group.continuous_mat.comp (by fun_prop)) continuous_const) continuous_const
lemma inflate {v:Elm}(h:∀ X∈x.marks,GDist (v X) (g X) ≤1/(C.val:ℝ))(u:Veil x A C g K):Veil x A C v (K+2):=by
 intro p i a; let U:=A (p,i); let Y:=p+step i; let k:= u _ _ a; let t₁:= v p*U; let t₂:=v Y; let s₁:= g p*U; let s₂:=g Y; change GDist s₁ s₂≤_ at k; apply (dist_triangle4_right _ _ (SU.group.mat s₁) (SU.group.mat s₂)).trans; change GDist t₁ s₁+GDist t₂ s₂+GDist s₁ s₂ ≤ _; unfold GDist; unfold s₁ t₁; rw [bolt]; exact (add_le_add (add_le_add (h _ (spanFits.mp a.1).1) (h _ (spanFits.mp a.1).2)) k).trans_eq (by ring)
private lemma chartness (x:Rooms)(K:ℝ)(C:Side):∃ F:Finset Elm,∀ A:Realms,(∃ g,Veil x A C g K) → ∃ v∈ F,Veil x A C v (K+2):=by
 letI:= (Rooms.finite x).fintype; let P : Elm → ↑x.marks→SU.group.Mat:= fun y i => SU.group.mat (y i)
 have h:Continuous P:= by fun_prop
 obtain ⟨Y,g,v,H⟩:= finite_cover_balls_of_compact (isCompact_range h) (show 0< 1/(C.val:ℝ) by positivity); choose f p using fun i:Y=>g i.property
 letI:=v.fintype; refine ⟨Finset.univ.image f,?_⟩; rintro A ⟨u,q⟩; obtain ⟨z,Z,t⟩:=Set.mem_iUnion₂.mp (H (Set.mem_range_self u)); let x':Y:=⟨z,Z⟩
 refine ⟨f x',Finset.mem_image_of_mem f (Finset.mem_univ x'), inflate (fun i H=>?_) q⟩; apply (dist_le_pi_dist (P (f x')) (P u) (⟨i,H⟩: ↑x.marks)).trans; rw [p]; rw [dist_comm]; exact (mem_ball.mp t).le
private lemma runoff(x:Rooms)(K:ℝ)(C:Side):∃ v:Realms→Elm, Measurable v ∧ (∀ A, (∃ g,Veil x A C g K) → Veil x A C (v A) (K+2)) ∧∀ A B,Agrees x.marks A B → v A=v B:=by
 classical
 obtain ⟨F,g⟩:= chartness x K C; have h(F:Finset Elm):∃ v:Realms→Elm,Measurable v ∧ (∀ A,(∃ v∈F,Veil x A C v (K+2))→Veil x A C (v A) (K+2))∧∀ A B, Agrees x.marks A B → v A=v B:=by
   induction F using Finset.induction_on with
   | empty=> refine ⟨fun _=>1,measurable_const,fun _ v=>by simpa using v,fun _ _ _=>rfl⟩
   | insert i F m ih=>
       obtain ⟨v,e,h,q⟩:= ih; refine ⟨ ({A|Veil x A C i (K+2)}:Set Realms).piecewise (fun _=>i) v, Measurable.piecewise (closedCell ..).measurableSet measurable_const e,fun A u=>?_,fun A B y=>?_⟩
       · by_cases g:Veil x A C i (K+2)
         · rw [Set.piecewise_eq_of_mem _ _ _ g]; exact g
         rw [Set.piecewise_eq_of_notMem _ _ _ g]; apply h A; obtain ⟨w,p,v⟩:=u; exact ⟨w,(Finset.mem_insert.mp p).resolve_left (fun p=>g (p ▸ v)),v⟩
       have ht: Veil x A C i (K+2) ↔ Veil x B C i (K+2):=⟨fun p=>veil_loc y p,fun p=>veil_loc (fun i p q=> (y i p q).symm) p⟩; simp [Set.piecewise,ht,q A B y]
 obtain ⟨v,e,h,q⟩:=h F; exact ⟨v,e,fun A v=>h A (g A v),q⟩

abbrev ChosenF (x:Rooms)(K:ℝ)(C:Side): Realms→Elm := (runoff x K C).choose
abbrev Pick(s:March)(x:Rooms)(K:ℝ)(C:Side)(A:Realms):Elm:= kicks s⁻¹ (ChosenF (s⁻¹.follow x) K C (s.turns A))
protected lemma upper(s:March)(v:∃ g,Veil x A C g K): Veil x A C (Pick s x K C A) (K+2):=by
 obtain ⟨g,v⟩:=v; let x':=s⁻¹.follow x; let q:= (runoff x' K C).choose_spec.2.1 (s.turns A) ⟨s.kicks g,s.spin_veil A g (by rw [show s.follow x'=x from foll_right ..]; exact v)⟩
 have ht:=s⁻¹.spin_veil (s.turns A) ((runoff x' K C).choose (s.turns A)) (X:=x) q; rw [s.turnBack] at ht; exact ht
lemma rateTurn(s v:March)(x:Rooms): Pick v x K C (s.turns A)= s.kicks (Pick (s*v) (s.follow x) K C A):=by unfold Pick; rw [show (s*v)⁻¹.follow (s.follow x)=v⁻¹.follow x from by simp,turnChain,←kickChain]; rw [show (s*v)⁻¹ * s = v⁻¹ from by group]
private lemma scm (s:March)(D:Realms)(v:Agrees x.marks A D) : Agrees (s⁻¹.follow x).marks (s.turns A) (s.turns D):=by
 intro i t v'; rw [←Step.pos_read (s.turns A) i.1 i.2,←Step.pos_read (s.turns D) i.1 i.2,s.ladder,s.ladder]; have e:= (s.stride_le _ _).2 (show span i.1 _ ≤ _ from spanFits.2 ⟨t,v'⟩); change s.follow (span i.1 (i.1+(posDir i.2).vec)) ≤ _ at e; rw [← s.lane_z (posDir i.2) i.1,s.foll_right] at e
 let h:= v (s.lane (posDir i.2) i.1) (spanFits.mp e).1 (spanFits.mp e).2; unfold March.lane at h; unfold Step.read; congr 1; rw [h]
lemma rateLocal(s:March)(D:Realms)(p:Agrees x.marks A D): Pick s x K C A=Pick s x K C D:= congrArg (kicks s⁻¹) ((runoff _ K C).choose_spec.2.2 _ _ (scm s D p))
lemma kicksC(s:March):Continuous (March.kicks s):=by
 apply continuous_pi; intro i; exact (Skye.rev_C _).comp (continuous_apply _)
lemma turnsC(s:March):Continuous (turns s):=by
 apply continuous_pi; rintro ⟨x,i⟩; let k:=(posDir i).rotate s.step; let U:=s.slide x
 refine (Skye.rev_C _).comp (show Continuous (fun (g:Realms)=> k.read g U) from ?_); unfold Step.read; split; exact (continuous_apply _).inv; exact continuous_apply _
lemma pickProof(s:March)(x:Rooms)(K:ℝ)(C:Side):Measurable (Pick s x K C):= (kicksC s⁻¹).measurable.comp ((runoff _ K C).choose_spec.1.comp (turnsC s).measurable)
end Guide
end YM.CF.VolumeCape
