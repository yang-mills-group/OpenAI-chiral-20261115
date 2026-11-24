import YM.CF.Mesa.Topcoat
/-! Recurrence of the filling gauge on all active cells. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Filter Metric Lattice CF.Cube Lat
open scoped Topology NNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {m B:Side} {a b c: Index m}

private abbrev Top (n:ℕ)(p:Edge (Site (Domain m B))):Prop:= ∃ a:Index m, degree m a=n∧Plug a p∧∀ b,Lesser b a→¬ Plug b p
private def Applies (n:ℕ)(X:Au m B→Au m B)(K:ℝ):Prop:=Measurable X ∧ ∀ b:Index m,
   (∀ U V :Au m B, Agrees (room m B b) U V→ Agrees (room m B b) (X U) (X V))∧
   (∀ U:Au m B, well b U 1→ Agrees (room m B b) (X U) U) ∧
    ∀ U:Au m B, degree m b<n→ well b (X U) K
private lemma stucco (n:ℕ):∃ N:ℕ,∃ K:ℝ,1≤K ∧∀ m B:Side,N≤B.val→ 2≤m.val →∃ X:Au m B→Au m B, Applies n X K:=by
  classical
  induction n with
  | zero => exact ⟨0,1,le_rfl,fun _ _ _ _=>⟨id,measurable_id,fun b=>⟨fun _ _ t=>t,fun _ _ _ _ _=>rfl,fun _ h=>by omega⟩⟩⟩
  | succ n ih =>
    obtain ⟨N,K,t,P⟩:=ih; obtain ⟨L,R,hL,H⟩:= bed_budget 5 K (zero_le_one.trans t)
    let K':=max K (L+2)
    refine ⟨max N R,K',t.trans (le_max_left ..),fun m B hG hm=>?_⟩
    obtain ⟨X,hX,ht⟩:= P m B ((le_max_left ..).trans hG) hm; choose Y hY l Z using fun a:Index m=>fixB (B:=B) a L
    let F (p:Edge (Site (Domain m B)))(U: Au m B) :SU.E:= if h:Top n p then
       let a:=h.choose
       if well a U 1 then U p else (Y a (X U) p.1)⁻¹*Y a (X U) (p.1+step p.2)
      else X U p
    let W (U:Au m B): Au m B:=fun p=> F p U
    have Yx (p:Edge (Site (Domain m B)))(h:Top n p)(b:Index m)(g:Plug b p):Fits m h.choose b:=by
      obtain ⟨i,t,r,f⟩:=overlap hm h.choose_spec.2.1.1 g.1
      by_cases hp:i=h.choose; rwa [hp] at r
      have Hx:=h.choose_spec.2.2 i ⟨t,hp⟩ ⟨f p.1 h.choose_spec.2.1.1 g.1,f _ h.choose_spec.2.1.2 g.2⟩; contradiction
    refine ⟨W, measurable_pi_lambda _ (fun i=>?_),fun b=> ⟨?_,?_,?_⟩⟩
    · change Measurable (fun U=>F i U); unfold F; split
      · exact Measurable.ite (well_closed ..|>.measurableSet) (measurable_pi_apply _) ((((measurable_pi_apply i.1).comp ((hY _).comp hX)).inv).mul ((measurable_pi_apply _).comp ((hY _).comp hX)))
      exact (measurable_pi_apply _).comp hX
    · intro U V h p y z; let f:= (ht b).1 U V h
      change F p U=F p V; unfold F; by_cases g:Top n p
      swap; simpa only [dif_neg g] using f p y z
      let a:=g.choose; rw [dif_pos g,dif_pos g]
      have he:= Yx p g b ⟨y,z⟩
      have hg:Agrees (room m B a) U V:= fun p u v=>h p (room_in he u) (room_in he v)
      have hi:well a U 1↔well a V 1:=⟨well_local hg, well_local (fun p u v=> (hg p u v).symm)⟩
      have hy:Y a (X U)=Y a (X V):= Z a _ _ ((ht a).1 U V hg)
      by_cases hk:well a U 1
      · rw [if_pos hk,if_pos (hi.mp hk)]; exact h _ y z
      rw [if_neg hk,if_neg (mt hi.mpr hk),hy]
    · intro U h p y z; change F p U=_; unfold F; split
      next g =>
        rw [if_pos ?_]; obtain ⟨v,t⟩:=h; exact ⟨v,fun i u=> t _ (plug_le (Yx p g b ⟨y,z⟩) u)⟩
      exact (ht b).2.1 _ h p y z
    · intro U h; by_cases e:degree m b<n
      · obtain ⟨v,g⟩:=(ht b).2.2 U e
        refine ⟨v,room_bed_le g (le_max_left ..) (fun p y z=>?_) (fun _ _=>rfl)⟩
        change _=F p U; unfold F; apply Eq.symm; rw [dif_neg]; intro hz
        have hu:=Finset.card_le_card (fits_os (Yx p hz b ⟨y,z⟩)); change degree m hz.choose≤degree m b at hu; rw [hz.choose_spec.1] at hu; omega
      have he:degree m b=n:=by omega
      have hy {c:Index m}(w: Lesser c b) :degree m c<n:=(fits_degree w.1 w.2).trans_eq he
      have hl (p:Edge (Site (Domain m B)))(h:Plug b p)(g:Top n p):g.choose=b:=by
        by_contra t; have hd:=fits_degree (Yx p g b h) t; rw [he,g.choose_spec.1] at hd; omega
      by_cases g:well b U 1
      · refine well_local (U:=U) (K:=K') (W:=W U) (a:=b) (fun p y z=>?_) ?_
        · change _=F p U; unfold F; split
          next u => rw [hl p ⟨y,z⟩ u,if_pos g]
          exact ((ht b).2.1 _ g p y z).symm
        obtain ⟨v,H⟩:=g; exact ⟨v,room_bed_le H (t.trans (le_max_left ..)) (fun _ _ _=>rfl) (fun _ _=>rfl)⟩
      let f:=Y b (X U)
      refine ⟨f,fun p y=>?_⟩
      by_cases z: Top n p
      · change GDist (f _* F p U) _ ≤ _
        unfold F; rw [dif_pos z,hl _ y z,if_neg g,show f p.1 * _=f (p.1+step p.2) by unfold f; group, GDist,dist_self]; apply div_nonneg _ (by positivity); exact le_trans (zero_le_one.trans t) (le_max_left ..)
      have H' : ∃ v,Facebed b L (X U) v:=by
        obtain ⟨v,T⟩:= H m B ((le_max_right ..).trans hG) hm b _ (fun i w=> (ht i).2.2 U (hy w))
        exact ⟨v,fun i h=> T i h (lt_of_le_of_lt (degree_le ..) (by norm_num))⟩
      have hq:=l b _ H'
      by_contra! hz
      apply z
      refine ⟨b,he,y,fun i w u=>?_⟩
      apply hz.not_ge
      rw [show W U p=X U p from dif_neg z]
      exact (hq i w p u).trans (div_le_div_of_nonneg_right (le_max_right ..) (by positivity))
def marked (X: Au m B→Au m B)(K:ℝ):Prop:= Measurable X∧ ∀ b:Index m,
  (∀ U V:Au m B, Agrees (room m B b) U V→ Agrees (room m B b) (X U) (X V))∧
  (∀ U:Au m B, well b U 1→Agrees (room m B b) (X U) U) ∧ ∀ U:Au m B, well b (X U) K
lemma yieldX : ∃ N:ℕ,∃ K:ℝ, 0<K∧∀ m B:Side,N≤B.val→ 2≤m.val→∃ X:Au m B→Au m B,marked X K:=by
  obtain ⟨N,K,H,h⟩:=stucco 5
  refine ⟨N,K,lt_of_lt_of_le zero_lt_one H,fun m B p u=>?_⟩
  obtain ⟨X,k,r⟩:=h m B p u; exact ⟨X,k,fun b=>⟨(r b).1,(r b).2.1,fun U=>(r b).2.2 U (lt_of_le_of_lt (degree_le ..) (by norm_num))⟩⟩
end YM.CF.Mesa
