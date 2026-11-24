import YM.CF.Mesa.Ties

/-! Extend a choice of frames around all flags of the boundary. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mesa
open Function Set Filter Metric Lattice CF.Cube Lat
open scoped Topology NNReal BigOperators InnerProductSpace Matrix.Norms.Frobenius
variable {m B:Side} {a b c:Index m} {K L:ℝ} {F W U : Bkg (Domain m B)}
abbrev Plug (a:Index m)(p:Edge (Site (Domain m B))):Prop:=p.1∈room m B a ∧ p.1+step p.2∈room m B a
abbrev Bed (a:Index m)(K:ℝ)(U:Bkg (Domain m B))(u:Fa m B):=∀(p:Edge _), Plug a p → GDist (u p.1 * U p) (u (p.1+step p.2)) ≤ K/B.val
lemma plug_le (h:Fits m b a){p: Edge (Site (Domain m B))}(g:Plug b p):Plug a p:=⟨room_in h g.1,room_in h g.2⟩
lemma from_bed {u v}(h:Bed a K U u)(g:Bed a L U v): HintX a (K+L) (u*v⁻¹):=by
  intro x i hx he
  let y:=x+step i
  let w:=U (x,i)
  have ht:=h (x,i) ⟨hx,he⟩; have hk:=g (x,i) ⟨hx,he⟩
  change GDist (u x*(v x)⁻¹) (u y*(v y)⁻¹) ≤ _
  rw [show u x*(v x)⁻¹=(u x*w)*(v x*w)⁻¹ by group, add_div]
  apply (dist_triangle _ (SU.group.mat (u y*(v x*w)⁻¹)) _).trans; rw [bolt,bolt',bolt_inv]; exact add_le_add ht hk
lemma bed_join {u v}(h:HintX a K u)(g:Bed a L U v): Bed a (K+L) U (u*v):=by
  rintro ⟨x,i⟩ ⟨hx,hy⟩; let y:=x+step i; let w:=U (x,i)
  change GDist ((u x*v x)*w) (u y*v y)≤_
  rw [mul_assoc,add_div]; apply (dist_triangle _ (SU.group.mat (u y*(v x*w))) _).trans; rw [bolt,bolt']; exact add_le_add (h x i hx hy) (g (x,i) ⟨hx,hy⟩)
lemma room_bed_le {u v:Fa m B}(h:Bed a K U u)(f:K≤L)(e:Agrees (room m B a) U F)(t:∀ x∈room m B a,v x=u x):Bed a L F v:=by
  intro p hx; rw [t _ hx.1,t _ hx.2,←e p hx.1 hx.2]; exact (h _ hx).trans (div_le_div_of_nonneg_right f (by positivity))
lemma bed_budget (n:ℕ)(K:ℝ)(hK:0≤K):∃ L:ℝ,∃ N:ℕ,0≤L∧∀ m B:Side,N≤B.val→ 2≤m.val →∀ a:Index m,∀ U:Bkg (Domain m B),(∀ b, Lesser b a→∃ f:Fa m B,Bed b K U f) →∃ v:Fa m B,∀ b,Lesser b a→ degree m b<n → Bed b L U v:=by
  classical
  induction n with
  | zero => exact ⟨0,0,le_rfl,fun _ _ _ _ _ _ _ => ⟨1,fun _ _ h=>by omega⟩⟩
  | succ n ih =>
    obtain ⟨L,N,e,H⟩:=ih
    obtain ⟨R,T,t,G⟩:= extract_all (L+K) (add_nonneg e hK)
    refine ⟨max L (T+K),max N R,le_trans e (le_max_left ..),fun m B r hm a U g=>?_⟩
    obtain ⟨w,hW⟩:=H m B ((le_max_left ..).trans r) hm a U g
    let S (b:Index m):Prop:= Lesser b a∧degree m b=n
    have q (b:Index m)(h:S b) : ∃ v:Fa m B,Bed b (T+K) U v∧∀ x, Rim b x→ v x=w x :=by
      obtain ⟨f,hf⟩:=g b h.1
      have hx:=fits_degree h.1.1 h.1.2
      obtain ⟨z,t,q⟩:=G m B b (w*f⁻¹) ((le_max_right ..).trans r) hm (by have hg:=degree_le m a;omega) (fun c E=> by
        have Y:=h.2
        exact from_bed (hW c (lowt E.1 h.1) (Y ▸ fits_degree E.1 E.2)) (fun p P => hf _ (plug_le E.1 P)))
      exact ⟨z*f,bed_join t hf,fun x hx=> by rw [Pi.mul_apply,q x hx,Pi.mul_apply,Pi.inv_apply]; group⟩
    choose! p f l using q
    let v (x:Site (Domain m B)):= if h:∃ b, S b ∧ x∈room m B b then p h.choose x else w x
    have ht b (h:Lesser b a)(e:degree m b<n)(x:Site (Domain m B))(g:x∈room m B b): v x=w x:=by
      unfold v; split; rename_i H; let d:= H.choose; obtain ⟨D,Hx⟩:= H.choose_spec
      obtain ⟨c,hk,k,Hq⟩:= overlap hm g Hx
      have hy:= Finset.card_le_card (fits_os hk); change degree m c≤ degree m b at hy
      exact l d D _ ⟨c,k,(fun hz=> (hy.trans_lt e).ne (by rw [hz]; exact D.2)),Hq x g Hx⟩ -- tune
      rfl
    refine ⟨v,fun b h E =>?_⟩; by_cases Lb:degree m b<n
    · exact room_bed_le (hW b h Lb) (le_max_left ..) (fun _ _ _=>rfl) (ht b h Lb)
    have hu:S b:=⟨h,by omega⟩
    refine room_bed_le (f b hu) (le_max_right ..) (fun _ _ _=>rfl) (fun x g=>?_)
    let H:∃ i,S i∧ x∈room m B i:=⟨b,hu,g⟩; let d:=H.choose; obtain ⟨T,Y⟩:=H.choose_spec
    unfold v; rw [dif_pos H]; by_cases e:d=b
    · change p d x=_; rw [e]
    obtain ⟨c,hc,i,C⟩:= overlap hm g Y
    have hb:c≠b:= fun hz=>by
      rw [hz] at i; have hh:=fits_degree i (Ne.symm e); rw [hu.2,T.2] at hh; omega
    have hh:c≠d:= fun hz=>by
      change Fits m _ d at i; rw [hz] at hc; have hh:=fits_degree hc e; rw [hu.2, show degree m d=n from T.2] at hh; omega
    rw [l _ T x ⟨_,i,hh,C x g Y⟩,l _ hu x ⟨_,hc,hb,C x g Y⟩]
end YM.CF.Mesa
