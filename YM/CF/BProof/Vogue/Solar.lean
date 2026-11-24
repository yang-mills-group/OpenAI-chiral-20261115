import YM.CF.BProof.Vogue.Carte
/-! Roof arrives. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Vogue
open Function Filter MeasureTheory ProbabilityTheory Skye Spire Lattice Wilson Mesh Shore Finset LocalH Cube SU
open scoped Topology BigOperators NNReal ENNReal Classical Matrix.Norms.Frobenius
variable {K:Type} [Fintype K][Nonempty K]{n:Side}{d u:ℝ}{k r L:ℕ}(P:Spice n K d u k L)(p:k≤ r)
private lemma mine_b(v:k≤r){X:Pane n→ Pane n}(h:Basic n X u d k): Basic n X u d r:=⟨h.legal,h.meas,fun U i t=>h.covers _ _ (t.mono_right (Corona.halo_mono v (Subset.refl _))),fun U V i t=>h.shore U V i (agrees_mono t (Corona.halo_mono v (Subset.refl _)))⟩
include p
-- adapted from lightLegal
lemma burn_p(x:Orbit n):RG.flags d (burn P r x)=∅:=by
 apply Skye.broad; intro i; let M:=RG.flags u x.1; let A:= RG.touched i; let B:= burn P r x
 obtain ⟨Q,hQ⟩: ∃ Q:Pane n, RG.flags d Q=∅∧ Agrees A B Q:=by
    by_cases g:∃ e:reach n,ends e⊆ A ∧ Bubb M r e; swap
    · let a:= Classical.arbitrary K; let v:=mine_b p (P.ok a); refine ⟨P.P a x.1,v.legal _,fun i m k=>?_⟩; have hv:¬Bubb M r i:= fun h=> g ⟨_,insert_subset_iff.mpr ⟨m,singleton_subset_iff.mpr k⟩,h⟩; change (if Bubb M r i then _ else _)=_; rw [if_neg hv]; exact (v.covers _ i (not_not.mp (fun h=> hv (pieV .. |>.mpr h)))).symm
    obtain ⟨e,t,v⟩:=g; let S:=soup M r e; let Y:=timb S x.2; let a:= brush K x.2 S; let hg:=mine (mine_b p (P.ok a)) Y; refine ⟨mend (P.P a) Y x.1, hg.legal _,fun b j f=>?_⟩; let hp:ends b⊆ A:=insert_subset_iff.mpr ⟨j,singleton_subset_iff.mpr f⟩; have hz(w:Seat n)(d:w∈A)(y:Seat n)(u:y∈ A): separation w y ≤20:=by have ht:= Work.E01.sep_touched i w d; have hp:=Work.E01.sep_touched i y u; rw [separation_comm i.1 w] at ht; have h:=separation_triangle w i.1 y; omega
    change (if Bubb M r b then mend (P.P (brush K x.2 _)) (timb (soup M r b) x.2) _ b else _)=_; split
    · rename_i h; have he:soup M r b=S:= Finset.Subset.antisymm (dives v (fun _ i _ j=> hz _ (hp i) _ (t j))) (dives h (fun _ i _ j=> hz _ (t i) _ (hp j))); rw [he] -- defeq a hp issue
    next h=> exact (hg.covers _ b (not_not.mp fun g=>h (pieV ..|>.mpr g))).symm
 by_contra! hv; have hm:i.1∈ RG.flags d Q:= (RG.flags_spec d Q i.1).mpr ⟨i, Work.E01.base_touched _, (show faceValue B i=faceValue Q i from travel_local _ _ _ _ (fun e p q=> hQ.2 e (List.mem_toFinset.mpr p) (List.mem_toFinset.mpr q))) ▸ hv⟩
 rw [hQ.1] at hm; exact notMem_empty _ hm

lemma warmL (X S:Support (More n))(V W:Pane n)(t q:Ids n)(f:X ∩ RG.flags u V=X ∩ RG.flags u W)(g:Week X S (RG.flags u V) r)(u':Week X S (RG.flags u W) r)(a:Agrees X V W)(e:Set.EqOn t q X): Agrees S (conic P r (V,t)) (conic P r (W,q)):=by
 intro i vi wi; let A:= Lattice.gauge (frameP t) V; let B:= gauge (frameP q) W; let D:= RG.flags u V; let J:= RG.flags u W; have hx: Agrees X A B:=tied _ _ _ _ _ a (fun i v=> by simp only [frameP,e v]); have ht:ends i⊆ S:= insert_subset_iff.mpr ⟨vi,singleton_subset_iff.mpr wi⟩; have hp:ends i⊆ X:=Finset.Subset.trans (halo_subset r _) (g.all i ht)
 have hz:soup D r i=soup J r i:= suppC _ _ _ _ _ (by unfold D J; rw [inter_comm,inter_comm J]; exact f) (g.all _ ht) (g.mask _ ht) (u'.mask _ ht)
 have he: burn P r (A,t) i=burn P r (B,q) i:=by
    have he : RG.flags u A = D:= RG.gauge_flags ..; have hv:RG.flags u B=J:=RG.gauge_flags ..; unfold burn Bubb; dsimp only; rw [he,hv,hz]; by_cases H:(soup J r i).Nonempty; swap; · rw [if_neg H,if_neg H]; exact hx i (hp (by simp)) (hp (by simp)) -- both occurrences rw?
    have ht'(x)(v:x∈soup J r i):x∈X:= u'.mask i ht _ v (halo_subset _ _ (mem_singleton_self x)); have hm:Set.EqOn (priorP t) (priorP q) (soup J r i):=fun i v=>congrArg Prod.fst (e (ht' i v)); rw [if_pos H,if_pos H]; unfold timb; rw [mastL _ _ _ hm, e (ht' _ (mastP _ H _).1),show brush K t _=brush K q (soup J r i) from ?_, (mine (mine_b p (P.ok _)) _).shore A B i (agrees_mono hx (g.all _ ht))]; -- may need if_pos
    unfold brush Taste; congr 1; refine sum_congr rfl fun i k=>congrArg _ (hm k)
 unfold conic Lattice.gauge; simp only [show ∀ i,(frameP t)⁻¹ i=(t i).2.2⁻¹ from fun _=>rfl,show ∀ i,(frameP q)⁻¹ i=(q i).2.2⁻¹ from fun _=>rfl]; rw [e (show (i.1)∈↑X from hp (by simp)),e (show i.1+step i.2∈↑X from hp (by simp))]; exact congrArg (fun v=>_*v*_) he
theorem covers_toit (d1:ℝ)(h:∀ (V:Pane n), RG.flags d V=∅→ Guard V d1): Roof n u d1 r (conic P r):= ⟨fun x=>h _ (by rw [conic,RG.gauge_flags]; exact burn_p P p _),conicM ..,conic_g P r,fun _ _ s=>loom_spin P r s _ _,noop P r,fun V W t q X S f=>warmL P p X S V W t q f⟩
end YM.CF.BProof.Vogue
