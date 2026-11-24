import YM.CF.Vp929.Borel.Film
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.VolumeCape.Borel
open Filter Function Finset MeasureTheory ProbabilityTheory
open Mesh Lattice Atlas Skye Cane Spire Scroll SU Cube Lat Aerial Sample Gather
open scoped Classical Topology ENNReal NNReal Matrix.Norms.Frobenius
private lemma weave{X Y J D G:Type}[MeasurableSpace X][MeasurableSpace Y][MeasurableSpace J][MeasurableSpace D][MeasurableSpace G](μ:Measure X)(ν:Measure Y)(p:Measure J){f:X→G}{g:J→G}(x:X→Y)(X₁:Y→D)(X₂:J→D)(F:D→G)(t:MeasurePreserving x μ ν)(h:ν.map X₁=p.map X₂)(u:Measurable X₁)(v:Measurable X₂)(q:Measurable F)(w:∀ i,f i= F (X₁ (x i)))(W:∀i,g i=F (X₂ i)) : μ.map f=p.map g:=by rw [show f= F∘(X₁∘x) from funext w,show g= F∘ X₂ from funext W,←Measure.map_map q (u.comp t.1), ←Measure.map_map u t.1, t.2,h,Measure.map_map q v]
namespace Scoop
variable (n:Side)(r:ℕ)(M:Finset (Seat n))
local notation "S_"=>Stain n r M
variable {I:Type} [Nonempty I][Fintype I][MeasurableSpace I][MeasurableSingletonClass I][StandardBorelSpace I]
variable (p:Ticket I)(R:Sweep n→Equiv.Perm I)
variable (v:∀s,MeasurePreserving (R s) p.Law p.Law)
variable {A:Type} [Fintype A][MeasurableSpace A][MeasurableSingletonClass A]
variable (f k:ℕ) (T:Budget r f k) (F:I→Seat n→A)
variable (h:∀ S V,stone (More n) S V k→ Ticket.Indep p (Vision S F) (Vision V F))
variable (u d:ℝ)(Q:I→Pane n→Pane n)
variable (a:∀i,Basic n (Q i) u d f)
variable (t:∀ s i,mend (Q i) s=Q (R s i))
variable (g:∀i j,∀ e:reach n,(∀ x∈ Read.glow _ e f,F i x= F j x)→∀ V:Pane n,Q i V e= Q j V e)

private def piece (w:S_→I)(V:Pane n):Pane n:= fun e=> if p:(soup M r e).Nonempty then Q (w (plotTag n r M e p)) V e else V e
private lemma budget_safe(B k:ℕ)(T:Budget r B k): B≤r:= by unfold Budget at T; omega
private theorem win_le (b:ℕ)(u:b≤r)(e:reach n): win b e⊆ win r e:=fun i k=>by obtain ⟨x,h,v⟩:=halo_spec.mp k; exact halo_spec.mpr ⟨x,h,v.trans u⟩
include a T g
private lemma sherbet(V:Pane n)(q:M=RG.flags u V)(x y:S_→I)(p:∀i:S_,deck n r M f F i (x i)= deck n r M f F i (y i)): piece n r M Q x V=piece n r M Q y V:=by
 funext i; unfold piece; split_ifs with h; swap; · rfl
 let c:=plotTag n r M i h; by_cases v: Disjoint M (win f i); · rw [(a (x c)).covers _ i (q ▸ v),(a (y c)).covers _ i (q ▸ v)]
 exact g _ _ i (fun i' w=> congrFun (p c) ⟨i', moats n r M i f (budget_safe r _ _ T) h v w⟩) V
omit g
private lemma onepiece (V:Pane n)(q:M=RG.flags u V)(x:I): piece n r M Q (fun _=> x) V= Q x V:=by
 funext i; unfold piece; split; · rfl
 rename_i h; have e: Disjoint M (win r i) := not_not.mp fun v=>h ((pieV ..).mpr v); rw [(a x).covers _ i (q ▸ e.mono_right (win_le n r _ (budget_safe r _ _ T) _))]
omit a T
include t
local notation "Ω"=> Wave n
private lemma scene(V:Pane n)(w:Ω)(D:Frame n): Braid.join n r Q (samp n p) M (merge n (D,w)) V=piece n r M Q (decode n r M p R w) V:=by
 funext i; unfold Braid.join piece; by_cases h:(soup M r i).Nonempty; · let S:=soup M r i; let v:= behold n S w; rw [if_pos h,dif_pos h]; change mend (Q (samp n p S v.1)) v.2 V i = Q (R v.2 (samp n p S v.1)) V i; rw [t]
 rw [if_neg h,dif_neg h]
-- distribution conditioned on fixed frame and field
include a T t v h g
private lemma bowl(V:Pane n)(q:M=RG.flags u V)(D:Frame n): (valsw n).map (fun w=> Braid.join n r Q (samp n p) M (merge n (D,w)) V)= p.Law.map (fun x=> Q x V) := by
 let P:=fun (z:S_→I)=> piece n r M Q z V
 let H:=fun (z:S_→I) (i:S_)=> deck n r M f F i (z i)
 let J : Set (∀ i:S_,((moat n r M i f)→ A)):= Set.range H
 let K(x:∀ i:S_,((moat n r M i f)→ A)) : Pane n:= if p:x∈ J then P (Exists.choose p) else 1
 have hk(z:S_→I):K (H z)=P z:=by unfold K; rw [dif_pos (show H z∈J from Set.mem_range_self z)]; let e:= (show H z∈J from Set.mem_range_self z); exact sherbet n r M f k T F u d Q a g V q _ _ (congrFun e.choose_spec)
 have hv(x:I): K (Plot n r M f F x)= Q x V:= (hk (fun _=>x)).trans (onepiece _ r M f k T u d Q a V q x)
 have hu:Measurable H:=measurable_of_countable H; have hb:= measurable_of_countable K; have he:Measurable (fun z:S_→ I=> P z):= measurable_of_countable P
 refine weave (valsw n) (Measure.pi (fun _:Stain n r M=>p.Law)) p.Law (Gather.decode n r M p R) H (Plot n r M f F) K (decode_law n r M p R v) (price_tape n r M p f k T F h).symm hu (measurable_of_countable _) hb ?_ (fun i=> (hv i).symm)
 intro i; exact (scene n r M p R Q t V i D).trans (hk _).symm

lemma join_law (V:Pane n)(D:Frame n): (valsw n).map (fun w=> Braid.story n r u Q (samp n p) V (merge n (D,w)))=p.Law.map (fun x=> Q x V):= bowl n r _ p R v f k T F h u d Q a t g V rfl D
end Scoop
end YM.CF.VolumeCape.Borel
