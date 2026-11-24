import YM.SU5.Reconstruction.Sleet.NacreTag
/-! # Real ray compatibility. Uniform off-axis account -/
set_option autoImplicit false
noncomputable section
namespace YM.ConePrice.Storm
open Function Set Filter MeasureTheory Complex Sail Metric
open scoped Topology NNReal Real Classical
variable {X:Type*}{μ:X→ℝ}
structure Motion (μ:X→ℝ): Prop where
 pos(x:X):0<μ x
 rich (x:ℝ)(p:0<x):∃ u:ℕ→X,Tendsto (fun n=> μ (u n)) atTop (𝓝 x)
variable (p:Motion μ)
include p
lemma rich_glue {F G:ℂ→ℂ}(h: AnalyticOnNhd ℂ F optimistic)(u:AnalyticOnNhd ℂ G optimistic)(o:∀ i:X,F (μ i)=G (μ i)):
    EqOn F G optimistic:= by
 refine pioneer current_conn (assigned_ground (v:=1) (by norm_num)) 0 2 (by norm_num) h u ?_
 intro x ⟨h₀,hx⟩
 obtain ⟨q,b⟩:=p.rich x h₀
 let r(n:ℕ):= ((μ (q n)):ℂ)
 have hr:Tendsto r atTop (𝓝 (x:ℂ)):= (continuous_ofReal.tendsto x).comp b
 apply tendsto_nhds_unique (f:=F∘r) ((h _ (assigned_ground h₀)).continuousAt.tendsto.comp hr)
 exact ((u _ (assigned_ground h₀)).continuousAt.tendsto.comp hr).congr (fun n=> (o (q n)).symm)
local instance: leadStream.NeBot:= by unfold leadStream; infer_instance
variable {C:ℝ}
omit p in
lemma flock (V:ℕ→ℂ→ℂ)(h:∀ i,Kite C (V i)):∃ f:ℂ→ℂ,Kite C f ∧ ∀ z∈optimistic, Tendsto (fun i=> V i z) leadStream (𝓝 (f z)):=by
 obtain ⟨F,H,w⟩:=limit_chance V current_open (fun n=>(h n).1.differentiableOn) (fun n=>(h n).2)
 exact ⟨F,⟨H,fun z Z=>le_of_tendsto (w z Z).norm (Eventually.of_forall fun i=>(h i).2 z Z)⟩,w⟩
lemma steep {L:Set ℝ}{U:ℝ→ℂ→ℂ}(h:∀ x∈ L,Kite C (U x))
   (r:∀ y:X,ContinuousOn (fun x=>U x (μ y)) L)(z:ℂ)(e:z∈optimistic):ContinuousOn (fun x=> U x z) L:=by
 intro x t; apply tendsto_iff_seq_tendsto.mpr; intro v a
 intro T g
 by_contra ht
 obtain ⟨q,b,d⟩:= extraction_of_frequently_atTop (show ∃ᶠ n in atTop, v n∈L∧ U (v n) z∉ T from ((show ∃ᶠ n in atTop, U (v n) z∉ T from not_eventually.mp ht).and_eventually (tendsto_nhdsWithin_iff.1 a).2).mono (fun i h=>h.symm)) -- And.symm?
 obtain ⟨f,k,j⟩:= flock (fun n=> U (v (q n))) (fun i=> h _ (d i).1)
 have he: f z= U x z:= rich_glue p k.1 (h x t).1 (fun i=> tendsto_nhds_unique (j _ (assigned_ground (p.pos i))) (((Tendsto.comp (r i x t) a).comp b.tendsto_atTop).mono_left (Ultrafilter.of_le atTop))) e
 have hf:= j z e; rw [he] at hf; obtain ⟨i,u⟩:= (hf.eventually g).exists; exact (d i).2 u

variable {V W:X→ℂ→ℂ}
/-- Horizontally extend V. Need W for opposing clock on readings. -/
lemma eastward (h:∀ i,Kite C (V i))(u:∀ i,Kite C (W i))(v:∀ i j,V i (μ j)=W j (μ i)):
    ∃ f:ℝ→ℂ→ℂ,(∀ x∈ Ioi 0,Kite C (f x)) ∧ (∀ x∈Ioi 0,∀ i:X,f x (μ i)=W i x) ∧ ∀ z∈optimistic,ContinuousOn (fun x=> f x z) (Ioi 0):=by
 have hp (x:ℝ):∃ f:ℂ→ℂ,0<x→ Kite C f ∧ ∀ i:X,f (μ i)=W i x:=by
    by_cases e: 0<x; swap; · exact ⟨0,fun h=>(e h).elim⟩
    obtain ⟨g,G⟩:=p.rich x e
    obtain ⟨f,k,y⟩:= flock (V∘g) (fun n=> h _); refine ⟨f,fun _=>⟨k,fun i=>?_⟩⟩
    have hw:= y _ (assigned_ground (p.pos i))
    have ht:Tendsto (fun l=> (↑(μ (g l)):ℂ)) leadStream (𝓝 (x:ℂ)):= (Complex.continuous_ofReal.tendsto _).comp (G.mono_left (Ultrafilter.of_le atTop))
    exact tendsto_nhds_unique hw ((((u i).1 _ (assigned_ground e)).continuousAt.tendsto.comp ht).congr (fun n=> (v (g n) i).symm))
 choose f hf using hp
 refine ⟨f,fun x u=> (hf x u).1,fun x u=> (hf x u).2,steep p (fun x u=> (hf x u).1) ?_⟩
 intro y; apply (((u y).1.continuousOn.comp Complex.continuous_ofReal.continuousOn (fun x h=> assigned_ground h))).congr
 intro x t; exact (hf x t).2 _

lemma airfield (h:∀ i,Kite C (V i))(u:∀ i,Kite C (W i))(v:∀ i j,V i (μ j)=W j (μ i)):
    ∃ (f:ℝ→ℂ→ℂ) (g:ℂ→ℝ→ℂ), Squall C f g ∧ (∀ z∈optimistic,∀ i:X,f (μ i) z=V i z∧g z (μ i)= W i z):=by
 obtain ⟨f,F,a,k⟩:= eastward p h u v; obtain ⟨G,M,l,n⟩:= eastward p u h (fun i j=>(v j i).symm)
 have hu(z:ℂ)(Z:z∈optimistic)(i:X): f (μ i) z=V i z∧ G (μ i) z=W i z:= by
    have he:=p.pos i
    exact ⟨rich_glue p (F _ he).1 (h i).1 (fun j=> (a (μ i) he j).trans (v i j).symm) Z,rich_glue p (M _ he).1 (u i).1 (fun j=> (l (μ i) he j).trans (v j i)) Z⟩
 refine ⟨f,(fun x y=>G y x), ⟨fun x e=>(F x e).1, fun x e=> (M x e).1,fun x e=>(F x e).2,fun x e=>(M x e).2,?_,k⟩,hu⟩
 intro x y H E; obtain ⟨b,t⟩:=p.rich y E
 have ht:Tendsto (fun n=> μ (b n)) atTop (𝓝[Ioi 0] y):=tendsto_nhdsWithin_iff.2 ⟨t,Eventually.of_forall (fun i=>p.pos (b i))⟩
 exact tendsto_nhds_unique (((F _ H).1 _ (assigned_ground E)).continuousAt.tendsto.comp ((continuous_ofReal.tendsto y).comp t)) ((Tendsto.comp (n _ (assigned_ground H) y E) ht).congr (fun j=> ( (a x H (b j)).trans (hu x (assigned_ground H) (b j)).2.symm).symm))

lemma preordained(R:X→X→ℂ)(h:∀ x,Voucher μ (R x) C)(u:∀ y,Voucher μ (fun x=>R x y) C):∃ (f:ℝ→ℂ→ℂ) (g:ℂ→ℝ→ℂ),Squall C f g∧∀ x y:X, f (μ x) (μ y)=R x y∧g (μ x) (μ y)=R x y:=by
 choose V Hv Hp using fun x=> Voucher.wear μ _ C (h x) p.pos
 choose W Hq Ht using fun y=> Voucher.wear μ _ C (u y) p.pos
 obtain ⟨f,G,F,t⟩:= airfield p Hv Hq (fun x y=>(Hp x y).trans (Ht y x).symm); refine ⟨f,G,F,fun x y=>?_⟩
 exact ⟨((t _ (assigned_ground (p.pos y)) x).1).trans (Hp x y), ((t _ (assigned_ground (p.pos x)) y).2).trans (Ht y x)⟩
end YM.ConePrice.Storm
