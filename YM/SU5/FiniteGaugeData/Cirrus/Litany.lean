import YM.SU5.FiniteGaugeData.Cirrus.Trope
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Maison
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℂ E][CompleteSpace E](F: H.space→L[ℂ]E)(x:Bench S)(Ω:Bench S)(hΩ:∀ p:E4,M S p Ω.val=Ω.val)
variable {ι:Type}(G:Canopy H ι)(t:G.Token)(w:List G.Token)
local notation "D"=> Bench S
local notation "Mₜ"=>G.horizon S
local notation "P"=>usher S
local notation "C"=> Rite S Ω G
local notation "W"=> Hut S Ω G
local notation "R"=> saucer S
-- support
variable (U:Set E4)(f:Test4)
abbrev LetterQ (U:Set E4)(f:Test4):Prop:= HasCompactSupport (f:E4→ℂ)∧tsupport f ⊆ U
abbrev CloseParty (U:Set E4)(w:List G.Token):Prop:= ∀ t∈ w,LetterQ U t.2
abbrev LocalCab (U:Set E4): Set D:= {x|∃ w, CloseParty G U w ∧ x=G.bud S Ω w}
abbrev SampleInR (U:Set E4): Set H.space:= Subtype.val '' LocalCab S Ω G U
local notation "λₜ"=>LocalCab S Ω G U
local notation "Lₐ"=> SampleInR S Ω G U
variable (p:E4)
lemma support_F : tsupport (ahead p f) ⊆ (fun z:E4=> z+p) '' tsupport f:= fun z h=> ⟨z-p, route p f h,sub_add_cancel ..⟩
lemma support_G (c:HasCompactSupport (f:E4→ℂ)) : HasCompactSupport (ahead p f : E4→ ℂ) := (c.image (show Continuous (fun q:E4=> q+p) from continuous_id.add continuous_const)).of_isClosed_subset (isClosed_tsupport _) (support_F f p)
variable (u:IsOpen U)
include u
lemma lockFit (h:LetterQ U f): ∀ᶠ p:E4 in 𝓝 0,LetterQ U (ahead p f) := by
 let D': Set (E4 × E4):= {x| x.2+x.1∈ U}
 have he: {(0:E4)} ×ˢ tsupport f ⊆ D' := fun ⟨x,y⟩ ⟨p,q⟩=> show y+x∈U from by have he:x=0:=p; rw [he,add_zero]; exact h.2 q
 obtain ⟨A,B,r,s,H,k,v⟩:= generalized_tube_lemma (isCompact_singleton (x:=(0:E4))) h.1 (u.preimage (continuous_snd.add continuous_fst)) (show _ ×ˢ _ ⊆ (fun p=>_) ⁻¹' U from he)
 filter_upwards [r.mem_nhds (H (mem_singleton _))] with p hp; refine ⟨support_G _ p h.1, fun z hz=> ?_⟩; obtain ⟨z,e,rfl⟩:=support_F f p hz; exact v (show (p,z)∈ A ×ˢ B from ⟨hp,k e⟩)
lemma entourage(h:CloseParty G U w): ∀ᶠ p:E4 in 𝓝 0,CloseParty G U (w.map (farther G p)):=by
 classical
 have he:= (eventually_all_finset (l:=𝓝 (0:E4)) (I:=w.toFinset) (p:=fun (t:G.Token) p=> LetterQ U (farther G p t).2)).mpr (fun t e=> lockFit U t.2 u (h t (List.mem_toFinset.mp e))); filter_upwards [he] with p hp; intro t q; obtain ⟨t,hb,rfl⟩:= List.mem_map.mp q; exact hp _ (List.mem_toFinset.mpr hb)
include hΩ
lemma parties (h:CloseParty G U w): Hut S Ω G w (LocalCab S Ω G U) := by
 suffices Z: ∀ (n:ℕ) (w:List G.Token),CloseParty G U w→ w.length≤n → Hut S Ω G w (LocalCab S Ω G U) from Z w.length w h le_rfl
 intro n
 induction n with
 | zero=> intro w e z; rw [show w=[] from List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero z)]; change Ω∈ λₜ; exact ⟨[],by simp [CloseParty],rfl⟩
 | succ n ih=>
   intro w h k
   cases w with
   | nil=> change Ω∈ λₜ; exact ⟨[],by simp [CloseParty],rfl⟩
   | cons t w=>
      rw [Hut]; filter_upwards [entourage G (t::w) U u h] with p z; let r:=farther G p; refine higher S Ω G w _ _ ?_ (holt S Ω hΩ G w p (λₜ) (ih (w.map r) (fun i h=> z _ (List.mem_cons_of_mem _ h)) (by simpa using k)))
      rintro y ⟨V,hv,q⟩; change P p (G.horizon S t y)∈ λₜ; refine ⟨r t:: V,fun j v=> (List.mem_cons.mp v).elim (fun w=>w ▸ z (r t) List.mem_cons_self) (hv _), ?_⟩; exact (show P p (G.horizon S t y)=G.horizon S (r t) (P p y) from attends S _ _ _ _ _).trans (congrArg (G.horizon S (r t)) q)
variable (X:Boundary.Action H)(e:∀ p:E4,X.orbit.translation p=M S p)
include e
local notation "￥"=> G.Ticket S Ω
variable (hF:∀ x∈ SampleInR S Ω G U, F x=0)
include hF
lemma kinfolk (h:CloseParty G U w) (y:Bench S)(p:y∈ Rite S Ω G w) : F y.val=0:=by
 rw [← home S]; refine tang S F Ω G w X e 0 (higher S Ω G w _ _ ?_ (parties S Ω hΩ G w U u h)) p; intro x v; change F (hall S 0 _)=0; rw [home]; exact hF _ ⟨x,v,rfl⟩
-- dice near translations
abbrev OrbitBox (U:Set E4)(f:Test4):Prop:=∃ (p:E4)(g:Test4),LetterQ U g ∧ ahead p g=f
lemma folk_B (h:∀ t∈w, OrbitBox U t.2) : F (￥ w)=0:= by
 suffices e: ∃ v,CloseParty G U v ∧ G.bud S Ω w∈ C v by obtain ⟨v,r,t⟩:= e; exact kinfolk S F Ω hΩ G v U u X (by assumption) hF r _ t
 clear e hF; induction w with
 | nil=> exact ⟨[],by simp [CloseParty],rfl⟩
 | cons t w ih=>
    obtain ⟨v,r,l⟩:= ih (fun i e=> h _ (List.mem_cons_of_mem _ e))
    obtain ⟨p,g,Gb,k⟩:= h t List.mem_cons_self; let A:G.Token := (t.1,g); have he:farther G p A=t:= Prod.ext rfl k; refine ⟨A::v,fun i v=> (List.mem_cons.mp v).elim (fun q=>q ▸ Gb) (r _),?_⟩; rw [Canopy.planeV]; have hm:= arrives S Ω hΩ G A v p _ l; rw [he] at hm; exact hm
#print axioms folk_B
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Maison
