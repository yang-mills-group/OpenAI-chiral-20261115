import YM.SU5.FiniteGaugeData.Cirrus.Ariane
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)
variable (x:Bench S)(Ω:Bench S)(hΩ:∀ p:E4,M S p Ω.val=Ω.val)
variable {ι:Type}(G:Canopy H ι)(J K:Set ι)(t:G.Chip)(w v:List G.Token)
local notation "D"=> Bench S
local notation "M'"=> G.Model S Ω
local notation "Ω₁"=> G.focus S Ω []
local notation "£"=>G.horizon S
local notation "¥"=> G.Ticket S Ω
-- full completion belongs to each actor already with Life.
open Submodule
variable (X:Boundary.Action H)(e:∀ p:E4,X.orbit.translation p=M S p)
variable (U V:Set E4)(u:IsOpen U)(v':IsOpen V)(d:U.Nonempty)(d':V.Nonempty)
include hΩ u d
lemma census (p:G.Arrival S Ω X) : (Maison.LocalSeed S Ω G U).topologicalClosure=⊤:=by
 rw [breeds S Ω hΩ G U u d X p.time]; let L:= G.lens S Ω; let Z:= G.Strand S Ω; have h:LinearMap.range L= Z:=by unfold L Canopy.lens; rw [LinearMap.range_comp,range_subtype]; rfl
 refine eq_top_iff.mpr (fun x _=> ?_); change x∈ Z.topologicalClosure; rw [← h]; exact p.dense x
-- sectors
omit hΩ u d
def tower (J:Set ι): Canopy H J where
 P x:= G.P x.val
 flash x:= G.flash x.val
 duplex x:= G.duplex x.val
abbrev riseChip (t:(tower G J).Chip): G.Chip:= ⟨t.1.val,t.2⟩
abbrev riseTok (t:(tower G J).Token): G.Token:= (riseChip G J t.1,t.2)
abbrev mDown(t:G.Chip)(p:t.fst∈J): (tower G J).Chip:=⟨⟨t.fst,p⟩,t.snd⟩
def enrolled : Prop:= ∀ t∈ w,t.1.1∈ J
lemma preaching (w:List (tower G J).Token): enrolled G J (w.map (riseTok G J)):=by intro t v; obtain ⟨t,h,rfl⟩:= List.mem_map.mp v; exact t.fst.fst.property
lemma purchase (h:enrolled G J w) : ∃ V: List (tower G J).Token,w=V.map (riseTok G J):=by
 induction w with
 | nil=> exact ⟨[],rfl⟩
 | cons t w ih=>
    obtain ⟨v,r⟩:= ih (fun s w=>h s (List.mem_cons_of_mem _ w)); exact ⟨(mDown G J t.1 (h t List.mem_cons_self),t.2)::v,congrArg (t::·) r⟩
lemma rises (w: List (tower G J).Token): (tower G J).bud S Ω w= G.bud S Ω (w.map (riseTok G J)):=by induction w with
 | nil=> rfl
 | cons t w ih=> exact congrArg ((tower G J).horizon S t) ih
lemma partying (w:List (tower G J).Token) : CloseParty (tower G J) U w ↔ CloseParty G U (w.map (riseTok G J)):=by
 constructor
 · intro h t p; obtain ⟨t,q,rfl⟩:= List.mem_map.mp p; exact h t q
 intro h t p; exact h (riseTok G J t) (List.mem_map_of_mem p)
local notation "L₁"=> tower G
abbrev Height (J:Set ι):= (tower G J).Climb S Ω
abbrev Rings (U:Set E4)(w:List G.Token):Prop:= CloseParty G U w ∧ enrolled G J w
def CensusR := span ℂ (G.Ticket S Ω '' {w| Rings G J U w})
lemma homeField : CensusR S Ω G J U= LocalSeed S Ω (tower G J) U:=by
 apply congrArg (span ℂ); ext x; constructor
 · rintro ⟨w,⟨p,e⟩,rfl⟩; obtain ⟨w,rfl⟩:= purchase G J w e; exact ⟨(tower G J).bud S Ω w,⟨w,(partying G J U w).2 p,rfl⟩,congrArg Subtype.val (rises S Ω G J w)⟩
 rintro ⟨y,⟨w,P,rfl⟩,rfl⟩; exact ⟨w.map (riseTok G J),⟨(partying G J U w).1 P,preaching G J w⟩, congrArg Subtype.val (rises S Ω G J w).symm ⟩
include e hΩ u d
lemma plot_reach : (CensusR S Ω G J U).topologicalClosure= Height S Ω G J:= by rw [homeField]; exact breeds S Ω hΩ (tower G J) U u d X e
omit e hΩ u d
-- Connected correlations. Note FACTOR intrinsically means relative to selected observable
-- multiplets (eventually to be tied to W geometry & chiral field stencils).
def linked (Ω x y:H.space):ℂ:= inner ℂ x y-inner ℂ x Ω * inner ℂ Ω y
abbrev LocSplit (U V:Set E4):Prop:=∀ w v:List G.Token,Rings G J U w→ Rings G K V v→linked (H:=H) Ω.val (¥ w) (¥ v)=0
def dist_V (Ω x:H.space): H.space→L[ℂ]ℂ:= innerSL ℂ x - inner ℂ x Ω • innerSL ℂ Ω
lemma ankle (Ω x y:H): dist_V (H:=H) Ω x y=linked (H:=H) Ω x y:=rfl
lemma tie_κ (Ω x y:H): linked (H:=H) Ω x y=(starRingEnd ℂ) (linked (H:=H) Ω y x):=by unfold linked; rw [map_sub,map_mul]; simp [inner_conj_symm]; ring
-- form factor on entire ℋ (for separate sectors)
abbrev Pale := ∀ x∈Height S Ω G J,∀ y∈Height S Ω G K,linked (H:=H) Ω.val x y=0
include e hΩ u d v' d'
lemma extinct (h:LocSplit S Ω G J K U V): Pale S Ω G J K:=by
 let f(x y:H):=linked (H:=H) Ω.val x y; have he(w)(p:Rings G J U w): ∀ y∈Height S Ω G K,f (¥ w) y=0:=by
    let A:= dist_V (H:=H) Ω.val (¥ w); rw [← plot_reach S Ω hΩ G K X e V v' d']; intro y V'; refine (topologicalClosure_minimal (s:=CensusR S Ω G K V) (t:=A.ker) (span_le.mpr ?_) A.isClosed_ker) V'; rintro i ⟨t,T',rfl⟩; exact h _ _ p T'
 intro x p y q; let A:= dist_V (H:=H) Ω.val y; rw [← plot_reach S Ω hΩ G J X e U u d] at p; have H:A x=0:= ?_; swap; · refine (topologicalClosure_minimal (s:=CensusR S Ω G J U) (t:=A.ker) (span_le.mpr ?_) A.isClosed_ker) p; rintro i ⟨w,v,rfl⟩; change f y (¥ w)=0; unfold f at he ⊢; rw [tie_κ, he w v y q, map_zero]
 rw [tie_κ,← ankle,H,map_zero]
#print axioms extinct
#print axioms census
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus
