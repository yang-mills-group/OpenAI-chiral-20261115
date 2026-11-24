import YM.SU5.FiniteGaugeData.Cirrus.Scepter
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
open Complex Filter Function Set MeasureTheory MeasureTheory.Measure Boundary OS OS.Semigroup Probe Maison Flute Mink
open scoped Topology NNReal InnerProductSpace
variable {H:Hilbert}(S: OS.Semigroup H timeAxis)(Ω:Bench S)
variable {ι:Type}(G:Canopy H ι)(J K:Set ι)(U V:Set E4)(t:G.Token)(w:List G.Token)
local notation "D"=> G.Model S Ω
local notation "X"=> Effort S Ω G
local notation "E"=> G.lens S Ω
local notation "Ω₁"=>G.focus S Ω []
local notation "T₁"=> RToken G J U
local notation "Kₐ"=> Hull S Ω G
open Canopy Submodule
variable (A B:Effort S Ω G) (Pn:Boundary.Action H)(L:G.Arrival S Ω Pn)
local notation "T₂"=> DualR S Ω G
local notation "T"=> G.Ticket S Ω
abbrev Route(w:List G.Token):= (w.map (G.conduct S Ω)).prod
set_option quotPrecheck false
lemma pays_κ (p:Rings G J U w) : Route S Ω G w ∈ Hull S Ω G J U:=by
 induction w with
 | nil=> exact (Kₐ J U).one_mem
 | cons t w ih=>
    exact (Kₐ J U).mul_mem (seeds S Ω G J U _ ⟨p.2 _ List.mem_cons_self,p.1 t List.mem_cons_self⟩) (ih ⟨fun i h=> p.1 i (List.mem_cons_of_mem _ h),fun i h=> p.2 _ (List.mem_cons_of_mem _ h)⟩)
lemma routeRules : Route S Ω G w Ω₁=G.focus S Ω w:=by induction w with
 | nil=> rfl
 | cons i w ih=> exact (congrArg (G.conduct S Ω i) ih).trans (convene ..)
-- direct word span within Domain
private def gallery:= span ℂ (G.focus S Ω '' {w|Rings G J U w})
local notation "U'"=>gallery S Ω G J U
lemma points_to (p:A∈Hull S Ω G J U) : MapsTo A (U':Set (D)) (U'):=by
 refine Algebra.adjoin_induction (R:=ℂ) (s:= G.conduct S Ω '' RToken G J U) (p:=fun A _=> MapsTo A (U':Set (D)) U') ?_ ?_ ?_ ?_ p
 · rintro _ ⟨t,v,rfl⟩; apply (show U'≤ (U').comap (G.conduct S Ω t) from span_le.mpr ?_); rintro x ⟨w,q,rfl⟩; change G.conduct S Ω t _∈ U'; rw [convene]; exact subset_span ⟨t::w,⟨fun j u=>(List.mem_cons.mp u).elim (fun h=>h ▸ v.2) (q.1 _),fun j u=> (List.mem_cons.mp u).elim (fun k=>k ▸ v.1) (q.2 _)⟩,rfl⟩
 · intro r; rw [Algebra.algebraMap_eq_smul_one]; intro x v; exact (U').smul_mem _ v
 · intro i j x y q z a h; exact (U').add_mem (q h) (z h)
 intro i j x y q z a h; exact q (z h)
abbrev save : Effort S Ω G →ₗ[ℂ] D := LinearMap.applyₗ Ω₁
abbrev Sales(U:Set E4): (Hull S Ω G J U)→ₗ[ℂ] H := (G.lens S Ω).comp ((save S Ω G).comp (Hull S Ω G J U).toSubmodule.subtype)
lemma Treasury : CensusR S Ω G J U=LinearMap.range (Sales S Ω G J U):=by
 let S':=Hull S Ω G J U; let V:= Sales S Ω G J U; let R:=CensusR S Ω G J U; have he: R=(U').map (E):=by unfold gallery; rw [map_span,Set.image_image]; rfl
 apply le_antisymm (span_le.mpr ?_) (fun x p=> ?_); · rintro x ⟨w,p,rfl⟩; refine ⟨(⟨Route S Ω G w,pays_κ S Ω G J U w p⟩: S'),?_⟩; exact congrArg (E) (routeRules ..)
 obtain ⟨A,rfl⟩:= p; have h:Ω₁∈ U':= subset_span ⟨[],⟨by simp [CloseParty],by simp [enrolled]⟩,rfl⟩
 change V A∈ R; rw [he]; exact mem_map_of_mem ( f:= E) ((points_to S Ω G J U A.val A.property) h) -- f binder
lemma coincides : CensusR S Ω G Set.univ U=Maison.LocalSeed S Ω G U:=by
 let S':=T; apply congrArg (span ℂ); ext x; constructor
 · rintro ⟨w,t,rfl⟩; exact ⟨_, ⟨w,t.1,rfl⟩,rfl⟩
 rintro ⟨y,⟨w,t,rfl⟩,rfl⟩; exact ⟨w,⟨t,fun _ _=>Set.mem_univ _⟩,rfl⟩
variable (hΩ:∀ x:E4,M S x Ω.val=Ω.val)(u:IsOpen U)(u':U.Nonempty)
include hΩ L u u'
lemma blessed : DenseRange (Sales S Ω G Set.univ U):=by
 intro x; change x∈ (LinearMap.range (Sales S Ω G Set.univ U)).topologicalClosure; rw [← Treasury,coincides,census S Ω hΩ G Pn U u u' L]; exact Submodule.mem_top
-- densely negative case. not extending to multiplierC.No.
omit u u'
lemma separating (z:separated U V)(v:IsOpen V)(v':V.Nonempty)(t:A∈ Hull S Ω G J U)(q:A (G.focus S Ω [])=0): A=0:=by
 let Z:= Kₐ Set.univ V; let l:=(blessed S Ω G V Pn L hΩ v v'); let K:= Sales S Ω G Set.univ V; obtain ⟨B,p,z'⟩:= reserve S Ω G J U A Pn L t; have he:B=0:= by
    ext1 x; apply lensI G S Ω; apply l.eq_of_inner_right ℂ; intro u; let S':=u.val; change inner ℂ (E (S' Ω₁)) (E (B x))=inner ℂ _ (E 0); rw [← z']; let h:= LinearMap.congr_fun (apart S Ω G J Set.univ U V A _ Pn L z t u.property).eq (Ω₁); rw [show A (S' Ω₁)= S' (A Ω₁) from h, q]; simp
 apply uniq_δ S Ω G 0 0 Pn L (fun x y=>by simp) (he ▸ twoSide S Ω G A B z')
#print axioms separating
#print axioms Treasury
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.Cirrus.PavilionM
