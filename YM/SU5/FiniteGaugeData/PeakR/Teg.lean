import YM.SU5.FiniteGaugeData.PeakR.Shelby
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
namespace Corners
open ArchiveK.Midway
open Hierarchy.Eight Chaperone
open Largo
open Tint Charm Largo
variable {U U' S T:Finset Cover}{σ τ:Window.Family}
section birth
variable {n:Side}
private lemma maple (p:S.image nodeC⊆T)(h:Hosp T n)(t:List (Site n))(q:t.toFinset⊆ S.image (wrap n)) : ∃ l:List Cover,l.map (wrap n)=t ∧ l.toFinset⊆ S ∧∀ x, l.count x ≤ t.count (wrap n x):=by
 have he : ∃ l:List Cover,l.map (wrap n)=t∧ l.toFinset⊆ S:=by
    clear p h; induction t with
    | nil=> exact ⟨[],rfl,by simp⟩
    | cons i t ih=>
       rw [List.toFinset_cons] at q; obtain ⟨b,z⟩:= insert_subset_iff.mp q; obtain ⟨x,h,rfl⟩:= mem_image.mp b; obtain ⟨l,h',e⟩:= ih z
       exact ⟨x::l, (by rw [List.map_cons,h']),by rw [List.toFinset_cons,insert_subset_iff]; exact ⟨h,e⟩⟩
 obtain ⟨l,rfl,f⟩:=he; refine ⟨l,rfl,f,fun x=>?_⟩; -- inequality even without inj
 clear f q p h; induction l with
 |nil=> simp
 |cons a t ih=>
   simp only [List.map_cons,List.count_cons]; by_cases h:x=a; · subst a; simp [ih]
   simp only [beq_iff_eq]; rw [if_neg (show ¬a=x from Ne.symm h)]; omega
-- account as singular Pair.Front and roof (wide). Abbrev relation at E equals discord. Note post Room.Subevents.all sequences. strict center positive at evaluator of R.Stance.
end birth
section
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {u v:ℕ→ℕ}{R:ℕ→Family (tent Y h)→ℂ} {I:ℕ→ Family (tent Y h)→ℕ→ℂ}{g r a:ℝ} (K:Universal Y h u v I R) (t:∀ᶠ s:ℕ in atTop, Club Y g s) (p:Travels Λ)
set_option quotPrecheck false
local notation "P"=> (tent Y h)
-- Desired cross pair impedance includes BEHIND. persistence. don't include adjacent.Ahead when taking linear combinations. 
variable (U U' D L L':Finset Cover)(f₁ f₂: Family (tent Y h))
section
-- internal conversion when Roomy. main.LLU. Support housing.Includes.Seams.
variable (i s:ℕ)
local notation "M"=> side Y i s

variable {Z:Family (tent Y h)→ℂ}
private theorem skate (L0 : Mark (side Y i s) →ₗ[ℂ]ℂ)(t: ∀ (f:Family (tent Y h)),InTest P true D false f→Tint.Durable P f→ L0 (sold Y h s i f)=Z f)
 (P₁:Roomy L' (side Y i s)) (y1:InTest P true L false f₁)(y2:InTest P true L' false f₂)(u:L⊆ D)(v:L'⊆D) -- remove
 (z:Window.Brique.Free (region L' M) (sold Y h s i f₂)) (e:covariant (sold Y h s i f₁))(z₁:covariant (sold Y h s i f₂))
 (Q₁:Hosp L M)(Zl:U.image nodeC ⊆ L')(Zr:U'.image nodeC ⊆ L')(J: Mirage.discord L0 (sold Y h s i f₁) (sold Y h s i f₂) ≠0)(K₀:Disjoint (U.image nodeC) (U'.image nodeC))
 (m:List (Site M))(x:m≠[])(h₀:∀ i0, m.count i0≤2)(c:m.toFinset⊆ U.image (wrap M)) (X₁:∀ x, Mirage.Chord σ τ M ((U'.image (wrap M)).image node) m (sold Y h s i f₂ x)): Operon Y h Z L L' f₂ ∧ ∃ l:List Cover, StencilB P σ τ (U'.image nodeC) L' l f₂:=by
 obtain ⟨l,hl,hL,hC⟩:=maple Zl (roomy_hosp _ P₁) m c; refine ⟨⟨y2,f₁,y1,(sold_color Y h L s i y1 Q₁).mp e,?_⟩, l,Zr, ?Front,?W,(fun x=>(hC x).trans (h₀ _)),?PP,?_, (sold_color Y h L' s i y2 (roomy_hosp _ P₁)).mp z₁⟩; swap
 · exact fun x p=> Zl (mem_image_of_mem _ (hL (List.mem_toFinset.mpr p)))
 case W=> exact fun s=> x (by rw [←hl,s,List.map_nil])
 case PP=> exact fun x p z=> disjoint_left.mp K₀ (mem_image_of_mem _ (hL (List.mem_toFinset.mpr p))) z
 swap
 · let U:=U'.image nodeC; obtain ⟨B,y⟩:= castQ (terrain Y h (Y.ir i) s) (f₂ (momentm Y i s)) U l z (fun x=>by rw [← chordN,hl]; exact X₁ x)
   exact Chaperone.press4 P σ τ U L' l y2 ((terrain Y h (Y.ir i) s).symm ▸ P₁) Zr (fun x hx=> Zl (mem_image_of_mem _ (hL (List.mem_toFinset.mpr hx)))) B y
 unfold decor; let H:= (sold_color Y h L s i y1 Q₁).mp e; let V:= (sold_color Y h L' s i y2 (roomy_hosp _ P₁)).mp z₁; rw [← t f₁ (y1.mono u) H,←t f₂ (y2.mono v) V, ← t _ ((y1.mono u).mul (y2.mono v)) ((allG P).mul_mem H V),sold_mult]; exact J
where castQ {s N:Side}(h':s=N) (x:Mark s) (U:Finset Cover)(t:List Cover)(p:Window.Brique.Free (region L' N) (ship h' x))(q:∀ z,Mirage.Chord σ τ N (region U N) (t.map (wrap N)) (ship h' x z)): Window.Brique.Free (region L' s) x∧∀ z,Mirage.Chord σ τ s (region U s) (t.map (wrap s)) (x z):=by subst s; exact ⟨p,q⟩
#check skate
end
variable (x₁:0≤g)
include p t K x₁
variable {Jt:Wicket Λ l}{Pq:Call Λ l}(RR:Rolled Y h u v Jt Pq)(Fam:∀ a:Axis,Chrono.Repertory Y h K RR a)
omit K p t x₁
abbrev crews (Λ:Preparation) (l Lk:ℕ) (g:ℝ):= optionH (zen (slopeF Λ.W g) (storeH Λ.V).C) (storeH Λ.V).c (storeH Λ.V).C Lk Λ.J.n (2*(reserve Λ l+4*Λ.block.val)) Λ.h
include K p t x₁ RR Fam
lemma Sailor (Lk:ℕ)(κ:0<Lk)(u0: crews Λ l Lk g): ∃ D S S₀:Finset Cover,S₀⊆ S ∧ (∀ a:Axis,Ahead a 0 Lk (refract a 0 D))∧ (∀ a:Axis,Ahead a 0 Lk S)∧
 ∀ᶠ s:ℕ in atTop, ∀ (Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ), Hills.Sphere Y h K RR Fam Φ→∀ σ τ:Window.Family,σ.2=τ.2→σ.1≠τ.1→∃ A,∃ l', StencilB (tent Y h) σ τ S₀ S l' A ∧ Operon Y h (Model Y h Φ s) D S A:=by
 obtain ⟨n,m,d,q,x,A1,S',T',Sr,V⟩:=u0 -- Apos set=Q, S=Bp, T=An, Sr=Bn
 let Ψ:=helix n; let P0:=Manor Ψ Ψ d Λ.J.n; let D(b):=stagePr Ψ Ψ Lk b; have he(b):D b⊆ P0:=(Subset.trans (show D b⊆ WoodV Ψ Ψ from Finset.filter_subset ..) (Subset.trans (grain_in Ψ Ψ d) (gramS Ψ Ψ d Λ.J.n)))
 have hc: Sr.image nodeC⊆ D true:=helix_stage true Lk κ (V.field.hull false).2 (V.field.lanes false).2; have ht':A1.image nodeC⊆ D true:=helix_stage true Lk κ (V.field.hull true).1 (V.field.lanes true).1
 have hp:Disjoint (A1.image nodeC) (Sr.image nodeC):= by apply disjoint_left.mpr; intro x v t; obtain ⟨i,y,rfl⟩:=mem_image.mp v; obtain ⟨b,z,H⟩:= mem_image.mp t; exact disjoint_left.mp (show Disjoint A1 Sr from V.field.mark true) y (nodeC_inj H ▸ z)
 refine ⟨D false,D true,Sr.image nodeC,hc,refS Lk,highAhead Lk,?_⟩; let S:=Sr; let Q:= A1
 filter_upwards [shelter Y h K t p V κ x₁ RR Fam] with s c Φ J0 σ τ x y
 obtain ⟨i,z,hQ,z1,z2⟩:= (c.and ((enoughR Y h K P0 s).and ((enoughR Y h K (D false) s).and (enoughR Y h K (D true) s)))).exists
 obtain ⟨L',HL⟩:= votes Y h P0 s (u i) Φ hQ; obtain ⟨A,C,P₁,P₂,p,q,v,V,z,c',f,T⟩:=z σ τ x y L' Φ J0 HL
 obtain ⟨b,rfl⟩:= sold_surj Y h (D true) s (u i) z2 C P₂.zone; obtain ⟨a,rfl⟩:= sold_surj Y h (D false) s (u i) z1 A P₁.zone
 obtain ⟨W',l',G⟩:= skate Y h (Z:=Model Y h Φ s) Q S P0 _ _ _ _ (u i) s L' (fun f t z=> HL.buys Y h P0 s (u i) t z (roomy_hosp _ hQ)) z2 (compose_t ..) (compose_t ..) (he false) (he true) P₂ p q (roomy_hosp _ z1) ht' hc v hp V z c' f T
 exact ⟨_,l',G,W'⟩
end
#print axioms Sailor
end Corners
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
