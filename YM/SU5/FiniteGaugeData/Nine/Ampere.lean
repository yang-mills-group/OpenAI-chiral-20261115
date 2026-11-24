import YM.SU5.FiniteGaugeData.Nine.Sepia
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 430000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Chaperone Heat Afterglow.Hierarchy.Eight Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
set_option quotPrecheck false
open Window.Pivot Tint
variable (o:Cover) {N:Side}
local notation "Μ"=> Single N
open Fock Fock.Brique
local notation "H₀"=> (polarQ o)
open Nacre
-- precise handed probe class incl GI and orientation. allows finite comb & changes of rooms. Empty union avoid typeclass.
inductive Stall (K:Calibration)(S:Finset Cover)(σ:Window.Family) : Family K→ Prop where
| off : Stall K S σ 0
| haloP {x:Family K}{T:Finset Cover}{t:List Cover}: Copse K S T σ t x→Stall K S σ x
| add {x y:Family K}: Stall K S σ x→Stall K S σ y→Stall K S σ (x+y)
| scale {x:Family K}: Stall K S σ x→∀ c:ℂ, Stall K S σ (c•x)
section
variable {K:Calibration}{S U R:Finset Cover}{σ:Window.Family}{F G:Family K}
variable (p:Stall K S σ F)
include p
lemma Stall.quotes : InTest K false S false F∧ Durable K F:=by
 induction p with
 | off=> exact ⟨.zero, fun i g x=> (map_zero _).symm⟩
 | haloP v=> exact ⟨Copse.narrow σ v,v.coin⟩
 | add _ _ a b=> exact ⟨a.1.add b.1, (by intro i g x; change _+_=twist _ (_+_); rw [map_add]; exact congrArg₂ (·+·) (a.2 i g x) (b.2 i g x))⟩
 | scale _ c a=> exact ⟨.smul _ a.1,by intro i g x; change c • _= twist _ (c • _); rw [twist_scalar]; exact congrArg (fun t:FC _=> c • t) (a.2 i g x)⟩
lemma Stall.turn : Stall K (πS o S) σ (pageP o K F) := by
 induction p with
 | off=> rw [map_zero]; exact .off
 | haloP v=>obtain ⟨_,w⟩:=pi_revenue o K v; exact .haloP w
 | add _ _ a b=> rw [map_add]; exact .add a b
 | scale _ _ a=>rw [map_smul]; exact .scale a _
lemma Stall.sub (q: Stall K S σ G) : Stall K S σ (F-G):=by rw [sub_eq_add_neg, ← neg_one_smul ℂ]; exact .add p (.scale q _)
lemma Stall.dd (τ:Window.Family)(h:F≠0): Haze K σ τ S F:= by
 induction p with
 | off=>exact (h rfl).elim
 | haloP v=> exact .oneB (.fromCopse v)
 | @add x y i j a b=>
    by_cases p:x=0; · rw [p,zero_add] at h ⊢; exact b h
    by_cases p':y=0; · rw [p',add_zero] at h ⊢; exact a h
    exact .plus (a p) (b p')
 | scale i z a=> apply Haze.mul (a (fun p=> h (by rw [p,smul_zero])))
-- use without h! StencilB anti, linear includes 0
lemma Stall.solo (ν: ContinuousMap LinksC ℂ→ₗ[ℂ]ℂ)(s:Solitary S ν){n:Side}(v:Roomy S (K.c n))(M:FC (Single (K.c n))→ₗ[ℂ]ℂ): ν (soloC K S n F p.quotes.1 M) = 0:=by
 by_cases h:F=0; · subst F; rw [show soloC K S n _ _ M=(0:ContinuousMap LinksC ℂ) from ?_,map_zero]; ext1 i; exact map_zero M
 exact Haze.solos (Stall.dd p σ h) ν s v M
end
section wharf
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)(s i:ℕ)(σ:Window.Family)
local notation "Υ"=> (side Y i s)
local notation "ΛF"=> tent Y h
local notation "ζ"=> sold Y h s i
lemma sold_orb (F:Family (tent Y h)) : sold Y h s i (pageP o ΛF F)=pageF o Υ (sold Y h s i F):=by unfold sold; exact castC (terrain Y h (Y.ir i) s) _
where castC {n m:Side}(p:n=m)(x:Mark n) : ship p (pageF o n x)=pageF o m (ship p x):=by subst n; rfl
variable (S T:Finset Cover)(Q:Finset Cover)(q: Q.image nodeC ⊆ T)(v:T⊆ S)
variable (F: Corset (region T (side Y i s)) (region S (side Y i s)) (wrap (More (side Y i s)) o))(W: Pane (side Y i s)→ℂ)
variable (p:Roomy S (side Y i s))(u: Stump (region S (side Y i s)) W)
local notation "D"=> (Q.image (wrap Υ))
local notation "T₀"=> T \ Q.image nodeC
local notation "T₂"=> region T Υ\ (Q.image (wrap Υ)).image node
local notation "τ" c:max => (loadF F W) (centB Υ c)
include v p q
lemma σ_size : (Q.image (wrap Υ)).image node⊆ region T Υ:= by rw [chordN]; exact image_subset_image q
lemma σ_size_aux : T₂=region (T \ Q.image nodeC) Υ:=by
 rw [chordN]; ext k; constructor<;> intro g
 · obtain ⟨g,t⟩:=mem_sdiff.mp g; obtain ⟨x,y,rfl⟩:=mem_image.mp g; exact mem_image_of_mem (wrap _) (mem_sdiff.mpr ⟨y,fun u=>t (mem_image_of_mem (wrap _) u)⟩)
 obtain ⟨x,y,rfl⟩:=mem_image.mp g; refine mem_sdiff.mpr ⟨mem_image_of_mem (wrap _) (sdiff_subset y),fun t=>?_⟩; obtain ⟨z,t,k⟩:=mem_image.mp t; exact (mem_sdiff.mp y).2 (((roomy_hosp S p).seat_ (v (q t)) (v (sdiff_subset y)) k) ▸ t)
include u
lemma solo_cost {x:FC (Single (side Y i s))}{t:List (Site (side Y i s))} (e:t≠[])(g:t.Nodup)(d:t.toFinset⊆ Q.image (wrap (side Y i s)))(u': Trio σ (side Y i s) (region T (side Y i s) \ (Q.image (wrap (side Y i s))).image node) t x): ∃ y:Family (tent Y h), Stall (tent Y h) S σ y ∧ sold Y h s i y=(loadF F W) (centB Υ x):=by
 let A:= centB Υ x; have hA:Trio σ Υ T₂ t A:= cent_tiny x u'; let C:=cargo F W A; have hp:T₀⊆ S:= (Subset.trans sdiff_subset v)
 have heC:Window.Brique.Free (region S Υ) C:= delivered F u (image_subset_image v) (hA.fines (fun k x=>σ_size Y s i S T Q q v p (mem_image_of_mem node (d (List.mem_toFinset.mpr x)))) sdiff_subset); have hc:covariant C:= cargos F u A (cent_invariant x)
 obtain ⟨Y₀,H⟩:= sold_surj Y h S s i p C heC.zone; let y:= composeQ ΛF S Y₀; have hY: InTest ΛF true S false y:=compose_t ..; have ht':Durable ΛF y:= (sold_color Y h S s i hY (roomy_hosp S p)).1 ((show C=sold Y h s i y from H.symm) ▸ hc) -- H orientation?
 obtain ⟨r,L,hr⟩: ∃ r:List Cover, r.map (wrap Υ)=t∧∀ x∈r,x∈Q:=by
    suffices w:∀ x:List (Site (side Y i s)),x.toFinset⊆ Q.image (wrap (side Y i s))→∃ r:List Cover,r.map (wrap (side Y i s))=x∧∀ v∈r,v∈Q from w t d
    intro l u; induction l with
    | nil=> exact ⟨[],rfl,by simp⟩
    | cons a l ih=> obtain ⟨z,w,z'⟩:= mem_image.mp (u (List.mem_toFinset.mpr List.mem_cons_self)); obtain ⟨y,v,m⟩:= ih (by rw [List.toFinset_cons] at u; exact (insert_subset_iff.mp u).2)
                    exact ⟨z::y,by rw [List.map_cons,z',v],by simp [w]; exact m⟩
 let P:= momentm Y i s; have hQ(k)(h':k∈r):nodeC k∈S:= v (q (mem_image_of_mem nodeC (hr k h'))); have hV: (sold Y h s i y)=C:= H
 have hz(V:Fields (side Y i s)): Trio σ Υ (region T₀ Υ) (r.map (wrap Υ)) (sold Y h s i y V):=by rw [L,←σ_size_aux Y s i S T Q q v p,hV]; exact (hA.wind _).mul _
 obtain ⟨o₁,o₂⟩:= castB (terrain Y h (Y.ir i) s) _ (T \ Q.image nodeC) S r (show Window.Brique.Free (region S Υ) (sold Y h s i y) from hV.symm ▸ heC) hz
 refine ⟨y,Stall.haloP (T:=T \ Q.image nodeC) ⟨fun x=> e (L.symm.trans (by rw [x]; rfl)), List.Nodup.of_map _ (L.symm ▸ g),hp,hQ,fun x p h'=> (mem_sdiff.mp h').2 (mem_image_of_mem _ (hr x p)),press4 ΛF σ T₀ S r hY ((terrain Y h (Y.ir i) s).symm ▸ p) hp hQ o₁ o₂,ht'⟩,hV.trans (load_exact F (centB Υ x)).symm⟩ -- notation
where castB {n P:Side}(e:n=P) (x:Mark n)(R S:Finset Cover)(t:List Cover)(L:Window.Brique.Free (region S P) (ship e x))(s:∀ w,Trio σ P (region R P) (t.map (wrap P)) (ship e x w)): Window.Brique.Free (region S n) x ∧ ∀ w,Trio σ n (region R n) (t.map (wrap n)) (x w):= by subst n; exact ⟨L,s⟩
lemma punch {x:FC (Single (side Y i s))}(t:Barque σ (Q.image (wrap (side Y i s))) (region T (side Y i s)\ (Q.image (wrap (side Y i s))).image node) x): ∃ y:Family (tent Y h), Stall (tent Y h) S σ y ∧ sold Y h s i y=(loadF F W) (centB Υ x):= by
 induction t with
 | stage t e g d u'=> exact solo_cost o Y h s i σ S T Q q v F W p u e g d u'
 | zero=> exact ⟨0,.off,by rw [map_zero,map_zero,map_zero]⟩
 | add _ _ a b=> obtain ⟨y,u,h⟩:= a; obtain ⟨x,v,w⟩:=b; exact ⟨y+x,.add u v, by rw [map_add,map_add,map_add,h,w]⟩
 | mul i _ a=> obtain ⟨y,u,h⟩:=a; exact ⟨i • y,.scale u _, by rw [map_smul,map_smul,map_smul,h]⟩
lemma life_orbit(Sx:πS o S=S){x:FC (Single (side Y i s))}(t:Barque σ (Q.image (wrap (side Y i s))) (region T (side Y i s)\ (Q.image (wrap (side Y i s))).image node) x): ∃ y:Family (tent Y h), Stall (tent Y h) S σ y ∧ sold Y h s i y=(loadF F W) (centB Υ x)-pageF o Υ ((loadF F W) (centB Υ x)) ∧ pageP o ΛF y = -y:=by
 obtain ⟨y,w,v⟩:=punch o Y h s i σ S T Q q v F W p u t; exact ⟨y-pageP o ΛF y,w.sub (Sx ▸ w.turn o), by rw [map_sub,sold_orb,v], by rw [map_sub,page_proj]; abel⟩ -- order of stall.turn
end wharf
#print axioms Stall.turn
#print axioms punch
end YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.Quest.PoleP.Stall.quotes
