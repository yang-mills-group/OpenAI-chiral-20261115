import YM.SU5.FiniteGaugeData.Brique.Tome
import YM.SU5.FiniteGaugeData.Brique.Sedan
set_option autoImplicit false
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
set_option quotPrecheck false
open Tint Window.Brique
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {E:ℕ→Family (tent Y h)→ℂ} (s i:ℕ) (u v:ℕ)(r:ℝ)(σ:Window.Family)
local notation "K₁" => (tent Y h)
structure Copse (K:Calibration)(S U:Finset Cover)(σ:Window.Family)(t:List Cover)(F:Family K):Prop where
 walk : t≠[]
 strand: t.Nodup
 rear : U⊆ S
 front : ∀ x∈t,nodeC x∈S
 gap : ∀ x∈t,nodeC x∉U
 output: Tableau K σ U S t F
 coin : Tint.Durable K F
-- orientation only, no `K.takes` assumptions. even Lorraine at aliased periods where one plane wraps may have different Center, pay Peggy. Need require `Hosp` for center.
variable {K:Calibration}{S U:Finset Cover}{t:List Cover}{F:Family K}
lemma Copse.narrow (c:Copse K S U σ t F): InTest K false S false F := c.output.tier c.rear c.front
lemma Copse.included (c:Copse K S U σ t F): F∈ Charm.well K:=⟨⟨⟨_,(c.narrow σ).widen⟩,by simp⟩,c.coin⟩
lemma Copse.center (c:Copse K S U σ t F){n:Side}(h: Hosp S (K.c n))(y:Cover)(p:y∈t) (V:Fields (K.c n)): F n (simultaneous (lamp (wrap (K.c n) y)) V)=SU.z^(powerS σ) • F n V:=by
 rw [c.coin n]; let N:= K.c n; let i:= wrap N y; let a:= t.map (wrap N); have he: List.Nodup a:=by
    -- list Pairwise
    refine (List.pairwise_map ..).mpr ?_; refine c.strand.imp_of_mem ?_; intro x u q z v e; apply v (nodeC_inj (h.seat_ (c.front x ?_) (c.front _ ?_) (?_))) -- tune binder order
    · exact q
    · exact z
    exact ((node_of N x).symm.trans ((congrArg node e).trans (node_of ..)))
 have hv:node i ∉ region U (K.c n):=by
    unfold i N; rw [node_of]; intro f; obtain ⟨x,h',p'⟩:=mem_image.mp f; exact c.gap y p (h.seat_ (c.rear h') (c.front y p) p' ▸ h')
 change flipsP (lamp i) _= _ ; rw [(c.output.native n V).centerP i hv, show a.count i=1 from (List.nodup_iff_count_eq_one.mp he (wrap (K.c n) y) (List.mem_map.mpr ⟨y,p,rfl⟩)),pow_one] -- notation h etc

section
-- syntactic dictionary Body of Badge trimmings from ANY such period.
variable (y:Cover)(g:Travels Λ)
local notation "d"=> pace Λ
local notation "T"=> penB (pace Λ) u v
local notation "t̂"=> penB (pace Λ) u v+v
local notation "S₁"=> scape (nodeC y) (sphereR t̂ Λ.J.n)
local notation "S₂"=> scape (nodeC y) T
local notation "A"=> vergeCover y (pace Λ) u
local notation "A₂"=> vergeNative y (pace Λ) u (side Y i s)
lemma Badge.work (F:Family (tent Y h))(P:Badge Y h (E:=E) s i y u v r F σ): E s F≠0 ∧ ∃ t:List Cover,Copse (tent Y h) S₁ (S₂ \ (vergeCover y (pace Λ) u).image nodeC) σ t F:=by
 let a:=roomy_hosp _ P.room; let N:= side Y i s; let V:=region S₁ N; let U':= region (S₂\(vergeCover y (pace Λ) u).image nodeC) N; obtain ⟨x,L,l,H⟩:= P.company
 refine ⟨l F P.someone ▸ H.marked,?_⟩; obtain ⟨t,w,v',c,hC⟩:= H.trio
 have h1:T ≤ sphereR t̂ Λ.J.n:=by unfold sphereR; omega
 have hX:(A).image nodeC⊆ S₂:=fun i h=>by obtain ⟨x,k,rfl⟩:=mem_image.mp h; exact scape_mono (show spreadB (pace Λ) u ≤ T from Nat.le_add_right ..) (chordC k)
 let A' := A; let R:= S₂\A'.image nodeC; have r₁:S₂⊆ S₁:= scape_mono h1
 have he: region S₂ N\ (A'.image (wrap N)).image node= region R N:=by
    rw [chordN]; ext i; constructor <;> intro g
    · obtain ⟨g,h⟩:=mem_sdiff.mp g; obtain ⟨x,p,rfl⟩:=mem_image.mp g; exact mem_image_of_mem (wrap _) (mem_sdiff.mpr ⟨p,fun p'=> h (mem_image_of_mem _ p')⟩)
    obtain ⟨x,hx,rfl⟩:=mem_image.mp g; refine mem_sdiff.mpr ⟨mem_image_of_mem _ (sdiff_subset hx),fun t=> ?_⟩; obtain ⟨y,p,z⟩:=mem_image.mp t; exact (mem_sdiff.mp hx).2 (((roomy_hosp S₁ P.room).seat_ (r₁ (hX p)) (r₁ (sdiff_subset hx)) z) ▸ p)
 have hβ: ∃ t':List Cover,t'.map (wrap N)= t ∧ ∀ x∈t',x∈A':=by
    suffices H:∀ t:List (Site N), t.toFinset⊆ A'.image (wrap N) → ∃ t':List Cover,t'.map (wrap N)=t ∧∀ x∈t',x∈A' from H t c
    intro t v; induction t with
    | nil=> exact ⟨[],rfl,by simp⟩
    | cons i t ih=> obtain ⟨j,k,e⟩:= mem_image.mp (v (List.mem_toFinset.mpr List.mem_cons_self)); obtain ⟨t',h,u⟩:=ih (by rw [List.toFinset_cons] at v; exact (insert_subset_iff.mp v).2)
                    exact ⟨j::t',by rw [List.map_cons,e,h],by simp [k]; exact u⟩
 obtain ⟨t',ht,u'⟩:=hβ; have hx:∀ x∈t',nodeC x∈S₁:=fun i v=>r₁ (hX (mem_image_of_mem nodeC (u' i v)))
 let tQ:= P.someone; let Pκ:=H.unwear; have hv: R⊆ S₁:= Subset.trans sdiff_subset r₁
 have hx'(z:Fields N) : Trio σ N (region R N) (t'.map (wrap N)) (sold Y h s i F z):=by rw [ht,←he,H.mark_shield]; exact (hC.wind _).mul _
 obtain ⟨o₁,o₂⟩:= castB (terrain Y h (Y.ir i) s) _ R S₁ t' H.unwear hx' 
 refine ⟨t',fun e=>w (ht.symm.trans (by rw [e]; rfl)), List.Nodup.of_map _ (ht.symm ▸ v'),hv,hx,fun x p h=> (mem_sdiff.mp h).2 (mem_image_of_mem _ (u' x p)),press4 K₁ σ R S₁ t' tQ ((terrain Y h (Y.ir i) s).symm ▸ P.room) hv hx o₁ o₂,(Tint.sold_color Y h S₁ s i tQ (roomy_hosp _ P.room)).mp H.donor⟩
where castB {N P:Side}(e:N=P) (x:Mark N)(R S:Finset Cover)(t:List Cover)(L:Window.Brique.Free (region S P) (ship e x))(s:∀ w,Trio σ P (region R P) (t.map (wrap P)) (ship e x w)): Window.Brique.Free (region S N) x ∧ ∀ w,Trio σ N (region R N) (t.map (wrap N)) (x w):= by subst N; exact ⟨L,s⟩
end
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
