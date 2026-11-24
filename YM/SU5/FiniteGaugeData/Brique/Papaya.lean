import YM.SU5.FiniteGaugeData.Brique.Amber
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
open Function
-- independent link rotations). Reader comparison ABI before any vacuum refinement. Excludes hypothetical factorization on even the physical (not color-nonsinglet) readings. Formulated directly as a single observable no such evaluation can assign this value. Handles exactly positive level > pure flat. 
-- Period here is chart for matter Fock algebra & coefficients (signed frames carry); gauge evaluation always on the infinite COVER. Use all continuous functions. Invariance on functions local on S (can even require EVERY shape or only these). Values of E defined on only physical class suffice for contradiction. No hypothesis normalizations etc. 
open ContinuousMap
variable {K:Calibration} {S U :Finset Cover}{σ:Window.Family}{t:List Cover}{F:Family K}
lemma Copse.Rbasis (P:Copse K S U σ t F): ∃ x∈t,∀ (n:Side)(h: Hosp S (K.c n))(W:Pane (K.c n)),
    F n (simultaneous (lamp (wrap (K.c n) x)) (W,W))=SU.z^(powerS σ) • F n (W,W):= by
 obtain ⟨y,p⟩:∃ y,y∈t:= List.exists_mem_of_ne_nil _ P.walk; exact ⟨y,p,fun i h W=> P.center σ h y p _⟩
-- comparison recipe on any Hosp. G gauge on LinksC, MATTER letter state may be *any* linear map on FC at resolution/chart. normalized maps not needed. Standard product states/independence would compute each narrow recipe this way on a fixed finite stencil. (No continuity, no mass-gap.) Can't read this one Gauge covariant observable even on ONE roomy chart like that. Extends to arbitrary finite linear combinations of such evaluations and pointwise limits on narrow singlets.
structure Solitary (S:Finset Cover) (ν:ContinuousMap LinksC ℂ→ₗ[ℂ]ℂ) : Prop where
 shift (x: Cover→SU.E) (V W:ContinuousMap LinksC ℂ) (p:Lattice.LocalOn S V) (q:∀ z,W z=V (gauge x z)) : ν W = ν V
-- Fock on narrow families is joy: f m x uses only FIRST link. `replant` gives exactly that function on chart (and via `take_family` independence despite periodic gauge rotations). For any dense open family no assertion that all phase representations work without `Roomy`. Can even require only center. 
variable (S K)
def fockOf(m:Side)(x:Family K)(M:FC (Single (K.c m))→ₗ[ℂ]ℂ): LinksC→ℂ:= fun V=> M (x m (replant S (K.c m) (V,V)))
lemma soleC (m:Side)(v:Family K)(x: InTest K false S false v) (M:FC (Single (K.c m))→ₗ[ℂ]ℂ): Continuous (fockOf K S m v M):= by
 have hc:= x.only_cont m; obtain ⟨h,l,c⟩:=hc; unfold fockOf; simp_rw [l]; exact M.continuous_of_finiteDimensional.comp (c.comp (show Continuous (Satin.graft S (K.c m)) from by apply continuous_pi; intro i; unfold Satin.graft; split; exact continuous_apply _; exact continuous_const))
def soloC (m:Side)(v:Family K)(x: InTest K false S false v) (M:FC (Single (K.c m))→ₗ[ℂ]ℂ):ContinuousMap LinksC ℂ:= ⟨fockOf K S m v M,soleC K S m v x M⟩
lemma Copse.isolates (P:Copse K S U σ t F) (ν:ContinuousMap LinksC ℂ→ₗ[ℂ]ℂ)(s:Solitary S ν){n:Side}(p:Roomy S (K.c n))(M:FC (Single (K.c n))→ₗ[ℂ]ℂ): ν (soloC K S n F (P.narrow σ) M) = 0 := by
 obtain ⟨x,z,Q⟩:= P.Rbasis; let N:= K.c n; let V:= soloC K S n F (P.narrow σ) M; let g:= lamp (wrap N x); let W:= fun a=> g (wrap (More N) a); let u:= SU.z^(powerS σ); let f:= F n; let h:= (InTest.support (P.narrow σ) n).dep; let p':=roomy_hosp _ p
 have he: Lattice.LocalOn S V:= by intro a b v; exact congrArg M (h (replant S N (a,a)) (replant S N (b,b)) (graft_agrees S p v) (graft_agrees S p v))
 have hv(a:LinksC): V (gauge W a)= u * V a:= by
    let b:= Satin.graft S N a; let b':= Satin.graft S N (gauge W a); have hb: Agrees (region S N) b' (gauge g b):=by
       rintro ⟨i,d⟩ r _; obtain ⟨j,k,rfl⟩:= mem_image.mp r; unfold b' b; rw [graft_at S p' _ k]; unfold Lattice.gauge; rw [graft_at S p' _ k]; unfold W; rw [map_add,wrap_step] -- policy clock
    change M (f (b',b')) = u * M (f (b,b)); rw [show f (b',b')= F n (simultaneous g (b,b)) from h _ _ hb hb, Q n p' b, map_smul]; rfl
 change ν V=0; by_contra k; have hx:ν (u • V)=ν V:= s.shift W V _ he (fun v=>(hv v).symm); rw [map_smul,smul_eq_mul] at hx; apply powerS_nonunit σ (mul_right_cancel₀ k (hx.trans (one_mul _).symm)) -- rewrite localon
variable {S K}
-- stronger cut `buy` recollection in Chisel/Amber. Monad statement. 
structure Luster (K:Calibration)(y:Family K)(Q:Finset (Face ℤ)) (r:ℝ): Prop where
 power : 0 < r
 bright (m:Side)(x:Fields (K.c m)): y m x≠0 → ∀ i∈Q,r < SU.group.chord (faceValue (onC _ x.1) i)
lemma Copse.lives (r:ℝ)(t:0<r)(K:Calibration)(Q:Finset (Face ℤ))(F:Family K): Luster K (shineB r Q K*F) Q r:= by
 refine ⟨t,fun m x g=> amber_fades r Q t x.1 (fun p=>g ?_)⟩; rw [Pi.mul_apply,Pi.mul_apply]; unfold shineB scalar; dsimp only [Function.comp_apply]; rw [p,zero_smul,zero_mul]
-- interpret F m (replant...) also on ANY LinksC: curvature gap if mark in recipe support. Good for comparing on pure flat.
lemma Luster.release {r:ℝ}{Q:Finset (Face ℤ)}(P:Luster K F Q r)(u:carpet Q ⊆ S){n:Side}(h:Hosp S (K.c n))(W:LinksC): F n (replant S _ (W,W))≠0 → ∀ i∈Q,r < SU.group.chord (faceValue W i):=by
 intro v i p; let N:=K.c n; let w:= replant S N (W,W); refine lt_of_lt_of_le (P.bright n _ v i p) (le_of_eq ?_); apply congrArg SU.group.chord; apply travel_local i.1 _ (onC N w.1) W; intro e t t'; exact Satin.tail S N h W e (u (mem_biUnion.mpr ⟨i,p,List.mem_toFinset.mpr t⟩)) -- h before any period

variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {u v:ℕ→ℕ}{E:ℕ→Family (tent Y h)→ℂ} {I:ℕ→Family (tent Y h)→ℕ→ℂ} (S:Finset Cover)
variable (K5:Universal Y h u v I E)
local notation "Κ"=> (tent Y h)
include K5 in
lemma reflect_live {S:Finset Cover}{s:ℕ}{F:Family (tent Y h)}(P:Copse Κ S U σ t F)(q:E s F≠0)(Q:Finset (Face ℤ)) (T:carpet Q⊆ S): ∃ r:ℝ, ∃ x:Family (tent Y h), Luster Κ x Q r ∧ Copse Κ S U σ t x ∧ E s x≠0:=by
 obtain ⟨r,he⟩:= ((soles Y h s Q P T K5).eventually (isOpen_ne.mem_nhds q)).exists
 exact ⟨_,_,Copse.lives _ (Real.exp_pos _) Κ Q F, shine_spec (germB r) Q Κ P T,he⟩
variable {g:ℝ}
include K5
-- ahead axis fixed, PLANE 0. Badge costs independent spatial translate, keep E itself not covariance assertion. every h reservation & Loom shared. list of faces interior S nonempty; all those used. 
theorem vitality (V:Travels Λ) (p: ∀ᶠ s:ℕ in atTop, Club Y g s)(z: still Λ g) (e:0≤g) (i:Axis):∃ (S Q:Finset Cover)(A: Finset (Face ℤ)), A.Nonempty ∧ carpet A ⊆ S ∧ Ahead i 0 (reserve Λ l) S ∧ ∀ᶠ s:ℕ in atTop, ∀ σ: Window.Family, ∃ t F, Copse (tent Y h) S Q σ t F ∧ E s F≠0 ∧ ∃ r,Luster (tent Y h) F A r:= by
 obtain ⟨w,t,q,X⟩:=probe_receipts Λ g z; let m:=2*w+Λ.J.n+10+addgap Κ; let k:=pace Λ; let d:=penB k m w; let D:=sphereR (d+w) Λ.J.n
 obtain ⟨y,q⟩:=habitat i D (reserve Λ l) 0; let S:=scape (nodeC y) D; obtain ⟨v₀,p0,c⟩:= bore Y h K5 V e p y m w (by unfold m; omega) le_rfl X; let A:=carpetB (nodeC y) (d+w) Λ.J.n; let f₀:Face ℤ:= (nodeC y,⟨(0,1),by decide⟩); let R: Finset Cover:= scape (nodeC y) d \ (vergeCover y k m).image nodeC; have hv: carpet A ⊆ S:=sap_marks ..; refine ⟨S,R,A,⟨f₀,mem_product.mpr ⟨sap_here ..,mem_univ _⟩⟩,hv,q,?_⟩
 filter_upwards [c] with s p σ
 obtain ⟨i,hg⟩:= p.exists; obtain ⟨F,v⟩:=hg σ; obtain ⟨e,t,P⟩:= v.work Y h s (u i) m w v₀ σ y F; obtain ⟨r,x,T,H,E'⟩:=reflect_live Y h K5 P e A hv
 exact ⟨t,x,H,E',r,T⟩
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
