import YM.SU5.FiniteGaugeData.Mirage.Lorne
import YM.SU5.FiniteGaugeData.Mirage.Scene
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
namespace Chaperone
open Largo
section
variable {U:Finset Cover}{h q N d r l l' f x g w D D':ℕ}{a:Cover}
lemma lodge_paid (v:a∈ LodgeP d N (r+g)): nodeC a∈ estate (paperP r g) (page N):=by
 obtain ⟨u0,v0,F⟩:= parish .. |>.1 v; apply (owns _).mpr; simp only [nodeC, Pi.add_apply, two_smul, Pi.one_apply]; unfold paperP page; refine ⟨fun i=>?_,?_⟩; · specialize u0 i; unfold back at u0; omega
 omega
lemma operaPaid (e:l+D ≤ r)(v:h ≤ l)(a':0<h)(i:Bool) : (Opera l D N i).image nodeC ⊆ stagePr (paperP r g) (page N) h i:=by
 intro z t; obtain ⟨u,z,rfl⟩:=mem_image.mp t; refine mem_filter.mpr ⟨lodge_paid (operaE (by omega) z), ?_⟩; obtain ⟨a,vf,q'⟩:= mem_image.mp ((porter ..).mp z).2; simp only [nodeC, Pi.add_apply, two_smul, Pi.one_apply]; rw [←q', floorInst]; cases i<;>simp only [Bool.false_eq_true,↓reduceIte] <;> omega
-- within pure.Lact
lemma operaApart (N:ℕ)(e:l+D≤ l')(b:Bool) : Disjoint ((Opera l D N b).image nodeC) ((Opera l' D' N b).image nodeC):=by
 refine disjoint_left.mpr (fun i v x=>?_); obtain ⟨v',hv,hv'⟩:=mem_image.mp v; obtain ⟨u',hu,hu'⟩:=mem_image.mp x; rw [nodeC_inj (hv'.trans hu'.symm)] at hv; obtain ⟨j,v,v'⟩:=mem_image.mp (porter ..|>.mp hv).2; obtain ⟨j',x,x'⟩:=mem_image.mp (porter ..|>.mp hu).2; have hv:= mem_range.mp v; rw [floorInst] at v'; rw [floorInst] at x'; cases b <;> simp only [Bool.false_eq_true,↓reduceIte] at v' x' <;> omega
end
section
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {u v:ℕ→ℕ}{E:ℕ→Family (tent Y h)→ℂ} {I:ℕ→ Family (tent Y h)→ℕ→ℂ}{g aa:ℝ} (K:Universal Y h u v I E) (t:∀ᶠ s:ℕ in atTop, Club Y g s) (p:Travels Λ)
variable {q d j s₀ L J n k l' U U' f r:ℕ}{S T: Finset Cover}
set_option quotPrecheck false
local notation "ξ"=> zen (slopeF Λ.W g) (storeH Λ.V).C
local notation "ω"=> tailCost (storeH Λ.V).c (storeH Λ.V).C d
local notation "Ρ"=> PlanR
local notation "Η₁"=> reserve Λ l+1
local notation "K₁"=> tent Y h
-- fee_of_prior h0 outputs thresholds. parameter data set.
abbrev Resolute (Λ:Preparation)(l:ℕ)(g:ℝ):Prop:= ∃ n l0 u l' w U r d k K A t h,DemandR (zen (slopeF Λ.W g) (storeH Λ.V).C) (storeH Λ.V).c (storeH Λ.V).C PlanR (reserve Λ l+1) Λ.J.n (2*(reserve Λ l+4*Λ.block.val)) n l0 u l' w U r d k K A t h ∧ Real.exp A+1 ≤ Λ.h
variable {α tθ:ℝ}{M B:ℕ}
-- switch writing L=reserve+1; DemandR.
local notation "Lv"=> reserve Λ l+1
local notation "Vκ"=> 24*k
local notation "Ψ"=> paperP r d
local notation "ψ"=> page (24*k)
local notation "R₁"=> WoodV (paperP r d) (page (24*k))
local notation "A₀"=> Manor (paperP r d) (page (24*k)) d Λ.J.n
local notation "K'"=> addgap (tent Y h)
variable (V: DemandR (zen (slopeF Λ.W g) (storeH Λ.V).C) (storeH Λ.V).c (storeH Λ.V).C PlanR (reserve Λ l+1) Λ.J.n (addgap (tent Y h)) n (reserve Λ l+1) U l' U' f r d k M B tθ α)
local notation "W"=> drawMask (paperP r d) (page (24*k)) d Λ.J.n (Line (paperP r d) (page (24*k)) (reserve Λ l+1))
local notation "S₁"=> stagePr (paperP r d) (page (24*k)) (reserve Λ l+1) false -- `Lv` notation parser
local notation "S₂"=> stagePr (paperP r d) (page (24*k)) (reserve Λ l+1) true
local notation "X"=> GrainV (paperP r d) (page (24*k)) d
local notation "Θ"=> Mirage.twinCost (f:ℝ) ((24*k)^3*f)
local notation "Σ"=> k^3*n
local notation "Zr"=> Line (paperP r d) (page (24*k)) (reserve Λ l+1)
local notation "At"=> Opera (reserve Λ l+1) U (24*k)
local notation "Bt"=> Opera l' U' (24*k)
include K p t h V
-- first deliver.Native L attorneys post extraction all clocks. Same s selection later. ensure Roominess at ALL dimensions as needed. 
variable (e:Real.exp B+1≤ Λ.h)(x:0≤g)
include x e
theorem launchC  : ∀ᶠ s:ℕ in atTop,∀ᶠ i:ℕ in atTop, ∀ σ τ:Window.Family, σ.2=τ.2→ σ.1≠τ.1→let X0:= side Y (u i) s; let D i:=(region (stagePr Ψ ψ Lv i) X0);
 ∀ L:Mark X0→ₗ[ℂ]ℂ, Sovereign Y h (E:=E) A₀ s (u i) L →∃ A B:Mark X0, Window.Brique.Free (D false) A ∧ Window.Brique.Free (D true) B ∧ covariant A ∧ covariant B ∧ Mirage.discord L A B≠0 ∧ ∃ v:List (Site X0),v≠[] ∧ (∀ i,v.count i≤ 2) ∧ v.toFinset ⊆ (Bt true).image (wrap X0) ∧ ∀ w, Mirage.Chord σ τ X0 (((At true).image (wrap X0)).image node) v (B w):=by
 -- note orientation L.N lower opp from first suite TRUE (At true right L1); from second false (Bt false L2); y correct. Terrain usage.
 have htH:0< Lv:=Nat.succ_pos _; have hjP:Lv+U ≤ l':= V.tune; have heP:l'+U'≤r:= V.high; have ht':Lv ≤ Ψ:=by unfold paperP; omega
 have hpr:Chart.Hires X A₀ (pegT Lv true) Zr:=fun i t=> Subset.trans ((Line_area Lv ht' (Nat.le_add_right Ψ d) (Nat.le_add_right ψ d)) i t) (gramS Ψ ψ d Λ.J.n)
 obtain ⟨dκ,y0,Fκ⟩: ∃ s':ℝ,0<s' ∧ ∀ (X':Side)(W':Loom X')(u:Hosp A₀ X'){y:ℝ}, Roof X' Λ.J.k y Λ.J.n W' → CashMask (areaH Ψ ψ d Λ.J.n Zr hpr X' u) (W s' ∘ onC X') (region X X') ((storeH Λ.V).e*tθ) W':= by exact PurchaseC Ψ ψ d Λ.J.n Zr hpr _ Λ.J.ht (mul_pos (storeH Λ.V).posse.l V.aperture) -- placeholders referencing proof.pr not allowed
 have hg:0<(Θ):= pow_pos (by positivity) _; have hk:= atEye Y h K t x (mul_nonneg hg.le hg.le) (A₀) (charmC Ψ ψ d Λ.J.n Zr) (charmLocal Ψ ψ d Λ.J.n Zr hpr) (draw_norm Ψ ψ d Λ.J.n Zr dκ) (subsidize Ψ ψ d Λ.J.n Zr y0)
 have hv: Crags B Λ d α:= ⟨by positivity,e,V.hot,V.delta⟩
 filter_upwards [t,hk] with s H z
 let W':= (storeH Λ.V); let Met:= Chaperone.wholesale Y h K s (A₀) payDeed x p H hv (mul_nonneg hg.le hg.le) _ V.price
 filter_upwards [enoughR Y h K (A₀) s, side_grows Y s h K.pick.grow_i Vκ, masters Y s h K.pick.grow_i p, Met] with i Q budget Dτ J σ τ z₀ z₁
 intro X0 D L lκ; -- beta simplifiable
 obtain ⟨u₀,⟨a₀,T₀⟩,V₀⟩:= (((J Dτ).and (show ∀ᶠ k:ℕ in atTop,s≤ Y.uv (v k) from (Y.uv_grows.comp K.pick.grow_k).tendsto_atTop.eventually_ge_atTop _)).and (heightZoom Y s M K.pick.grow_k)).exists; -- binding `((J.and q).and f) → ⟨k,and,and⟩` order. tune
 let k':=v u₀; let N':= X0; let Mk:= (((Y.voyage (u i)).X (Y.uv k')).gram s).J; let Lm:= Mk.M; let BW:=(Y.voyage (u i)).CapeT s; let Z:= (posters Y s (u i) k' Dτ T₀ d).bleed.peg; have hs:=roomy_hosp _ Q; let pf':=Fκ N' BW hs (posters_p Y s (u i)); let fκ:=areaH Ψ ψ d Λ.J.n Zr hpr X0 hs
 have hx: Lv+U≤ l':= V.tune; have hl:l'+U'≤r:= V.high; have hee: Lv ≤ Ψ:=by unfold paperP; omega
 have ha: R₁⊆ A₀:=Subset.trans (grain_in Ψ ψ d) (gramS Ψ ψ d Λ.J.n); let F1:=cornerD N' Lv hs (q₀:=ha) hee false; let F2:=cornerD N' Lv hs (q₀:=ha) hee true
 have ht: Mirage.Frame F1 F2 fκ:= CurveF N' Lv hs ha htH hee (fun i z=>hpr i ((grain_in Ψ ψ d) z)) -- tune
 let KP:= p; let r':= region (R₁) N'; let hfee:= (storeH Λ.V).posse; let Ch:= (storeH Λ.V).C; let c:= (storeH Λ.V).c; let gV:= (storeH Λ.V).e
 have hK:Casing N' Z.e (Z.Ft false) c Ch gV:= hfee.tanker Mk Dτ.2 (Brush Λ.V _ (credit_full Y s (u i) k' T₀)) Λ.d Dτ.1 -- tune
 have h0:Z.Ft false 1=funde 4 Lm N' 1:= by
    rw [show Z.Ft false _=funde Λ.K.j Lm N' 1 from jewel Λ.K.j Mk, Λ.kJ]
 let Q₀:= Θ*Θ
 have hw: Mirage.Insure N' L (region A₀ N') (region X N') Z BW (W dκ∘onC N') d (k^3*n) (ω) α Q₀:= by
    refine ⟨fun A B nA hB γ lb Ver δ=>?_, ?_,?_⟩; -- tune order masked A B
    · obtain ⟨C,rfl⟩:= sold_surj Y h A₀ s (u i) Q A γ; rw [lκ _ (compose_t ..)]; exact a₀ T₀ _ (compose_t ..) lb B hB nA Ver δ
    · exact z _ Q _ lκ
    rw [←sold_one Y h s (u i), lκ _ .one, (K.gaugeMatter ..).1]
 -- instantiate.
 let N: Side:=⟨Vκ,Nat.mul_pos (by decide) V.scale⟩; obtain ⟨P₁,P₂⟩:= V.work N (by rfl) Lm (V₀ (u i)) N' budget
 have hr₁(i:Bool): stagePr Ψ ψ Lv i⊆ R₁:= Finset.filter_subset ..
 let Hk(i:Bool)(S':Finset Cover)(t:S'.image nodeC⊆ stagePr Ψ ψ Lv i):=(show (S'.image (wrap N')).image node ⊆ D i from chordN S' N' ▸ image_subset_image t)
 refine Mirage.Insure.bouquet L F1 F2 fκ ht (t':=(ω)) hK (Λ.dpos.le) pf' h0 (image_subset_image ha) (image_subset_image (hr₁ false)) (image_subset_image (hr₁ true)) (own_halo N' d) (image_subset_image (gramS Ψ ψ d Λ.J.n)) le_rfl le_rfl hw P₁ P₂ (Hk false _ (operaPaid (by omega) le_rfl htH false)) (Hk false _ (operaPaid heP (by omega) htH false)) (Hk true _ (operaPaid heP (by omega) htH true)) (Hk true _ (operaPaid (by omega) le_rfl htH true)) ?_ (mul_nonneg (Real.exp_pos _).le W'.posse.value.le) V.buy ?_ ?_ z₀ z₁
 · rw [chordN]; apply image_subset_image; intro z t; obtain ⟨i,q,rfl⟩:=mem_image.mp t; exact lodge_paid q
 · rw [opera_card]; exact Nat.mul_le_mul_left (Vκ^3) V.finance1
 rw [opera_card]; exact Nat.mul_le_mul_left (Vκ^3) V.finance2
end
end Chaperone
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
