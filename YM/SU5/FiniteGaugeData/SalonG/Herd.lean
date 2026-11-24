import YM.SU5.FiniteGaugeData.SalonG.Knitting
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
namespace SalonG
open Nacre Heat Charm Chrono Journey
variable (a:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)
local notation "D"=> Decko Y h a
local notation "X"=> (A.space:Type)
local notation "M" t:max=> store Y h t W' R a A
local notation "π"=>nectar Y h s W' R a
local notation "N" n:max=> energyS Λ d n
variable {f x:W (tent Y h)}(z:Plan Y h a d f)(y:Decko Y h a)(q:0<d)
local notation "V" z:max=> Wedge Y h s a d W' R A z q
local notation "δ"=> (energyS Λ d n)
-- Operator bound expressed relative to Catalog gauge profile if f has some Plan (not same S) control. universal.
variable (B ε:ℝ)
include A q z
lemma wedge_lip (p:Locator (tent Y h) f S): ‖Wedge Y h s a d W' R A z q‖ ≤ ‖reading Kₜ S f p‖*duration S/venus Y h S s a d:= by
 let T:= venus Y h S s a d; let b:=‖reading Kₜ S f p‖*duration S/T; have ht:0<T:=Real.exp_pos _; have hb:0 ≤ b:=div_nonneg (mul_nonneg (norm_nonneg _) (duration_pos _).le) ht.le
 have hx:b*T=duration S*‖reading Kₜ S f p‖:=by unfold b; rw [div_mul_cancel₀ _ ht.ne',mul_comm]
 apply le_of_forall_pos_le_add; intro ε p'; refine wedge_bound Y h S s a d W' R A z q (b+ε) p (by positivity) fun m v=>?_ ; exact (width_read p m v).trans (hx.symm.le.trans (mul_le_mul_of_nonneg_right (by linarith) ht.le))
lemma wedge_diff (p:Locator Kₜ f S) (e:Plan Y h a d x)(v:Locator Kₜ x S):
    dist (Wedge Y h s a d W' R A z q) (Wedge Y h s a d W' R A e q)≤duration S / venus Y h S s a d * dist (reading Kₜ S f p) (reading Kₜ S x v):= by
 let w:= (-1:ℂ) • x; let m':=Plan.subsidy Y h e (-1); let t:= Plan.plus Y h z m'; let p':= locate_sum Kₜ S p (locate_scale Kₜ S (-1) v)
 have he:reading Kₜ S (f+w) p'=reading Kₜ S f p+(-1:ℂ) • reading Kₜ S x v:= compose_inj S Kₜ (by rw [map_add,map_smul,reading_p,reading_p,reading_p]; rfl)
 have hp:= wedge_lip Y h S s a d W' R A t q p'
 rw [he,wedge_sum Y h s a d W' R A z q m' t,wedge_scale Y h s a d W' R A e q _ m',neg_one_smul,show (-1:ℂ) • reading Kₜ S x v = -(reading Kₜ S x v) from neg_one_smul ℂ (reading Kₜ S x v),← sub_eq_add_neg,← sub_eq_add_neg] at hp
 rw [dist_eq_norm,dist_eq_norm]; exact hp.trans_eq (by ring)
-- after P still independent! hence compact for sets; Affiliate later.Dilation prices.
omit A q z
include W' R
lemma panorama {F: Type*}(f:F→ Catalog S)(p:∀ i, ‖f i‖≤B): IsCompact (closure (Set.range fun i=>P S s (f i))):=by
 -- product p paidpt & all choices index, image closure
 let F0:=GridStep Λ l S
 let I':= PaidPt Y S s × F
 obtain ⟨k,g⟩:=eligible_exists Y u v W'.pick.grow_k
 let C': I'→ Catalog F0:= fun i=> transitionQ Y h S s i.1 (f i.2)
 have h':= collective Y h S s (fun i:I'=>i.1) (fun i=>f i.2) B (fun i=>p _)
 refine h'.of_isClosed_subset isClosed_closure ((closure_minimal ?_ isClosed_closure))
 rintro w ⟨i,rfl⟩; refine isClosed_closure.mem_of_tendsto (audition _ _ (calls Y h S s R k g) (tendsto_const_nhds (x:=f i))) ?_; filter_upwards [eligible_offer Y h S s W' k g] with j t
 rw [snag_pay Y h S s _ _ t]; exact subset_closure (Set.mem_range.mpr ⟨((⟨(u j, v (k j)),t⟩:PaidPt Y S s),i),rfl⟩)
lemma ascending_ord (p:Locator (tent Y h) f S): reading Kₜ (GridStep Λ l S) (Charm.next Y h s W' R f) (locate_next Y h S s W' R f p) = P S s (reading Kₜ S f p):= by apply compose_inj _ Kₜ; rw [reading_p,keeps Y h S s W' R f p]
include A q
lemma lounge {F:Type*} (f:F → W (tent Y h))(p:∀ i,Plan Y h a d (f i))(e:∀ i,Locator Kₜ (f i) S)(v:∀ i,‖reading Kₜ S (f i) (e i)‖≤ B) : IsCompact (closure (Set.range fun i=>Wedge Y h s a d W' R A (p i) q)):=by
 let S':= GridStep Λ l S; let Y' (i:F):= P S s (reading Kₜ S (f i) (e i)); let m:= Λ.R.L.val*d; have hp:0 < m:= by unfold m; positivity
 let U:= duration S' / venus Y h S' (s+1) a m; have hU:0<U:= div_pos (duration_pos S') (Real.exp_pos _); let T (i:F):= Wedge Y h s a d W' R A (p i) q
 have ht:IsCompact (closure (Set.range Y')):= panorama Y h S s W' R B (fun i=> reading Kₜ S (f i) (e i)) v
 have he(i j:F): dist (T i) (T j) ≤ U*dist (Y' i) (Y' j):= by
    have g:=wedge_diff Y h S' (s+1) a m W' R A (Plan.upgraded Y h s W' R (p i)) hp (locate_next Y h S s W' R _ (e i)) (Plan.upgraded Y h s W' R (p j)) (locate_next Y h S s W' R _ (e j)); rw [ascending_ord Y h S s W' R (e i), ascending_ord Y h S s W' R (e j),← wedge_step Y h s a d W' R A (p i) q _ hp,← wedge_step Y h s a d W' R A (p j) q _ hp] at g; exact g
 have hn:TotallyBounded (Set.range T):=by
   refine (Metric.totallyBounded_iff («α»:=A.space.Op)).mpr fun ε h=> ?_; obtain ⟨C,e,p⟩:= Hierarchy.equip (t:=ε/U) (by positivity) Y' (ht.totallyBounded.subset subset_closure); refine Hierarchy.issue T e fun i=> ?_; obtain ⟨j,u,v⟩:= p i; have hz:= (lt_div_iff₀ hU).mp v; exact ⟨j,u,(he i j).trans_lt (by rw [mul_comm]; exact hz)⟩
 exact hn.closure.isCompact_of_isClosed isClosed_closure
#print axioms lounge
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
