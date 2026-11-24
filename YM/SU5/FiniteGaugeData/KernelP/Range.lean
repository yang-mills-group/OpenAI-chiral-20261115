import YM.SU5.FiniteGaugeData.KernelP.Papacy
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
open Nacre Heat Charm Chrono SalonG Journey Hills Playlist Show
namespace KernelP
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h W' R a)
variable {Φ:ℕ→ Charm.W (tent Y h)→ₗ[ℂ]ℂ}(S':Sphere Y h W' R A Φ)
variable (a:Axis)(z:ℤ)(d n:ℕ)
local notation "D"=> Decko Y h a
local notation "W₀"=> W Kₜ
variable (V:Harbor Y h W' R Φ a) (p:Ahead a 0 (reserve Λ l) S) (B:ℝ)(b:0<B)
local notation "T"=> Hills.route Y h s a W' R (A a)
local notation "W₁"=> refract a 0 S∪S
-- relative l1 catalogue at next enough all y.Lean.tc.T
private lemma reading_f (x:W Kₜ)(e: Locator Kₜ x S)(t:Locator Kₜ (helve Kₜ a x x) (refract a 0 S∪S)): ‖reading Kₜ (W₁) (helve Kₜ a x x) t‖≤ (duration S * ‖reading Kₜ S x e‖)^2:= by
 obtain ⟨m,hQ⟩:= (roomy_sides (W₁) Kₜ).exists; apply offered_bound _ _ _ (roomy_hosp _ hQ); intro v; rw [reading_p,sq]; let g:= width_read e m; exact RealWidth.mule (RealWidth.reflected a g 0) g v -- tune `m` elab
include S' V b
lemma score_bound (u:∀ (x:W (tent Y h)) (p:Locator Kₜ x (W₁)), ‖Hills.route Y h s a W' R (A a) x‖ ≤ B*‖reading Kₜ W₁ x p‖)(x:D)(e:Locator Kₜ x.val S) : ‖V.leaf s x‖ ≤ √B*duration S * ‖reading Kₜ S x.val e‖ := by
 rw [← sq_le_sq₀ (norm_nonneg _) (by have ht:=duration_pos S; positivity : 0≤ (√B*duration S *‖reading Kₜ S x.val e‖:ℝ)), flash_metric Y h s W' R a V]; unfold flashH
 let y:= helve Kₜ a x.val x.val; let t:= helve_loc a e e; refine (Complex.re_le_norm (Φ s y)).trans ((S'.stamp s y a).trans ((u _ t).trans ((mul_le_mul_of_nonneg_left (reading_f Y h S a _ e t) b.le).trans_eq (by rw [mul_assoc (√B),mul_pow (√B),Real.sq_sqrt b.le]))))
set_option synthInstance.maxHeartbeats 60000 in
lemma score_lip (u:∀(x:W (tent Y h))(p:Locator Kₜ x (W₁)),‖Hills.route Y h s a W' R (A a) x‖≤B*‖reading Kₜ W₁ x p‖)(x y:D)(r:Locator Kₜ x.val S)(t:Locator Kₜ y.val S): dist (V.leaf s x) (V.leaf s y)≤ √B*duration S*dist (reading Kₜ S x.val r) (reading Kₜ S y.val t) := by
 let w:=x-y
 have hx : Locator Kₜ (x.val-y.val) S:= by rw [sub_eq_add_neg,←neg_one_smul (R:=ℂ)]; exact locate_sum Kₜ S r (locate_scale Kₜ S _ t)
 rw [dist_eq_norm (V.leaf s x),dist_eq_norm (reading Kₜ S x.val r), reading_sub Y h S a W' R (A a) _ _ r t hx,← map_sub (f:=V.leaf s)]; exact score_bound Y h S s W' R A S' a V B b u (x-y) hx
omit S' V b
abbrev Doll (B:ℝ):= {i:Decko Y h a // ∃ v:Locator (tent Y h) i.val S, ‖reading (tent Y h) S i.val v‖≤ B}
local notation "H₁" => Doll Y h S a B
include A
variable (ε:ℝ)
-- per each price.Campus.Pal.Selection.INDEPENDENT of State!
lemma finite_doll (h_:0<ε) : ∃ t: Finset (Doll Y h S a B), ∀ x:Doll Y h S a B,∃ i∈t,∀ {Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ}, Sphere Y h W' R A Φ →∀ V:Harbor Y h W' R Φ a, dist (V.leaf s x.val) (V.leaf s i.val)<ε := by
 let S':= GridStep Λ l S; let R':= refract a 0 S' ∪ S'; obtain ⟨b,f,t⟩:= route_budget Y h R' (s+1) a W' R (A a);
 let z(v:Doll Y h S a B):Locator Kₜ v.val.val S:=Classical.choose v.property; let V(i:Doll Y h S a B):= P S s (reading Kₜ S i.val.val (z i)); have hp : 0<√b*duration S':= mul_pos (Real.sqrt_pos.2 f) (duration_pos _)
 obtain ⟨p,q,e⟩:= Hierarchy.equip (t:=ε/(√b*duration S')) (by positivity) V ((panorama Y h S s W' R B (fun i:Doll Y h S a B=>reading Kₜ S i.val.val (z i)) (fun i=>Classical.choose_spec i.property)).totallyBounded.subset subset_closure)
 refine ⟨q.toFinset,fun x=>?_⟩; obtain ⟨i,t₀,hv⟩:=e x; refine ⟨i,q.mem_toFinset.mpr t₀,fun {Φ} T' W=>?_⟩; let X(v:Doll Y h S a B):= nectar Y h s W' R a v.val
 let r(v:Doll Y h S a B):= locate_next Y h S s W' R v.val.val (z v); have H':= score_lip Y h S' (s+1) W' R A T' a W b f t (X x) (X i) (r x) (r i)
 have H(v:H₁):reading Kₜ S' (X v).val (r v)= V v:= ascending_ord Y h S s W' R (z v)
 refine lt_of_le_of_lt ?_ (?_ : (√b*duration S')*dist (V x) (V i)<ε); · rw [←H,←H,← W.up Y h s W' R a x.val, ← W.up Y h s W' R a i.val]; exact H'
 rw [mul_comm]; exact (lt_div_iff₀ hp).1 hv
lemma charged : ∃ T': Set (ℕ × Decko Y h a), T'.Countable∧∀ {Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ}, Sphere Y h W' R A Φ →∀ V:Harbor Y h W' R Φ a,DenseRange (fun x:T'=>V.leaf x.val.1 x.val.2) := by
 classical
 choose X hX using fun s S (i n:ℕ)=>finite_doll Y h S s W' R A a i ((1/2:ℝ)^n) (by positivity)
 let U(S:Finset Cover)(s i n:ℕ):= (X s S i n).image (fun x:Doll Y h S a i=>(s,x.val)); let D':Set (ℕ× Decko Y h a):= ⋃ (s:ℕ)(S:Finset Cover)(i:ℕ)(n:ℕ),(U S s i n:Set _)
 refine ⟨D',Set.countable_iUnion (fun s=> Set.countable_iUnion fun S=> Set.countable_iUnion fun i=> Set.countable_iUnion fun n=>(U S s i n).countable_toSet),fun {Φ} hx v=>?_⟩; let P:Set v.space:= Set.range (fun x:D'=> v.leaf x.val.1 x.val.2); change ∀ x:v.space, x∈ closure P
 apply leaf_lift Y h 0 W' R a v _ isClosed_closure
 intro i t y; apply Metric.mem_closure_iff.mpr; intro ε h'
 obtain ⟨S,hy,r⟩:= y.property; obtain ⟨j,w⟩:=exists_nat_ge ‖reading Kₜ S _ r‖; obtain ⟨n,p⟩:= (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (show (1/2:ℝ)<1 by norm_num)).eventually (gt_mem_nhds h') |>.exists; obtain ⟨u,x,s⟩:= hX i S j n ⟨y,r,w⟩
 have he:(i,u.val)∈D':= by apply Set.mem_iUnion.mpr; exact ⟨i,Set.mem_iUnion.mpr ⟨S,Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨n,(show _∈ U S i j n from mem_image_of_mem _ x)⟩⟩⟩⟩
 exact ⟨_,(show v.leaf i u.val ∈ P from Set.mem_range.mpr ⟨⟨_,he⟩,rfl⟩),(s hx v).trans p⟩
#print axioms charged
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
