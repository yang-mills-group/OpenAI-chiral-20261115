import YM.SU5.FiniteGaugeData.Brique.Pike
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
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {g:ℝ}{u v:ℕ→ℕ} {I:ℕ→Family (tent Y h)→ℕ→ℂ} {E:ℕ→Family (tent Y h)→ℂ}
set_option quotPrecheck false
variable (K:Journey.Universal Y h u v I E) (S:Finset Cover) (s i k:ℕ)
local notation "K₁"=> (tent Y h)
local notation "r̂"=> (Λ.J.n)
local notation "Ρ"=> (storeH Λ.V)
local notation "ΛV"=> (pace Λ)
local notation "ζ"=> zen (slopeF Λ.W g) (storeH Λ.V).C
section
include K
lemma enoughR :∀ᶠ i:ℕ in atTop, Roomy S (side Y (u i) s):=by
 filter_upwards [((momentum Y s).comp K.pick.grow_i.tendsto_atTop).eventually (roomy_sides S K₁)] with i p; rw [show side Y (u i) s= _ from (terrain Y h (Y.ir _) s).symm]; exact p
lemma together_sub (f g:Family K₁)(p: InTest K₁ true S false f)(q: InTest K₁ true S false g): InTest K₁ true S false (f-g) ∧ E s (f-g)= E s f-E s g:=by obtain ⟨f,rfl⟩:= Hierarchy.certify S K₁ f p; obtain ⟨g,rfl⟩:= Hierarchy.certify S K₁ g q; rw [←map_sub]; exact ⟨compose_t ..,map_sub (singer Y h S s K) ..⟩
private lemma coveted (g0:0≤g)(C:∀ᶠ s:ℕ in atTop, Club Y g s) (o:Cover)(r:ℕ)(t:ℝ)(p:0<t) : ∀ᶠ s:ℕ in atTop, 1/4 < ‖E s (umbrella (carpetB o r Λ.J.n) t (tent Y h))‖:= by
 let Z:= carpetB o r (r̂); let D:= sphereR r (r̂); let B:=umbrella Z t K₁; let f:=frost Λ.K.top.clip; let W:= hat Λ.R.L Λ.x; let I:= Pressure.temp; let A:=Real.exp (slopeF Λ.W g*((4:ℝ)*(2*D+addgap K₁:ℕ))^4); have hw:Tendsto W atTop atTop:= Steam.horizons (V:=Λ.V) Λ.x
 have hu:Tendsto (fun s=>2*Real.exp (-f (W s))*A) atTop (𝓝 0):=by
    have hz : Tendsto (fun s=>Real.exp (-f (W s))) atTop (𝓝 0):= Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ((frostT _).comp hw))
    simpa using (hz.const_mul 2).mul_const A
 filter_upwards [C, ((show Tendsto Pressure.temp atTop (𝓝 0) from (by simpa using Work.E09.radiusB_temp 0)).comp hw).eventually (ge_mem_nhds p), hu.eventually (gt_mem_nhds (show (0:ℝ)<3/4 from by norm_num))] with s d f₀ A'
 have hx(j:Side)(x:Fields ((K₁).c j)): ‖(1-B) j x‖ ≤ (2:ℝ):= (norm_sub_le ..).trans (by have hm:‖(1:FC (Single ((K₁).c j)))‖=1:=norm_one; change ‖(1:FC (Single ((K₁).c j)))‖+‖B j x‖≤_; linarith only [show ‖B j x‖ ≤1 from roof_line ..,hm]) -- tune
 obtain ⟨hZ,hV⟩:=together_sub Y h K (scape o D) s 1 B .one ((bower Z t _).widen.mono (sap_marks o r (r̂)))
 have he := coverage Z Y h K g0 d hZ (show (0:ℝ)≤2 from by norm_num) hx (2*D) (by rw [union_eq_right.mpr (sap_marks o r (r̂))]; exact scape_shape o D)
 rw [show troubles K₁ Z (Pressure.temp (hat Λ.R.L Λ.x s))*(1-B)=1-B from harsh_w Z t _ K₁ p f₀,hV,(K.gaugeMatter ..).1] at he; have hz: ‖1-E s B‖ < 3/4:=he.trans_lt A'; have hp:=norm_sub_norm_le (1:ℂ) (E s B); change 1/4<‖E s B‖; rw [norm_one] at hp; linarith
variable (o:Cover)(r:ℕ)
omit K
lemma establish (q:S⊆ scape o r) (v:ℝ) : cargo (coveredB o r (side Y i s) (scape o (sphereR r Λ.J.n)) q (exceedsB o r Λ.J.n)) (bedH (carpetB o r Λ.J.n) v ∘ onC _) 1 = sold Y h s i (umbrella (carpetB o r Λ.J.n) v (tent Y h)) := by unfold sold; rw [shield_equality]; exact Eq.symm (castK (terrain Y h (Y.ir i) s) (bedH (carpetB o r Λ.J.n) v))
where castK {n m:Side}(h:n=m)(V:LinksC→ℂ):ship h (fun x:Fields n=> V (onC n x.1) • 1) =(fun x:Fields m=> V (onC m x.1) • 1):=by subst m; rfl
end
abbrev still (Λ:Preparation)(g:ℝ) := thresholdH (pace Λ) (zen (slopeF Λ.W g) (storeH Λ.V).C) ≤ Λ.h -- h first before observations
variable (V:Travels Λ)(r:still Λ g)(g0:0≤g)(C:∀ᶠ s:ℕ in atTop, Club Y g s)
section
variable {t v':ℝ}
variable (y:Cover)(m w:ℕ)
local notation "ô"=> nodeC y
abbrev penB (k m w:ℕ):= spreadB k m+w
local notation "ℳ"=> penB (pace Λ) m w
local notation "P"=> ℳ+w
local notation "D"=> sphereR (penB (pace Λ) m w+w) Λ.J.n
local notation "Z"=> scape (nodeC y) D
local notation "U"=> scape (nodeC y) (ℳ+w)
local notation "ΛΠ"=> scape (nodeC y) (penB (pace Λ) m w)
local notation "M̂"=> side Y i s
local notation "A"=> (carpetB (nodeC y) (ℳ+w) Λ.J.n)
-- uniforms all fixed spatial S at any sufficiently high level. Open vacancy region all g chosen
structure Badge (ι:ℝ) (a:Family (tent Y h))(σ : Window.Family) : Prop where
 room : Roomy Z (side Y i s)
 someone : InTest K₁ true Z false a
 company : ∃ x,∃ L: Mark (side Y i s) →ₗ[ℂ]ℂ, (∀ b:Family K₁, InTest K₁ true Z false b → L (sold Y h s i b)= E s b) ∧ Community (c:=Λ) σ (region Z M̂) (region ΛΠ M̂) (vergeNative y ΛV m M̂) (wrap (More M̂) (nodeC y)) (coveredB (T:=ΛΠ) (nodeC y) P M̂ Z (scape_mono (Nat.le_add_right ..)) (exceedsB ..)) (bedH A ι ∘ onC _) (sold Y h s i a) x L -- L linear
-- syntax coe arrows in structure. implicit parameters verify
include V g0 C K
lemma bore (q:1 ≤ m)(x:2*w+Λ.J.n+10+addgap (tent Y h) ≤ m)(X:Vast Λ (photoB Λ g) sheenB pitchV (pace Λ) w t v'): ∃ τ:ℝ, 0<τ ∧ ∀ᶠ s:ℕ in atTop, ∀ᶠ i:ℕ in atTop, ∀ σ: Window.Family,∃ a:Family (tent Y h), Badge Y h (E:=E) s (u i) y m w τ a σ:=by
 have hv:ΛΠ⊆ U:=scape_mono (Nat.le_add_right ..); let b:=(Ρ).e*t; have hb:0<b:=mul_pos (Ρ).posse.l X.warmth; obtain ⟨τ,p,O⟩:=healthB (nodeC y) P (r̂) (b:=Λ.J.k) (y:=Λ.d) hv b hb Λ.J.ht
 refine ⟨τ,p,?_⟩; filter_upwards [coveted Y h K g0 C (nodeC y) P τ p,C] with s c G₀
 let Y₀:=photoB Λ g
 let V₀:=storeH Λ.V; let W:=per sheenB (m^4); have he:0≤W:=pow_nonneg (by have he:0<(sheenB/2)⁻¹:=inv_pos.mpr (half_pos shineP); linarith) _; let A_:=wholesale Y h K s Z (scape_shape (nodeC y) D) g0 V G₀ X.font he (1/4) (heightCost Λ Y h g (manner Λ.J.n ΛV w m (addgap K₁) x) q g0)
 filter_upwards [A_,enoughR Y h K Z s,side_grows Y s h K.pick.grow_i (pitchV+(2*(2*D+1)+1)),masters Y s h K.pick.grow_i V] with i k₀ qR B S σ
 obtain ⟨k,c',z'⟩:= ((k₀ S).and ((Y.uv_grows.comp K.pick.grow_k).tendsto_atTop.eventually_ge_atTop s)).exists; let i':=u i
 let N:=side Y (u i) s; let M:=vergeNative y ΛV m N; let K₀:=coveredB ô P N Z hv (exceedsB ô P (r̂)); have hz:2*(2*D+1)<(More N).val:= by change _<N.val*2; change _≤ N.val at B; omega
 have hg:P≤D:=(by unfold sphereR; omega); obtain ⟨L,Mh⟩:=authority Y h K s (u i) Z qR; let G:=b
 have hz0: 1/4 < ‖L (cargo K₀ (bedH A τ ∘ onC _) 1)‖:=by
    unfold K₀; change 1/4 < ‖L (cargo (coveredB (nodeC y) P (side Y (u i) s) Z hv (exceedsB ..)) (bedH A τ ∘ onC _) 1)‖; rw [establish Y h ΛΠ s (u i) ô P hv τ,Mh _ ((bower A τ K₁).widen.mono (sap_marks ô P (r̂)))]; exact c
 have hk:spreadB ΛV m ≤ D:= (Nat.le_add_right ..) |>.trans ((Nat.le_add_right ℳ w).trans hg) -- wait Nat.le_add_right a b: ?
 have ht:M.card=m^4:= cardinalN qR hk
 obtain ⟨W',Ψ,W'Z⟩:= demographic Y s (u i) (v k) Z S z' X qR (region ΛΠ N) (region U N) M (wrap (More N) ô) K₀ (bedH A τ ∘ onC N) (O τ p le_rfl N (by omega) _ (posters_p ..)) L (sparse_stretch hz hk) σ (reachN w) (halo_walk ℳ w ô N) (image_subset_image (exceedsB ô P (r̂))) (by change _≤N.val at B; exact (show pitchV≤ N.val by omega)) hz0 (by
    rw [ht]; intro f Q Γ B p P_B e r; obtain ⟨iC,rfl⟩:= sold_surj Y h Z s (u i) qR f Γ; have v:=compose_t Z K₁ iC; rw [Mh _ v]; exact c' z' _ v Q B p P_B e r)
 obtain ⟨C,rfl⟩:= sold_surj Y h Z s (u i) qR W' W'Z.unwear.zone; exact ⟨composeQ K₁ Z C,qR,compose_t ..,Ψ,L,Mh,W'Z⟩
end
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
