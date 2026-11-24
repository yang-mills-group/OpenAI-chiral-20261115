import YM.SU5.FiniteGaugeData.Eight.Likeness
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Eight
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ: Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x)
variable {u v:ℕ→ℕ}{I:ℕ→ Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}
variable (K:Universal Y h u v I E){P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)
variable (A:∀ i:Axis, Repertory Y h K R i)
open Hills Tint
variable (S T:Finset Cover)(s i k:ℕ) {g α C D ε θ C₀:ℝ}
local notation "Kₜ"=> tent Y h
local notation "N"=> side Y i s
local notation "Ω"=> (Y.voyage i).CapeT s
local notation "E₁"=> W (tent Y h)→ₗ[ℂ]ℂ
-- author at each phase, actual Φ extended to all W. Arbitrary extension; never pay outside W!
section
variable (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ) 
local notation "Κ"=> (tent Y h)
local notation "M"=> momentm Y i s
local notation "ψ"=> sold Y h s i
local notation "U₁"=> W (tent Y h)
private def manV (K:Calibration): Charm.W K→ₗ[ℂ] Family K:= (well K).val.toLinearMap -- val name
-- leftInv
open scoped Classical
abbrev Model (s:ℕ) : Family (tent Y h)→ₗ[ℂ]ℂ:= (Φ s).comp (manV (tent Y h)).leftInverse
#print Model
lemma Modell (x:W (tent Y h)): Model Y h Φ s x.val=Φ s x:= congrArg (Φ s) (LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (show Injective (manV Kₜ) from fun _ _ e=>Subtype.ext e)) x)
-- torus mark license (for all even supported). 'in quotes', handles averaged tests. not asserting that λ invariant of noncandidates; only functional on Frank.E.
structure Senate (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ)(U: Mark (side Y i s) →ₗ[ℂ]ℂ): Prop where
 price : ∀ (f:Mark (side Y i s))(x:Family (tent Y h)), AtSupport false (region S (side Y i s)) f → InTest Kₜ true S false x → sold Y h s i x=dewG (side Y i s) f → U f=Model Y h Φ s x
-- build using sold_catalog inverse, dew linear on Envelope. 
private def willG (S:Finset Cover)(n:Side): Submodule ℂ (Mark n) where
 carrier:={x| AtSupport false (region S n) x}; zero_mem':= AtSupport.zeroM; add_mem':=fun p q=> AtSupport.addM p q; smul_mem':=fun c x p=> AtSupport.smulM p c
private def windP(S:Finset Cover)(n:Side): willG S n→ₗ[ℂ]Mark n where
 toFun x:= dewG n x.val
 map_add' x y:= dewAdd x.property y.property
 map_smul' z x:= dewScale ..
theorem votes (p:Roomy S (side Y i s)) : ∃ L: Mark (side Y i s)→ₗ[ℂ] ℂ, Senate Y h S s i Φ L:=by
 let q:= (sold Y h s i).comp (composeQ Kₜ S); let Q:=q.leftInverse; let Z:=willG S N; let U:=Z.subtype; let M':=(windP S N).comp U.leftInverse; let G:=(composeQ Kₜ S).comp (Q.comp M'); refine ⟨(Model Y h Φ s).comp G, ⟨fun f x e t p' => ?_⟩⟩; obtain ⟨y,rfl⟩:=Hierarchy.certify S Kₜ x t; let A':Z:= ⟨f,e⟩; have hx: Q (q y)=y:=LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (sold_catalog_inj Y h S s i (roomy_hosp _ p))) _; have he:M' (U A')=q y:= ((congrArg (windP S N) (LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr (show Injective U from Z.subtype_injective)) A')).trans p'.symm); change Model Y h Φ s (composeQ Kₜ S (Q (M' (U A'))))=_; rw [he,hx]
section
variable {F:Family (tent Y h)}{x:Mark (side Y i s)} {φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ}{L:Mark (side Y i s)→ₗ[ℂ]ℂ} (V:Senate Y h S s i φ L)
include V
lemma Senate.buys (p:InTest Kₜ true S false F)(q:Durable Kₜ F)(z:Hosp S (side Y i s)): L (sold Y h s i F)= Model Y h φ s F:= V.price _ F (sold_affair Y h S s i p) p (dewFrozen _ ((sold_color Y h S s i p z).2 q)).symm
lemma Senate.one {h':Sphere Y h K R A φ}(p:Hosp S (side Y i s)) : L 1=1:=by rw [← sold_one Y h s i, Senate.buys Y h S s i V InTest.one (show Durable Kₜ _ from (well_for Kₜ (1:W Kₜ)).2) p,←identityW,Modell,h'.living]
omit V
private theorem compassG {x:Mark (side Y i s)}(p:Roomy S (side Y i s))(t:AtSupport false (region S (side Y i s)) x): ∃ w:W (tent Y h), Locator Kₜ w S ∧ sold Y h s i w.val=dewG (side Y i s) x:=by obtain ⟨V,v⟩:= sold_surj Y h S s i p _ (dewSupport t); have he:=composeQ Kₜ S V; exact ⟨⟨composeQ Kₜ S V,compose_test ..,(show Durable Kₜ _ from (sold_color Y h S s i (compose_t ..) (roomy_hosp _ p)).1 (v.symm ▸ dewNatur t))⟩,compose_t ..,v⟩
include V
lemma Senator.salvage (p:Roomy S (side Y i s))(t:AtSupport false (region S (side Y i s)) x): ∃ y:W (tent Y h), Locator Kₜ y S ∧ sold Y h s i y.val=dewG (side Y i s) x ∧ L x=φ s y:= by obtain ⟨y,hP,e⟩:=compassG Y h S s i p t; exact ⟨y,hP,e,(V.price x y.val t hP e).trans (Modell ..)⟩
end
variable {a:Axis}{m w n b:ℕ}
-- buy on native mark L.Price. Φ delayed with common conditions. 
include K R A
local notation "Δ"=> storeH Λ.V
local notation "ξ"=> Quest.zen (slopeF Λ.W g) (Δ).C
variable {vD:Axis→ℕ}(lP:Club Y g s)(uQ:∀ᶠ s in atTop,Club Y g s)
include lP
lemma wholesaleV (p:∀ i,∃ b:ℤ,film b (vD i) S i)(T:Crags α Λ w ε)(q:0≤g)(c:0≤C)(e:lighting m α C*Real.exp (ξ*capR (tent Y h) vD)<θ): ∀ᶠ i:ℕ in atTop,∀ y:Master Y s (u i),∀ᶠ k:ℕ in atTop,∀ z:s≤Y.uv (v k), let V:= side Y (u i) s; let U:= region S V; let Q:=(Y.voyage (u i)).CapeT s
 ∀ (f g:Mark V), AtSupport false U f→ AtSupport false U g→ (∀ z, ‖f z‖≤ C)→(∀ z,‖g z‖ ≤ C) → (∀ x,g (drawn Q x)=f (drawn Q x))→Crater w (tailCost (Δ).c (Δ).C w) ε (posters Y s (u i) (v k) y z w).bleed.peg (region S (side Y (u i) s)) g m false→∀ (Φ:ℕ→ W (tent Y h) →ₗ[ℂ]ℂ)(L:Mark V→ₗ[ℂ]ℂ),Sphere Y h K R A Φ → Senate Y h S s (u i) Φ L → ‖L f‖ ≤ θ:=by
 filter_upwards [enoughR Y h K S s,polar Y h K R A S s lP p T q c e] with i v₀ t y; filter_upwards [t y] with k Q z; intro V U Q' f g u₀ t' q' vF G w' Φ L hp ℓV; obtain ⟨F,vT,uH,H⟩:= Senator.salvage Y h S s (u i) ℓV v₀ u₀; rw [H]; apply Q z F vT _ _ Φ hp; rw [uH]; exact dewBound q'; unfold Tax; rw [uH]; refine Hull.dew (c:=(Δ).c) (C:=(Δ).C) (y:=(Δ).e) _ (?_) (posters_p Y s (u i)) w' G t' vF; exact (Δ).posse.tanker _ y.2 (Brush Λ.V _ (credit_full Y _ _ _ z)) Λ.d y.1 -- t' may shadow; separate T.Enough type of Casing with c etc. implicit inference might stuck
omit lP
#print axioms wholesaleV
-- coverage binder uniform in local support even when unrelated, changing s after needed Box.S and durations.THIS limit statement includes every Φ.E. include cut.
local notation "vV"=> Pressure.temp (hat Λ.R.L Λ.x s)
local notation "f₁"=> Steam.frost Λ.K.top.clip (hat Λ.R.L Λ.x s)
open scoped Classical
variable (Z:Finset (Face ℤ))
omit K R A
abbrev seesT (K:Calibration)(Z:Finset (Face ℤ))(r:ℝ) : Charm.W K:=⟨troubles K Z r,⟨⟨carpet Z,undone K Z r⟩,by simp⟩,(qualified K Z r)⟩
private lemma capsT' (Ko:Calibration)(f:W Ko)(r:ℝ)(c:Width Ko f C)(m':Side): let x:=seesT Ko Z r*f; let T:=carpet Z∪ S; let m:=Ko.c m'; RealWidth Ko x m' C ∧ Glints 1 (region T m) r (x.val m'):=by
 intro x T m; let Q:=seesT Ko Z r
 constructor; · intro z; change ‖(troubles Ko Z r m' z)*f.val m' z‖ ≤ C; exact (norm_mul_le ..).trans (le_trans (mul_le_of_le_one_left (norm_nonneg _) (hovers Ko Z r z)) (c m' z))
 change Glints 1 _ _ ((troubles Ko Z r m')*(f.val m')); exact Glints.shrink r (tripped Ko Z r m') (Finset.image_subset_image (show carpet Z⊆ T from subset_union_left))
private lemma capsT (f:W (tent Y h))(r:ℝ)(c:Width Kₜ f C) : let x:=seesT Kₜ Z r*f; let y:= sold Y h s i x.val
 (∀ z,‖y z‖ ≤ C) ∧ Glints 1 (region (carpet Z∪S) N) r y:=by
 intro x y; let T:=carpet Z∪ S; let Q:=seesT Kₜ Z r
 let V:= capsT' S Z Kₜ f r c (momentm Y i s); let hV:= terrain Y h (Y.ir i) s; change (∀ z,‖ship hV (x.val (momentm Y i s)) z‖≤ C)∧ Glints 1 _ r (ship hV _)
 exact castQ (terrain Y h (Y.ir i) s) (x.val (momentm Y i s)) T (t:=r) V.1 V.2
where castQ {n m:Side}(h:n=m)(x:Mark n)(T:Finset Cover){t:ℝ}(c: ∀ z, ‖x z‖≤ C)(hp:Glints 1 (region T n) t x): (∀ z, ‖ship h x z‖≤ C)∧Glints 1 (region T m) t (ship h x):=by subst n; exact ⟨c,hp⟩
include K R A lP in
lemma coverageV (p:∀ i,∃ b:ℤ,film b (vD i) (carpet Z∪S) i)(c:0≤C)(g':0≤g)(u_:Sphere Y h K R A Φ)(f:W (tent Y h))(q: Locator Kₜ f S)(e: Width Kₜ f C) : ‖Model Y h Φ s (troubles Kₜ Z vV*f.val)‖ ≤ C*Real.exp (-f₁)*Real.exp (slopeF Λ.W g * capR Kₜ vD):=by
 let T:= carpet Z∪ S; let Q:=seesT Kₜ Z vV; let x:=Q*f
 rw [show troubles Kₜ Z vV*f.val = x.val from rfl,Modell]; apply le_of_forall_gt_imp_ge_of_dense; intro w hv; obtain ⟨i,p'⟩:= (troublePrice Y h K R A T s lP p g' c hv).exists; obtain ⟨k,h₀⟩:= p'.exists
 have U:= capsT Y h S s (u i) Z f vV e
 exact h₀ x (locate_join Kₜ _ (locate_sub Kₜ (undone Kₜ Z vV: Locator Kₜ Q _) subset_union_left) (locate_sub Kₜ q subset_union_right)) U.1 U.2 Φ u_
#print axioms votes
end
end YM.CF.Buffered.Afterglow.Hierarchy.Eight
