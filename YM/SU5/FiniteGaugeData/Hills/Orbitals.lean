import YM.SU5.FiniteGaugeData.Hills.View
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
namespace Hills
open Nacre Heat Charm Chrono Journey SalonG Terrace
variable (a j:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)
local notation "T"=> StructureH Y h a W' R A
local notation "U"=> (StructureH Y h a W' R A).Unity
local notation "D"=> dip (U)
local notation "P'"=>planeP (U)
local notation "U'"=> cpo (U)
local notation "C"=> Camera Y h a W' R A
local notation "W1"=> W (tent Y h)
local notation "E'" f:max=> E s ((f:W (tent Y h)).val)
variable {x y:W (tent Y h)} (f:Plan Y h a d x)(A':A.space.Op)(e:0<d)
include A
-- star compatibility within one view.Motion.Still time axis.T=Terrace
variable (f':W (tent Y h))
include A
-- Sigma.Schwinger presentation.W.Fixed level
abbrev orbitSeed : Camera Y h a W' R A:= (dip ((StructureH Y h a W' R A).Unity)) (goldStar Y h W' R a A)
local notation "Ω"=> orbitSeed Y h a W' R A
lemma orbit_lift : (U') (orbitSeed Y h a W' R A)=goldStar Y h W' R a A:=by rw [orbitSeed,castC]; exact inlet (goldHill Y h a W' R A)
lemma orbit_norm : ‖orbitSeed Y h a W' R A‖=1:=by rw [←yen («U»:= U), orbit_lift]; exact gold_norm ..
def route : W (tent Y h) →ₗ[ℂ] (Camera Y h a W' R A).Op where
 toFun := steadyL Y h s a W' R A
 map_add' := fun _ _=> accountSum ..
 map_smul' := fun _ _=> accountSub ..
local notation "X" i:max=> route Y h i a W' R A
lemma route_formula : route Y h s a W' R A x=social (U) (Wedge Y h s a d W' R A f e):= steady_price Y h s a d W' R A _ f e
lemma stayP (z:ℤ) : route Y h s a W' R A (clockW Kₜ j z f')= route Y h s a W' R A f':=persist_space ..
lemma orbit_value : inner ℂ (orbitSeed Y h a W' R A) ((route Y h s a W' R A f') Ω)= E s f'.val:= by
 obtain ⟨d,e,z,p⟩:= house Y h a f'; rw [← invariantW Y h s a z W' f',← stayP Y h s a a W' R A f' z, route_formula Y h s a d W' R A p e]; rw [sightS,orbit_lift]; exact pocketT .. -- needs p
lemma route_nil : route Y h s a W' R A 1=1:=by
 rw [route_formula Y h s a 1 W' R A (x:=1) (plan_un Y h a 1) Nat.zero_lt_one, wedge_identity Y h s a 1 W' R A Nat.zero_lt_one]
 let A':= tock Y h s W' R a a A (1:ℕ) (fun _=>zero_le_one)
 -- absorb by unit.
 change social (U) A'=1; rw [← one_mul A', socialP,social_id]
lemma route_take : route Y h (s+1) a W' R A (Charm.next Y h s W' R f')=route Y h s a W' R A f':=by
 obtain ⟨d,e,y,p⟩:= house Y h a f'; let x:= clockW Kₜ a y f'; let w:= (Λ.R.L.val:ℤ)*y
 rw [← stayP Y h s a a W' R A _ y,← stayP Y h (s+1) a a W' R A _ w]; unfold w; rw [← promote_clock]; have hv:= Nat.mul_pos Λ.R.L.property e; rw [route_formula Y h s a d W' R A p e, route_formula Y h (s+1) a _ W' R A (Plan.upgraded Y h s W' R p) hv,← wedge_step Y h s a d W' R A p e (Plan.upgraded Y h s W' R p) hv]
lemma route_any : route Y h (s+n) a W' R A (ascended Y h s W' R n f') = route Y h s a W' R A f' := by
 induction n with
 | zero=> rfl
 | succ n ih=> change route Y h (s+n+1) a W' R A (Charm.next Y h (s+n) W' R _)= _; rw [route_take,ih]
lemma route_mirror : route Y h s a W' R A (fire Kₜ a 0 f')= star (route Y h s a W' R A f'):= by
 obtain ⟨d,e,z,p⟩:= house Y h a f'
 let x:= clockW Kₜ a z f'; let y:= mateW Kₜ a d x; have hp:y=clockW Kₜ a d (fire Kₜ a 0 x):=(freezing_tides ..).symm
 have he: route Y h s a W' R A (fire Kₜ a 0 f')= route Y h s a W' R A y:=by rw [hp,stayP]; unfold x; rw [clock_neg,stayP]
 rw [he,←stayP Y h s a a W' R A f' z,route_formula Y h s a d W' R A p e,route_formula Y h s a d W' R A (x:=y) (Plan.other Y h p) e,← social_star,wedge_star]
lemma guestPrice : ‖route Y h s a W' R A x‖≤ ‖Wedge Y h s a d W' R A f e‖:=by rw [route_formula Y h s a d W' R A f e]; exact social_bound _
include e in
lemma plate_emit : route Y h s a W' R A x (orbitSeed Y h a W' R A)=dip (U) (store Y h s W' R a A (pocket Y h a d f)):=by -- e not included!
 rw [route_formula Y h s a d W' R A f e]; change dip (U) (Wedge Y h s a d W' R A f e ((U') Ω))= _; rw [orbit_lift, SalonG.wink]
variable (t:Decko Y h a)
lemma exhibit : route Y h s a W' R A t.val (orbitSeed Y h a W' R A)= (D) (store Y h s W' R a A t):=by
 obtain ⟨S,p,g⟩:= t.property; obtain ⟨d,i,V⟩:= resident Y h S a _ p g; exact plate_emit Y h s a d W' R A V i -- Subtype ext defeq
lemma seed_whole : DenseRange (fun w:Playlist.Show.Vect Y h a 0 => (dip (StructureH Y h a W' R A).Unity) (A.paid w)):=
 (show Surjective (dip U) from fun x=> ⟨cpo U x, allC («U»:=U) x⟩).denseRange.comp A.issued (dip U).continuous
lemma phase_ext {x y:Camera Y h a W' R A}(p:∀ s f, inner ℂ (route Y h s a W' R A f (Ω)) x=inner ℂ (route Y h s a W' R A f (Ω)) y): x=y:= by
 apply ext_inner_left ℂ; intro t; refine (seed_whole Y h a W' R A).induction (P:=fun v:C=>inner ℂ v x=inner ℂ v y) ?_ (isClosed_eq (by fun_prop) (by fun_prop)) t; rintro _ ⟨w,rfl⟩; obtain ⟨k,e⟩:= (eventual_table Y h W' R a A w).exists; dsimp only at e ⊢; rw [←e,← exhibit]; exact p _ _
lemma phase_ac {M N:(Camera Y h a W' R A).Op}(p:∀ i k x y,inner ℂ ((X i) x Ω) (M ((X k) y Ω))=inner ℂ ((X i) x Ω) (N ((X k) y Ω))): M=N:= by
 ext1 t; refine (seed_whole Y h a W' R A).induction (P:=fun v:C=> M v=N v) ?_ (isClosed_eq M.continuous N.continuous) t; rintro _ ⟨w,rfl⟩; obtain ⟨k,e⟩:= (eventual_table Y h W' R a A w).exists; dsimp only at e ⊢; rw [←e,← exhibit]; apply phase_ext Y h a W' R A; intro i v; exact p _ _ _ _
#print axioms orbit_value
#print axioms route_any
#print axioms route_mirror
#print axioms phase_ext
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
