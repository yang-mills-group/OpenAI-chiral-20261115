import YM.SU5.FiniteGaugeData.Hills.Tariff
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
open Nacre Heat Charm Chrono SalonG Journey
namespace Hills
variable (a₀ a:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:∀ a:Axis,Repertory Y h W' R a)
variable (p:Actors Y h a₀ W' R (A a₀))(α:p.val.X)
local notation "F"=> Camera Y h a W' R (A a)
local notation "P₀"=>issueH Y h s a₀ W' R (A a₀) p α
local notation "H₁"=>route Y h s a W' R (A a)
local notation "U1"=> (StructureH Y h a W' R (A a)).Unity
local notation "M" i:max d:max f:max p:max=> Wedge Y h i a d W' R (A a) f p
variable {f:W (tent Y h)}(x:Decko Y h a)
-- effective phase splitting needs RP also at ODD-tick half planes whose ticks do not become integer by L. use promotion headroom. details Occasion.
private lemma margin_add {D w J e:ℕ} {L:Side} (t:Margin L D w J e)(h:3≤ L.val): e+1+L.val*gross D w J ≤ L.val*e:=by
 have he: beforePad D≤r₁ L D:= by unfold r₁ beforePad; nlinarith
 unfold Margin r₃ at t; unfold gross; nlinarith
lemma true_advance (z:ℤ)(u:Ahead a z (reserve Λ l) S): Ahead a ((Λ.R.L.val:ℤ)*z+1) (reserve Λ l) (GridStep Λ l S):=by
 intro y v; obtain ⟨t,hx,v⟩:=mem_biUnion.mp v; obtain ⟨k,hv,rfl⟩:=mem_image.mp hx; obtain ⟨t,e,rfl⟩:=mem_image.mp v; specialize u k hv
 let d:=gross (aliasLaw Λ) (distanceLaw l) Λ.R.J; let ℓ:= Λ.R.L.val; let r:=reserve Λ l; have he: -(↑(ℓ*d):ℤ) ≤ t a:= (box_test.mp e).1 a; have hp:(reserve Λ l:ℤ)+1+(↑(ℓ*d):ℤ) ≤ (ℓ:ℤ)*(reserve Λ l:ℤ):= by exact_mod_cast (margin_add (Journey.prepared Λ l) Λ.R.coarse)
 rw [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul]; change (ℓ:ℤ)*z+_+_≤_+(ℓ:ℤ)*_; nlinarith
lemma terrace_ahead (z:ℤ)(u:Ahead a z (reserve Λ l) S): Ahead a ((Λ.R.L.val:ℤ)^n*z + n) (reserve Λ l) (seriesQ Λ l S n) := by
 induction n with
 | zero=> rw [pow_zero,one_mul]; exact Ahead.subh _ _ (by omega) u
 | succ n ih=> apply Ahead.subh (seriesQ Λ l S (n+1)) a _ (true_advance (seriesQ Λ l S n) a _ ih); rw [pow_succ', Nat.cast_succ]; have he:3≤ Λ.R.L.val:=Λ.R.coarse; nlinarith

include A p α
variable {g:W (tent Y h)}(z:ℤ)
local notation "η"=> reserve Λ l
local notation "Z" n:max=> seriesQ Λ l S n
local notation "σ"=> gaugeShift Λ.block z
local notation "X" k:max=> issueH Y h k a₀ W' R (A a₀) p α
local notation "K"=> tic Kₜ
lemma wagonPlane (u:Ahead a (gaugeShift Λ.block z) (reserve Λ l) S)(e:Locator Kₜ f S):
   ascended Y h s W' R n (Fold Kₜ a (gaugeShift Λ.block z) f f) = Fold Kₜ a ((Λ.R.L.val:ℤ)^n* (gaugeShift Λ.block z)) (ascended Y h s W' R n f) (ascended Y h s W' R n f):=by
 induction n with
 | zero=> rw [pow_zero,one_mul]; rfl
 | succ n ih=>
    let V:= (Λ.R.L.val:ℤ); let z':= V^n*σ; let g:= ascended Y h s W' R n f; have hx:= ascend_loc Y h S s n f e W' R; have he:= Ahead.subh (Z n) a (show V^n*σ≤ _ from (by omega : V^n*σ≤ V^n*σ+n)) (terrace_ahead (Λ:=Λ) S a n _ u);
    change Charm.next Y h (s+n) W' R (ascended Y h s W' R n _)= Fold Kₜ a (V^(n+1)*_) _ _; rw [ih]; unfold Fold; rw [Charm.separate Y h (refract a z' (Z n)) (Z n) (s+n) W' R (locate_cold Kₜ (Z n) a z' hx) hx (ahead_split _ _ a z' he he), next_mir, pow_succ',mul_assoc]; rfl
lemma vote_up (x:W (tent Y h)): issueH Y h s a₀ W' R (A a₀) p α x = issueH Y h (s+n) a₀ W' R (A a₀) p α (ascended Y h s W' R n x):=by
 induction n with
 | zero=> rfl
 | succ n ih=> rw [ascended,LinearMap.comp_apply]; exact ih.trans (vote_stay Y h (s+n) a₀ W' R (A a₀) _ _ _).symm -- args
lemma vote_adaptive (u:Ahead a (σ + (tic Kₜ:ℤ)) (reserve Λ l) S)(e:Locator Kₜ f S):
   0 ≤ issueH Y h s a₀ W' R (A a₀) p α (Fold Kₜ a (gaugeShift Λ.block z) f f):=by
 -- choose t'≥(z+1)/2.First op.Jeed. y=clock(−d), shift to after0. Δ gap=2d−z. helve τδ y? compute Fold_z (τd y)= fire_z(τd y) τd y= τ(z−d) fire0 y * τd y. translate down by z−d yields θ0 y *(shift 2d-z y). step.Physical.
 let d:ℤ:=(z+1)/2; have hv:z≤2*d∧2*d≤z+1:=by unfold d; omega
 let y:= clockW Kₜ a (-d) f; let S':= hour Kₜ S a (-d)
 have hf:f=clockW Kₜ a d y:= by unfold y; rw [clock_add,add_neg_cancel,tic_zero]
 have hx :0≤ σ + (tic Kₜ:ℤ) +(tic Kₜ:ℤ)*(-d):= by
    have he:= tick_tock Kₜ z; change 2*σ= _ at he; nlinarith
 have ht:= Ahead.subh S' a hx (flightW Kₜ S a _ (-d) u)
 let x:Decko Y h a:= ⟨y, ⟨S',ht,loc_tic Kₜ S a _ e⟩⟩
 let n:=(2*d-z).toNat; have he : 0≤ 2*d-z:= sub_nonneg.mpr hv.1
 have hh:Fold Kₜ a σ f f= clockW Kₜ a (z-d) (helve Kₜ a x.val (clockW Kₜ a n y)):=by
    conv_lhs=>rw [hf]
    unfold Fold helve; rw [clock_neg,show fire Kₜ a σ y=clockW Kₜ a z (fire Kₜ a 0 y) from (by unfold clockW; rw [burning_ice]; rfl), clock_add, clock_mul,clock_add Kₜ a (z-d) (n:ℤ) y, show -d+z=z-d from by ring,Int.toNat_of_nonneg he, show z-d+(2*d-z)=d from by omega]
 rw [hh, vote_shift]; exact (step_selected Y h s a₀ a n W' R A p α x (Nat.zero_le _)).1
lemma floorPhase (u: Ahead a (gaugeShift Λ.block z) (reserve Λ l) S)(e: Locator Kₜ f S): 0 ≤ issueH Y h s a₀ W' R (A a₀) p α (Fold Kₜ a (gaugeShift Λ.block z) f f):=by
 let n:= tic Kₜ; have ht: (Λ.R.L.val:ℤ)^n*σ=gaugeShift Λ.block ((Λ.R.L.val:ℤ)^n*z):=by unfold gaugeShift; ring
 rw [vote_up Y h s a₀ n W' R A p α,wagonPlane Y h S s a₀ a n W' R A p α _ u e,ht]
 exact vote_adaptive Y h (Z n) (s+n) a₀ a W' R A p α _ (ht ▸ terrace_ahead S a n _ u) (ascend_loc Y h S s n f e W' R)
#print axioms floorPhase
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
