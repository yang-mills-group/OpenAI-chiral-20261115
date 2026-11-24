import YM.SU5.FiniteGaugeData.Hills.Domicile
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
include S'
local notation "X"=> Theater Kₜ
local notation "K₁"=> Kₜ
local notation "T₁"=> Motif Kₜ
local notation "η"=> reserve Λ l
local notation "σ" k:max=>frameQ Λ z k
-- prefix transport also for selected.Steps.
variable (m:Motif (tent Y h)) (x y:Theater (tent Y h))
omit S'
local notation "τ" n:max=> Show.collapse Y h n W' R
lemma lineal (p:Arrive Y h x s): Show.collapse Y h (s+1) W' R x= Charm.next Y h s W' R (Show.collapse Y h s W' R x):=by
 change _= (SalonG.companion Y h s W' R) _; unfold Show.collapse; rw [fills,fills,map_sum]; refine sum_congr rfl fun i t=>?_ ; rw [preRoll, p i t _ (by omega),mul_one,map_smul]; rfl
lemma behind_t (x:Motif (tent Y h))(p:Ends Kₜ x s): preRoll Y h W' R x (s+1)= Charm.next Y h s W' R (preRoll Y h W' R x s):=by rw [preRoll,p _ (by omega),mul_one]
private lemma plow (p:Arrive Y h x s)(v:s ≤ i): Arrive Y h x i:= fun m a=> ends_mono Y h s i m (p m a) v
-- actual expression since horizon eventually stable even when not on half
include S'
variable (Φ) in
def solo (s:ℕ) (m:Motif (tent Y h)): ℂ:= Φ s (preRoll Y h W' R m s) -- include S'? def section if not referenced
#check solo
lemma solstice (p:Ends Kₜ m s)(t:s ≤ i): solo Y h W' R Φ i m=solo Y h W' R Φ s m:=by induction i,t using Nat.le_induction with
 | base=> rfl
 | succ i t ih=>rw [← ih,solo,solo,behind_t Y h i W' R m (ends_mono Y h s i m p t),S'.cohere]
variable (Φ) in
def stamp (m:Motif (tent Y h)) := let i:= (ends_exists Kₜ m).choose; Φ i (preRoll Y h W' R m i)
lemma stamp_w (p:Ends Kₜ m s) : stamp Y h W' R Φ m=Φ s (preRoll Y h W' R m s):=by
 let i:= (ends_exists Kₜ m).choose; exact (solstice Y h i (s+i) W' R A S' m (ends_exists Kₜ m).choose_spec (by omega)).symm.trans (solstice Y h s (s+i) W' R A S' m p (by omega))
variable (Φ) in
def anthem : Theater (tent Y h)→ₗ[ℂ]ℂ:=fill Kₜ (stamp Y h W' R Φ)
lemma anthemAt (p:Arrive Y h x s): anthem Y h W' R Φ x=Φ s (Show.collapse Y h s W' R x):=by
 unfold anthem Show.collapse; rw [fills,fills,map_sum]; apply sum_congr rfl fun i f=> ?_; rw [map_smul,stamp_w Y h s W' R A S' i (p i f)]
lemma echo_dec (x y:Theater (tent Y h))(p:x∈ Half Y h a z)(v:y∈ Half Y h a z)(b:Arrive Y h x s)(t: Arrive Y h y s):
 anthem Y h W' R Φ ((intermezzo Kₜ a (frameQ Λ z) x)*y)= Φ s (fire Kₜ a (frameQ Λ z s) (Show.collapse Y h s W' R x)*Show.collapse Y h s W' R y):=by
 -- adaptation.Show.foyer; natural because P intertwines already.
 let C:= intermezzo Kₜ a (frameQ Λ z); let B:= freezing Y h a (σ s); let D(i:T₁):= preRoll Y h W' R i s
 change anthem Y h W' R Φ (C x*y) = Φ s (B _*_)
 let T':= anthem Y h W' R Φ
 have hx(i k:T₁)(m:i∈ x.coeff.support)(z':k∈ y.coeff.support)(c d:ℂ) : T' (C (MonoidAlgebra.single i c)*MonoidAlgebra.single k d)= Φ s ((B (c • D i))*(d • D k)):=by
   have V:Alone Y h a z i:= (Show.active_iff ..).mp p _ m
   have H:Alone Y h a z k:=(Show.active_iff ..).mp v _ z'
   have he:Ends Kₜ ((opus Kₜ a (frameQ Λ z) i)*k) s:= ends_mul Kₜ (ends_cold Kₜ a _ _ (b i m)) (t k z'); unfold T' C anthem; rw [moment_one,MonoidAlgebra.single_mul_single,fill_mode, stamp_w Y h s W' R A S' _ he,replay Y h s W' R k a z i V H]
   change ((star c)*d) • (Φ s (B (D i)*D k)) = _; rw [map_smulₛₗ (f:=B), Algebra.smul_mul_assoc,Algebra.mul_smul_comm,map_smul,map_smul,smul_smul]; rfl
 unfold Show.collapse; rw [fills,fills,map_sum,sum_mul]
 conv_lhs=> rw [←pick_all Kₜ x,←pick_all Kₜ y,map_sum,sum_mul]
 simp_rw [mul_sum,map_sum]; exact sum_congr rfl fun i h=> sum_congr rfl fun k t=> hx i k h t _ _

lemma lease_one : anthem Y h W' R Φ 1=1:=by unfold anthem; rw [MonoidAlgebra.one_def,fill_mode,one_smul,stamp_w Y h 0 W' R A S' _ (fun _ _=>rfl)]; exact S'.living 0
lemma lease_cons (hQ:x∈Half Y h a z) : 0 ≤ anthem Y h W' R Φ ((intermezzo K₁ a (frameQ Λ z) x)*x):=by -- shadow h
 obtain ⟨i,v⟩:= (arrived Y h x).exists; rw [echo_dec Y h i W' R A S' a z x x hQ hQ v v]; let b:= frameQ Λ z i; let y:= Show.collapse Y h i W' R x
 have hp : ∃ t:Finset Cover,Ahead a (frameQ Λ z i) η t∧ Locator (tent Y h) y t:= by unfold y Show.collapse; rw [fills]; exact port_union Y h a _ _ _ fun j p=> located Y h i W' R j a z ((Show.active_iff ..).1 hQ _ p)
 obtain ⟨T,u,q⟩:= hp; rw [frame_cash] at u ⊢; exact S'.expo i a _ T y q u
omit S'
local notation "V" s:max => Playlist.Show.Vect Y h a s
variable (Φ)
def contractX (y z': Theater (tent Y h)): ℂ := anthem Y h W' R Φ (intermezzo Kₜ a (frameQ Λ z) y * z')
local notation "ψ"=> contractX Y h W' R Φ a z -- order Φ binder before a
set_option linter.unusedVariables false in
def coordinate : Vect Y h a z →ₗ⋆[ℂ] (Vect Y h a z →ₗ[ℂ] ℂ) where
 toFun x:={ toFun y:=contractX Y h W' R Φ a z x.val y.val
            map_add' f g:= (by unfold contractX; rw [Subalgebra.coe_add,mul_add,map_add])
            map_smul' c f:=(by unfold contractX; rw [Subalgebra.coe_smul,Algebra.mul_smul_comm,map_smul]; rfl) }
 map_add' f g:= LinearMap.ext (fun y=>by change ψ (f+g).val y.val= ψ f.val _+ψ g.val _; unfold contractX; rw [Subalgebra.coe_add,map_add, add_mul,map_add])
 map_smul' c f:= LinearMap.ext (fun y=>by change ψ (c • f).val y.val=star c • ψ f.val _; unfold contractX; rw [Subalgebra.coe_smul,inter_scale,Algebra.smul_mul_assoc,map_smul])
variable {Φ}
include S'
lemma coords (x:Vect Y h a z) : 0 ≤ coordinate Y h W' R Φ a z x x:= lease_cons Y h W' R A S' a z x.val x.property
lemma contracts (v w:Vect Y h a 0)(e:Arrive Y h v.val s)(t:Arrive Y h w.val s): coordinate Y h W' R Φ a 0 v w=Φ s (helve Kₜ a (days Y h s W' R a v).val (days Y h s W' R a w).val):=by change anthem Y h W' R Φ _= _; rw [echo_dec Y h s W' R A S' a 0 _ _ v.property w.property e t, frame_b]; rfl
lemma granule (x:Charm.W (tent Y h)) : anthem Y h W' R Φ (credit_at Y h s x)=Φ s x:=by rw [anthemAt Y h s W' R A S' _ (pulse_arr Y h s x)]; unfold credit_at Show.collapse flow; rw [fill_mode,one_smul,pulse_full]
-- barycenter full mixed un-thinned.Focal.
omit S'
include A
lemma former : anthem Y h W' R (actual Y h W') x=chorusRead Y h W' R x:=by obtain ⟨i,v⟩:= (arrived Y h x).exists; rw [anthemAt Y h i W' R A (unanimous Y h W' R A) x v,ties Y h i W' R x v]; rfl
variable (p:Actors Y h a W' R (A a))
lemma portraiture : Continuous (fun α:p.val.X=> anthem Y h W' R (coronet Y h a W' R A p α) x):=by
 obtain ⟨i,v⟩:= (arrived Y h x).exists; simp_rw [anthemAt Y h i W' R A (sphere Y h a W' R A p _) x v]; exact vote_civil Y h i a W' R (A a) _ p -- param order
lemma portray : ∫ (α:p.val.X), anthem Y h W' R (coronet Y h a W' R A p α) x ∂ p.val.μ=chorusRead Y h W' R x:=by obtain ⟨i,v⟩:=(arrived Y h x).exists; simp_rw [anthemAt Y h i W' R A (sphere Y h a W' R A p _) x v]; rw [ties Y h i W' R x v]; exact vote_pearl ..
#print axioms lease_cons
#print axioms portray
end KernelP
end YM.CF.Buffered.Afterglow.Hierarchy
