import YM.SU5.FiniteGaugeData.Hills.Occasion
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
-- scenario in same hierarchy (attached to the Voxel W',R, for assembly in Client)
variable (Φ:ℕ→ Charm.W (tent Y h) →ₗ[ℂ] ℂ) (K:Calibration)
structure Sphere (A:∀ a:Axis,Repertory Y h W' R a) (Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ):Prop where
 living (s:ℕ) : Φ s 1=1
 cohere (s:ℕ) (f:W (tent Y h)): Φ (s+1) (Charm.next Y h s W' R f)=Φ s f
 color (s:ℕ)(a:Axis)(x:W (tent Y h))(z:ℤ): Φ s (clockW Kₜ a z x)=Φ s x
 mirror (s:ℕ) (a:Axis)(z:ℤ)(x:W (tent Y h)): Φ s (fire Kₜ a (Heat.gaugeShift Λ.block z) x)= star (Φ s x)
 expo (s:ℕ)(a:Axis)(z:ℤ)(S:Finset Cover)(x:W (tent Y h)): Locator Kₜ x S→ Ahead a (Heat.gaugeShift Λ.block z) (reserve Λ l) S→
    0 ≤ Φ s (Fold Kₜ a (Heat.gaugeShift Λ.block z) x x)
 hardy (s:ℕ)(a:Axis)(x:Decko Y h a)(n:ℕ): 0 ≤ Φ s (helve Kₜ a x.val (vectorT Y h a x n).val) ∧ Φ s (helve Kₜ a (vectorT Y h a x n).val (vectorT Y h a x n).val) ≤ Φ s (helve Kₜ a x.val x.val)
 spread (s:ℕ)(a:Axis)(d:ℕ)(x:Decko Y h a)(f:Charm.W (tent Y h))(t:Plan Y h a d f)(c:0<d):
    let y:= embark Y h a d t x; let B:ℂ:= (↑‖Wedge Y h s a d W' R (A a) t c‖:ℂ)^2
    Φ s (helve Kₜ a y.val y.val)≤ B • Φ s (helve Kₜ a x.val x.val)
 stamp (s:ℕ) (x:W Kₜ)(a:Axis): ‖Φ s x‖≤ ‖route Y h s a W' R (A a) x‖
include W' R A p α
lemma issue_price (x:W (tent Y h))(a:Axis) : ‖issueH Y h s a₀ W' R (A a₀) p α x‖≤ ‖route Y h s a W' R (A a) x‖:= by
 apply phase_property Y h s a₀ W' R A p α x a (Q:= {z:ℂ| ‖z‖≤‖route Y h s a W' R (A a) x‖}) (isClosed_le continuous_norm continuous_const)
 intro y e; let M':= route Y h s a W' R (A a) x; change ‖inner ℂ y (M' y)‖≤_; exact (norm_inner_le_norm ..).trans ((mul_le_mul_of_nonneg_left (M'.le_opNorm y) (norm_nonneg _)).trans_eq (by rw [e,one_mul,mul_one]))
abbrev coronet (α:p.val.X) : ℕ→ W (tent Y h) →ₗ[ℂ]ℂ:= fun s=> issueH Y h s a₀ W' R (A a₀) p α
lemma sphere : Sphere Y h W' R A (coronet Y h a₀ W' R A p α):= by
 refine ⟨fun i=> vote_one .., fun s x=>vote_stay ..,fun s a x z=> vote_shift Y h s a₀ W' R A p α x a z, fun s a z x=> vote_ref Y h s a₀ W' R A p α x a z, fun s a z S x t v=> floorPhase Y h S s a₀ a W' R A p α z v t,fun s a x n=> step_selected Y h s a₀ a n W' R A p α x (by omega),fun s a d x f p_ u=> lease_selected ..,fun s x a=>issue_price Y h s a₀ W' R A p α x a⟩
#print axioms sphere
omit p α
abbrev actual : ℕ→ W (tent Y h) →ₗ[ℂ]ℂ:= fun s=> Playlist.Show.sight Y h s W'
lemma actual_money (x:W (tent Y h)): actual Y h W' s x= E s x.val:=rfl
-- show unselected meets too.Easier as barycenter of p.Sphere.Cross
lemma old_stamp (x:W (tent Y h)) (a:Axis): ‖E s x.val‖ ≤ ‖route Y h s a W' R (A a) x‖:= by rw [← orbit_value Y h s a W' R (A a) x]; let T':= route Y h s a W' R (A a) x; let g:= orbitSeed Y h a W' R (A a); exact (norm_inner_le_norm (𝕜:=ℂ) g (T' g)).trans ((mul_le_mul_of_nonneg_left (T'.le_opNorm g) (norm_nonneg _)).trans_eq (by unfold g; rw [orbit_norm,one_mul,mul_one]))
-- can prove without p entirely.Actors
lemma unanimous : Sphere Y h W' R A (actual Y h W') := by
 -- expo direct.E. Others star comes from routing ANY.Za. Hardy.Chrono time positivity.W. lease from actual.
 refine ⟨fun s=> (W'.gaugeMatter s).1, fun s x=> foundation Y h s W' R x, fun s a x z=> invariantW Y h s a z W' x, ?_,?_,?_,?_,fun s x a=> old_stamp Y h s W' R A x a⟩
 · intro s a z f
   have he:fire Kₜ a (Heat.gaugeShift Λ.block z) f=clockW Kₜ a z (fire Kₜ a 0 f):=by unfold clockW; rw [burning_ice]; rfl
   change E s _=star (E s _); rw [he,invariantW Y h s a _ W',← orbit_value Y h s a W' R (A a) _,route_mirror,←orbit_value Y h s a W' R (A a) f,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]; exact (inner_conj_symm ..).symm
 · intro s a z S x t v; exact ahead_positive Y h S s W' a z x.val t v
 · intro s a x n
   change 0≤ E s _∧ E s _≤ E s _; let y:= vectorT Y h a x n; rw [←lawStore Y h s W' R a (A a) x y, ←lawStore Y h s W' R a (A a) y y,←lawStore Y h s W' R a (A a) x x]; exact ⟨disperses Y h s W' R a (A a) x ↑n (by positivity), (moneyB _ _).2 (time_contr Y h s W' R a (A a) x n)⟩
 intro s a d x f t c y B₁; change E s _≤ _ • E s _; rw [←lawStore Y h s W' R a (A a) x x, ← lawStore Y h s W' R a (A a) y y]; let T' := Wedge Y h s a d W' R (A a) t c; apply sub_nonneg.mp; unfold y; rw [← wedge_here Y h s a d W' R (A a) t x c]; exact moneyA _ _ ‖T'‖ (norm_nonneg T') (T'.le_opNorm _)
#print axioms unanimous
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
