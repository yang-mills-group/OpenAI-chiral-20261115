import YM.SU5.FiniteGaugeData.Hills.Acme
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
section calculus
variable {H:Hilbert}(x:H.Op)(u:H)
lemma money_R : 0 ≤ inner ℂ u u:= by rw [inner_self_eq_norm_sq_to_K]; change 0≤ (↑‖u‖:ℂ)^2; rw [← Complex.ofReal_pow]; exact ⟨sq_nonneg _,rfl⟩
lemma moneyP (p:0≤x) :0 ≤ inner ℂ u (x u):= by
 have hp:= (ContinuousLinearMap.nonneg_iff_isPositive x).1 p
 exact hp.inner_nonneg_right _ -- lemma inspect
lemma moneyB (v:H) : inner ℂ v v ≤ inner ℂ u u ↔ ‖v‖ ≤ ‖u‖:= by
 rw [Complex.le_def]; have h(z:H): (inner ℂ z z).im=0:= ((Complex.le_def.mp (money_R z)).2).symm; rw [h,h]; suffices he:(inner ℂ v v).re ≤ (inner ℂ u u).re ↔ ‖v‖≤‖u‖ from by simpa only [and_true,min_self, le_refl] using he
 rw [show (inner ℂ v v).re=‖v‖^2 from (inner_self_eq_norm_sq (𝕜:=ℂ) v), show (inner ℂ u u).re=‖u‖^2 from (inner_self_eq_norm_sq (𝕜:=ℂ) u),sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
lemma moneyA (v:H)(B:ℝ)(b:0≤ B)(e:‖u‖ ≤ B*‖v‖): 0 ≤ ((B:ℂ)^2 • inner ℂ v v-inner ℂ u u) := by
 apply sub_nonneg.mpr
 have he: ‖u‖≤ ‖(B:ℂ) • v‖:= by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg b]; exact e
 have hz:= (moneyB ((B:ℂ) • v) u).2 he; rw [inner_smul_left,inner_smul_right, Complex.conj_ofReal,← mul_assoc] at hz; exact le_trans hz (le_of_eq (by rw [smul_eq_mul,sq]))
end calculus
variable (a₀:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:∀ a:Axis,Repertory Y h W' R a)
variable (p:Actors Y h a₀ W' R (A a₀))(α:p.val.X)
local notation "F" a:max=> Camera Y h a W' R (A a)
local notation "P₀"=>issueH Y h s a₀ W' R (A a₀) p α
local notation "X" a:max=> route Y h s a W' R (A a)
-- vector approximation ℂ supports.
variable (f:W (tent Y h))(a b:Axis)
include A p α
-- compact core lemma.Conge.Nothing assumed. frame.Omega closeness localized mark selected only.Huge times preserved.LocalMany later. Using closeness for P0 f (not product under scale from projection).
lemma phase_property {Q:Set ℂ}(e:IsClosed Q)(t:∀ x:Camera Y h a W' R (A a), ‖x‖=1→ inner ℂ x ((route Y h s a W' R (A a) f) x)∈Q): issueH Y h s a₀ W' R (A a₀) p α f∈Q:= by
 classical
 apply e.closure_subset; refine Metric.mem_closure_iff.mpr fun ε u=> ?_
 let f':= readingH Y h s a₀ W' R (A a₀) f
 obtain ⟨x,r,w⟩:= coneB p.property α (ε/2) (by positivity) {f'} (faith Y h a₀ W' R (A a₀)); let g:= inner ℂ x ((X a₀) f x); have hx:dist (issueH Y h s a₀ W' R (A a₀) p α f) g<ε:= by rw [dist_comm,dist_eq_norm]; exact (w _ (mem_singleton_self f')).trans_lt (by linarith)
 refine ⟨g,?_,hx⟩; by_cases h':a=a₀
 · subst a; exact t _ r
 let U:= flowsH Y h a₀ a W' R (A a₀) (A a) (Ne.symm h'); have he: inner ℂ (U x) ((X a) f (U x))=g:= by unfold U; rw [←flows_m,LinearIsometryEquiv.inner_map_map]
 exact he ▸ t (U x) ((U.norm_map x).trans r)
lemma vote_shift (z:ℤ): issueH Y h s a₀ W' R (A a₀) p α (clockW Kₜ a z f)=(P₀) f:=by simp_rw [vote_real]; exact congrArg (p.val.character α) (Subtype.ext (stayP ..))
lemma vote_ref (z:ℤ): issueH Y h s a₀ W' R (A a₀) p α (fire Kₜ a (gaugeShift Λ.block z) f)= star ((P₀) f):=by
 have hp:fire Kₜ a (gaugeShift Λ.block z) f= clockW Kₜ a z (fire Kₜ a 0 f):=by unfold clockW; rw [burning_ice]; rfl
 rw [hp, vote_shift]; by_cases h':a₀=a
 · subst a; exact vote_star ..
 simp_rw [vote_real]; exact (show _ = p.val.character α (star (readingH Y h s a₀ W' R (A a₀) f)) from congrArg (p.val.character α) (Subtype.ext (reflects_x Y h s a₀ a W' R (A a₀) (A a) h' f))).trans (map_star ..)
-- matrix entry on Camera any Plan y.Basis from x.
omit p α
variable (t:Plan Y h a d f)(q:0<d)
local notation "U"=> (StructureH Y h a W' R (A a)).Unity
local notation "B" i:max z:max u:max=> Wedge Y h s a i W' R (A a) z u
local notation "M"=> Wedge Y h s a d W' R (A a) t q
-- Waw.Cast Gram. for different d positive. important.
include t q
lemma plate_gram (g:W (tent Y h))(p:Plan Y h a n g)(b:0<n):
 route Y h s a W' R (A a) (helve Kₜ a f g)= social ((StructureH Y h a W' R (A a)).Unity) (star (Wedge Y h s a d W' R (A a) t q)* Wedge Y h s a n W' R (A a) p b):= by
 let v:=Plan.other Y h t; let w:=couplePlan Y h a d n v p; rw [← stayP Y h s a a W' R (A a) _ d,helve, clock_mul,freezing_tides]; change (X a) (Swing ..) = _; rw [route_formula Y h s a _ W' R (A a) w (by omega),wedge_star Y h s a d W' R (A a) t q,←wedge_glues Y h s a d n W' R (A a) v q p w b] -- args order.Y 
lemma plate_score (x:F a)(g:W (tent Y h))(p:Plan Y h a n g)(b:0<n): inner ℂ x ((X a) (helve Kₜ a f g) x)= inner ℂ (Wedge Y h s a d W' R (A a) t q (cpo (U) x)) (Wedge Y h s a n W' R (A a) p b (cpo (U) x)):= by
 rw [plate_gram Y h s d n W' R A f a t q g p b] -- inspect
 rw [sightS,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
omit t q
-- positivity from every aspect. Also time T at Step selfadj and upper
include p α
lemma fragment (x:Decko Y h a): 0 ≤ issueH Y h s a₀ W' R (A a₀) p α (helve Kₜ a x.val x.val):=by
 obtain ⟨S,r,v⟩:=x.property; obtain ⟨d,q,t⟩:= resident Y h S a _ r v; apply phase_property Y h s a₀ W' R A p α (helve Kₜ a x.val x.val) a isClosed_Ici; intro y c; change 0 ≤ inner ℂ _ _; rw [plate_score Y h s d d W' R A x.val a t q y _ t q]; exact money_R ..
#print axioms phase_property
#print axioms plate_score
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
