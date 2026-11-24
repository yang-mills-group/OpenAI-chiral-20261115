import YM.SU5.FiniteGaugeData.Chrono.Valise
import YM.SU5.FiniteGaugeData.Mirage.Acre
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
variable {v u:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
namespace Chrono
open Nacre Heat Charm Playlist Show
variable (R:Universal Y h u v I E)(L:Rolled Y h u v J P)(a j:Axis)
local notation "η"=> reserve Λ l
open Quest Quest.Chaperone
local notation "a₀"=> (3:Axis)
open scoped NNReal
variable (A:Repertory Y h R L 3)
local notation "H"=> A.space
local notation "K"=> Kₜ
local notation "F'" i:max=>store Y h i R L a₀ A
local notation "T₀"=>tempo_aux Y h R L a₀ A
local notation "Ω"=>goldStar Y h R L a₀ A
variable {σ τ: Window.Family}{Z:Finset (Face ℤ)}{X:Family (tent Y h)}(c:BeamPel Y h (E s) σ τ T S Z X)
variable (g:Ahead 3 0 (reserve Λ l) S)(u':Ahead 3 0 (reserve Λ l) (refract 3 0 T))
def beatific : Decko Y h 3 := ⟨⟨X,c.glow.fits⟩, S,g,c.glow.funds.widen⟩
def variance (z:ℂ) : Decko Y h 3:= beatific Y h S T s c g - z • 1 -- include E implicit
variable (y:Decko Y h 3)
local notation "M"=> variance Y h S T s c g
lemma centered_ch (z:ℂ) : ((variance Y h S T s c g z).val.val)= Quest.centeredF Kₜ X z:=rfl
lemma nectar_unit : inner ℂ (goldStar Y h R L 3 A) ((F' s) y)= E s y.val.val:=by
 rw [← seed_gold Y h s R L a₀ A,lawStore]; change E s (helve Kₜ a₀ 1 _).val= _; rw [helve, ice_central,one_mul]
lemma beam_tune : inner ℂ (Ω) ((F' s) (beatific Y h S T s c g))≠0:= by rw [nectar_unit]; exact c.warm
include c u'
lemma brush_signal : 0 < inner ℂ ((F' s) ((M) (E s X))) ((F' s) ((M) (E s X))) ∧ inner ℂ Ω ((F' s) ((M) (E s X)))=0:=by
 rw [lawStore, nectar_unit]; refine ⟨(Chaperone.BeamPel.lives Y h R L c u' g).2, ?_⟩
 let O:=sight Y h s R; change O (((M) (E s X)).val)= 0
 have he: O 1=1:=(R.gaugeMatter s).1; unfold variance; rw [Subalgebra.coe_sub, map_sub, Subalgebra.coe_smul, map_smul, show (1:Decko Y h 3).val=(1:W K) from rfl, he]; change E s X- (E s X)•(1:ℂ)=0; simp
omit c u' in
private lemma beam_nonneg (w:H)(p:w≠0)(t:ℝ≥0): 0 < inner ℂ w (rail Y h R L 3 A t w):=by
 let S:= tempo_aux Y h R L 3 A; let u:= rail Y h R L 3 A (t/2) w
 have he: u≠0:= fun h=> p (injectRail Y _ R L 3 A _ _ h)
 have hz:inner ℂ w (rail Y h R L 3 A t w)=inner ℂ u u:=by
    rw [show rail Y h R L 3 A t w= S.E (t/2) u from ?_, ← S.swing]; swap
    · rw [show S.E (t/2) u = S.E (t/2+t/2) w from ?_,add_halves]; rfl -- nested
      rw [S.time]; rfl
    rfl
 rw [hz]; exact Complex.lt_def.mpr ⟨(re_inner_self_pos (𝕜:=ℂ)).mpr he,(inner_self_im (𝕜:=ℂ) u).symm⟩
lemma beam_delay (t:ℝ≥0): 0 < inner ℂ ((F' s) ((M) (E s X))) (rail Y h R L 3 A t ((F' s) ((M) (E s X)))):=beam_nonneg Y h R L A _ (fun e=> by have ht:=(brush_signal Y h S T s R L A c g u').1; rw [e,inner_zero_right] at ht; exact lt_irrefl _ ht) t
include A
lemma beam_far (i:ℕ): 0 < E s (helve K 3 ((variance Y h S T s c g (E s X)).val) ((vectorT Y h 3 ((M) (E s X)) i).val)).val:=by
 let x:= (M) (E s X); change 0< E s (helve Kₜ a₀ x.val _).val; have he:= beam_delay Y h S T s R L A c g u' (thetaX Λ s i); rw [rail_actual,clock_own,lawStore] at he; exact he
#print axioms beam_far
-- forensic errors for real time readings of this from Valise
end Chrono
end YM.CF.Buffered.Afterglow.Hierarchy
