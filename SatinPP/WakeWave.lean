import SatinPP.Counter
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 160000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six MacroGrid

open TopologicalSpace SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "G"=> P.ManyF 3 ξ
local notation "Γ"=> P.cartage 3 ξ
local notation "Θ"=> P.seasons 3 ξ
local notation "E"=> (Θ).E
local notation "κ"=> P.wealth 3 ξ
local notation "D%" s:max=>P.lengthP s
local notation "F%" s:max=> P.pointEra s
variable (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))

local notation "ℒ"=>Lead.Clan

open DoseTravel Set

variable (w:ℒ→Prism)(b:Bool)(q:ℝ)
def trails_LocalFieldBounds (a:ℒ)(p:Vantage):G:=Γ p (P.profilesZ x V w a (morning b q p))
local notation "τ"=>P.trails_LocalFieldBounds x V w b q
def wave (F:SampleDose)(a:ℒ):G:=DoseTravel.beam (G) F (P.trails_LocalFieldBounds x V w b q a)
variable {Y:ℕ→ P.Apron}{f n:ℕ}(R: GalaxyShow P x f n Y V)
include R
lemma trails_c(q₀:0<q)(a:ℒ):Continuous (τ a):=by
 have h:=P.profile_solid x f n V w q R q₀ a
 cases b; exact h.1; exact h.2
omit R
variable (m:ℒ→ℂ)
local notation "v"=> ounce m (P.cotillon x V w q)
abbrev lakelet(p:Vantage):G:=ounce m fun a=> P.trails_LocalFieldBounds x V w b q a p
local notation "L"=> P.lakelet x V w b q m
abbrev riseHour(b:Bool)(q:ℝ)(p:Vantage):= morning b q p-q
local notation "u"=> riseHour b q
include R
lemma lakelet_paves (q₀:0<q)(p:Vantage):
 L p=Γ p (E ((u p).toNNReal) v):=by
 rw [← ounces_map,← ounces_map]
 apply congrArg (ounce m); funext a
 unfold Function.comp trails_LocalFieldBounds cotillon riseHour
 apply congrArg (Γ p); exact P.profile_pos x f n V w R a _ _ q₀ (le_max_left q (dials b p))

lemma lake_c(q₀:0<q): Continuous (L):=by
 exact continuous_finsetSum _ fun a _=> (continuous_const (y:=m a)).smul (P.trails_c x V w b q R q₀ _)
lemma lake_contract (q₀:0<q)(p:Vantage):‖L p‖≤ ‖v‖:=by
 rw [P.lakelet_paves x V w b q R m q₀, P.cart_norm]
 exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((Θ).shrinks _))
lemma lake_y (q₀:0<q)(p y:Vantage): dist (L p) (Γ y (L p)) ≤ dist v (Γ y v):= by
 rw [P.lakelet_paves x V w b q R m q₀]
 let a:=E ((u p).toNNReal)
 rw [← ContinuousLinearMap.comp_apply (Γ y),← P.cart_paves, add_comm,P.cart_paves, ContinuousLinearMap.comp_apply,
    ←ContinuousLinearMap.comp_apply (Γ y),←P.travelers_temporal,ContinuousLinearMap.comp_apply]
 rw [dist_eq_norm,dist_eq_norm,←map_sub, P.cart_norm,←map_sub]
 exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((Θ).shrinks _))
omit R
lemma lake_horizontal (j:Axis)(h:j≠3)(t:ℝ)(p:Vantage):
 Γ (t • aglow j 1) (L (p-t • aglow j 1)) = L p:=by
 let y:=t • aglow j 1
 rw [lakelet,lakelet,←ounces_map]
 congr 1;funext a
 dsimp [trails_LocalFieldBounds]


 rw [←ContinuousLinearMap.comp_apply,←P.cart_paves, add_comm,sub_add_cancel]
 simp [morning,dials,aglow,Function.update, h.symm]

abbrev footfall(j:Axis):=aglow j 1
lemma footfall_bound(j:Axis):‖footfall j‖≤1:=by
 rw [pi_norm_le_iff_of_nonneg (by norm_num:(0:ℝ)≤1)]
 intro i;simp [footfall,aglow,Function.update];split_ifs <;>norm_num
include R
lemma wave_beam (q₀:0<q)(F:SampleDose):
 ounce m (P.wave x V w b q F)= DoseTravel.beam (G) F (L):=
 P.pull_beam_ounce x _ (P.trails_c x V w b q R q₀) _ _ 
lemma wave_bike (q₀:0<q)(F:SampleDose)(j:Axis)(e:j≠3)(t:ℝ) :
 ounce m (P.wave x V w b q (bike (footfall j) F t)) =
 t⁻¹ • (ounce m (P.wave x V w b q F) - Γ (t • footfall j) (ounce m (P.wave x V w b q F))):=by
 simp_rw [P.wave_beam x V w b q R m q₀]
 exact P.cycle_beam x _ (P.lake_c x V w b q R m q₀) F _ t (P.lake_horizontal x V w b q m j e t)


omit R
def Bolted(C:ℝ):Prop:=∀ (a:Vantage) {r:ℝ}(e:0<r){t h:ℝ},0<t → t≤h → h≤r → ∀ (p v':Vantage), ‖v'‖≤1 →
 |nick v' t p (pixel' a r e)-nick v' h p (pixel' a r e)| ≤ (C*(h/r^2))* (coverall a e).val p
structure CanMove (b:Bool)(F:SampleDose)(q r:ℝ)(e:0<r):Prop where
 pix:∃a,F=pixel' a r e
 wall(p:Vantage)(z:p∈tsupport F.val):q≤ dials b p
local notation "O"=> P.wave x V w b q
structure Flare (F:SampleDose)(d h z:ℝ) :Prop where
 swipe(m':ℒ→ℂ)(u':fanSet m'): (29/4)*h≤dist (ounce m' (O F)) (P.strideHeel x d h (ounce m' (O F)))
 spire(j:Axis)(j₀:j≠3)(t:ℝ)(e:0<t)(g:t≤d*z)(m':ℒ→ℂ)(u':fanSet m'):
    ‖ounce m' (O (bike (footfall j) F t))‖≤ (11/2)/d
 arch(m':ℒ→ℂ)(u':fanSet m'): 8*h≤dist (ounce m' (O F)) (P.strideHeel x d h (ounce m' (O F)))
 tranche(j:Axis)(j₀:j≠3)(t:ℝ)(e:0<t)(g:t≤d*z)(m':ℒ→ℂ)(u':fanSet m'):
    ‖ounce m' (O (bike (footfall j) F t))‖≤ (slack j+1/4)/d
 near:∃ a:Vantage, ∀(m':ℒ→ℂ)(u':fanSet m'), dist (ounce m' (O F)) (Γ a (ounce m' (P.cotillon x V w q))) ≤ h/8


include R
variable (a:Vantage) {r d δ M h ϵ z:ℝ} (e:0<r)(p':0<d)(g:0<δ)(y: dials b a=q+r)(s:r≤ 2*δ*d)
 (k:4*δ≤ ϵ)(q₀:0<q) (h':P.Surge x d M h ϵ z (ounce m (P.cotillon x V w q)))
include g p' y s k h' q₀
lemma wave_pin (p:Vantage)(t:p∈closedBall a r) :
 dist (L p) (Γ a v) ≤ h/8:=by
 let Y:=d⁻¹ • (p-a)
 let T:=(u p)/d
 have t':dist p a≤ r:= t
 have h₁: ‖Y‖ ≤ ϵ:=by
    unfold Y;rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity),←dist_eq_norm,←div_eq_inv_mul,div_le_iff₀ p']
    exact t'.trans (s.trans (mul_le_mul_of_nonneg_right (by linarith only [g,k]) p'.le))
 have B: q≤ morning b q p:=le_max_left ..
 have h₂: T≤ϵ:=by
    rw [show T=(max q (dials b p) - q) /d from rfl, div_le_iff₀ p',sub_le_iff_le_add,max_le_iff]; refine ⟨le_add_of_nonneg_left (mul_nonneg (by linarith only [k,g]) p'.le),?_⟩
    have v₂:=mul_le_mul_of_nonneg_right k p'.le
    linarith only [(abs_le.mp (good_face b a p)).2,y,s,t',v₂]
 have H:anklet P x d Y T= (Γ (p-a)).comp (E (u p).toNNReal):= by


    unfold Y T anklet strideHeel;rw [smul_smul,mul_inv_cancel₀ p'.ne',one_smul,mul_div_cancel₀ _ p'.ne']
 have w': (Γ a).comp (anklet P x d Y T)=(Γ p).comp (E (u p).toNNReal):=by
    rw [H, ← ContinuousLinearMap.comp_assoc,← P.cart_paves, add_comm,sub_add_cancel]
 rw [P.lakelet_paves x V w b q R m q₀, ← ContinuousLinearMap.comp_apply, ← w',ContinuousLinearMap.comp_apply,
    dist_comm,dist_eq_norm, ←map_sub,P.cart_norm, ← dist_eq_norm]
 exact h'.pin Y h₁ T (div_nonneg (sub_nonneg.mpr B) p'.le) h₂

lemma wave_h (e:0<r):
  8*h ≤ dist (ounce m (O (pixel' a r e))) (P.strideHeel x d h (ounce m (O (pixel' a r e)))):=by
 rw [P.wave_beam x V w b q R m q₀]
 let U:= P.strideHeel x d h
 have A:= bead (L) (pixel' a r e) (P.lake_c x V w b q R m q₀) (prescribed ..) (Γ a v) (fun p n'=>P.wave_pin x V w b q R m a p' g y s k q₀ h' p (show p∈closedBall a r from (DoseTravel.supported a (relative a r e)) ▸ n'))
 let ω:=DoseTravel.beam (G) (pixel' a r e) (L)
 let x':=Γ a v
 have Y:dist x' (U x')= dist v (U v):=by
    unfold x' U strideHeel
    rw [←ContinuousLinearMap.comp_apply, P.travelers_temporal, ContinuousLinearMap.comp_apply,dist_eq_norm,←map_sub,P.cart_norm,dist_eq_norm]

 change dist ω x'≤_ at A
 have B: (33/4)*h≤ dist x' (U x'):=Y.symm ▸ h'.whip
 have D:= (abs_le.mp (lipschitz (A:=U) ((Θ).shrinks _) x' ω)).2
 rw [dist_comm ω] at A <;> linarith only [D,A,B]
#print axioms wave_h

omit y k g s
lemma wave_zeal (j:Axis)(j₀:j≠3)(F:SampleDose)(f₀:F.Normalized)(l:0<z):
 ‖ounce m (O (bike (footfall j) F (d*z)))‖≤ (slack j)/d:=by
 rw [P.wave_bike x V w b q R m q₀ _ _ j₀,
    P.wave_beam x V w b q R m q₀, norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity:(0:ℝ)<(d*z)⁻¹),←dist_eq_norm]
 let A:=Γ ((d*z) • footfall j)
 have H:dist v (A v) ≤ slack j*z:=by
    convert h'.swish j j₀ using 1
    rw [spurHeel,aglow_line]
    unfold A footfall;rw [aglow_line,mul_one]
 apply (mul_le_mul_of_nonneg_left
    (bead_move (L) F (P.lake_c x V w b q R m q₀) f₀ A (fun p=>(P.lake_y x V w b q R m q₀ p _).trans H)) (by positivity)).trans_eq
 field_simp

include g e
lemma wave_stab
 {C:ℝ}(bol:Bolted C)(c:0<C)(l:0<z)(l₁:z≤δ)(l₂:C*z*M ≤ δ^2/4)
 (sr:δ*d ≤ r)(t:ℝ)(t₀:0<t)(u₀:t≤d*z)(j:Axis)(j₀:j≠3):
 ‖ounce m (O (bike (footfall j) (pixel' a r e) t))‖ ≤ (slack j+1/4)/d:=by
 let J:=footfall j
 let F:= pixel' a r e
 let Y(h':ℝ):=ounce m (O (bike J F h'))
 let D:=d*z
 have k': D≤r:=(le_trans (mul_le_mul_of_nonneg_left l₁ p'.le) (le_trans (mul_comm ..).le sr))
 have H:‖Y D‖ ≤ (slack j)/d:= P.wave_zeal x V w b q R m p' q₀ h' j j₀ F (prescribed ..) l
 have W:dist (Y t) (Y D) ≤ (C*(D/r^2))*M:=by
    unfold Y
    simp_rw [P.wave_beam x V w b q R m q₀]
    exact P.weigh_beams x (L) (P.lake_c x V w b q R m q₀) _ _ _ (cover_ok a e)
        (fun p=>(P.lake_contract x V w b q R m q₀ p).trans h'.cap)
        (fun p=>bol a e t₀ u₀ k' p J (footfall_bound _))
 rw [dist_eq_norm] at W
 apply ((norm_le_insert' (Y t) (Y D)).trans (add_le_add H W)).trans

 unfold D
 field_simp
 nlinarith only [mul_le_mul_of_nonneg_right l₂ (sq_nonneg d),pow_le_pow_left₀ (mul_nonneg g.le p'.le) sr 2]
omit h'
include s y k
lemma wave_paid
 {C:ℝ}(bol:Bolted C)(c:0<C)(l:0<z)(l₁:z≤δ)(l₂:C*z*M ≤ δ^2/4)
 (sr:δ*d ≤ r)
 (Q:∀ m,fanSet m→P.Surge x d M h ϵ z (ounce m (P.cotillon x V w q))):
 CanMove b (pixel' a r e) q r e ∧ P.Flare x V w b q (pixel' a r e) d h z:=by
 have ar(m:ℒ→ℂ)(h:fanSet m):= P.wave_h x V w b q R m a p' g y s k q₀ (Q _ h) e
 have st(j:Axis)(fj:j≠3)(h':ℝ)(t:0<h')(i:h'≤d*z)(m:ℒ→ℂ)(u':fanSet m):=P.wave_stab x V w b q R m a e p' g q₀ (Q _ u') bol c l l₁ l₂ sr h' t i j fj
 -- swipe weak requires h≥0, not local
 refine ⟨⟨⟨a,rfl⟩,?_⟩,⟨?_,?_,ar,st,a,?_⟩⟩
 · intro p t
   have r': p∈ closedBall a r:= (DoseTravel.supported a (relative a r e)) ▸ t
   linarith only [y,(abs_le.mp (good_face b a p)).1,mem_closedBall.mp r']
 · intro m hv₀
   rcases le_total h 0 with w₀|w₀
   · linarith only [w₀,show 0≤dist (ounce m (O (pixel' a r e))) (P.strideHeel x d h (ounce m (O (pixel' a r e)))) from dist_nonneg] -- placeholder
   linarith only [w₀,ar m hv₀]
 · intro j fj t p₂ p₃ m hv₀
   exact (st j fj t p₂ p₃ m hv₀).trans (div_le_div_of_nonneg_right (by linarith only [slack_price j]) p'.le)
 intro m hv₀
 rw [P.wave_beam x V w b q R m q₀]
 exact bead _ (pixel' a r e) (P.lake_c x V w b q R m q₀) (prescribed ..) _ (fun p n'=>P.wave_pin x V w b q R m a p' g y s k q₀ (Q m hv₀) p (show p∈closedBall a r from (DoseTravel.supported a (relative a r e)) ▸ n'))
