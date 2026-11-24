import YM.SU5.Hiro.Lard
import YM.SU5.Hiro.Platters
import YM.CF.Rel.Graced
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hiro
open Function Filter Fock Finset Cube Spire Scroll MeasureTheory Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Phase Brace Scree Gloss Branch RP Reflect Wilson Lat Rush SU Lat Lattice Precision Tree Tenant Push.SectorMeasure Peaks Tulip Buffered Afterglow Lifted Heat Advance Vale Window
open Reed (Fine)
open Lamour.Bridge.Celeste Lamour.Bridge Lamour
open Py.Rate.LocalLimit.Papal
open Pannier.Chancel Regis.Head.Brecht Regis.Head
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder ContDiff
attribute [local instance] opCStarAlgebra
open Ballad Metric
variable {N:Side}(F D:PlaqAxes)(x y:Cover)(ρ:ℝ){k ε C u Y:ℝ}(p:0<k)
local notation "Px"=> Tower.VacuumSelection.Spine.platePin F (nodeC x)
local notation "Py"=> Tower.VacuumSelection.Spine.platePin D (nodeC y)
local notation "P"=> pepperView F D x y p
local notation "ᵮ" t:max => juice (nodeC x) t k F
local notation "ᵯ" t:max => juice (nodeC y) t k D
abbrev trailV (x:Cover):= (visits (0:Cover) (Etch.toWalk (nodeC x))).toFinset
def coaster : Finset Cover:= ((Px∪Py)∪ spanOf P) ∪ (trailV x ∪ trailV y)
private def adore (x:Cover) (U:LinksC): ColorL →L[ℝ] ColorL :=(SU.group.adjoint (travel U 0 (Etch.toWalk (nodeC x)))).toContinuousLinearMap
private lemma adore_limit : Continuous (adore x):=continuous_clm_apply.mpr fun y=> (Rel.ad_j (G:=SU.group) y).comp (Wilson.continuous_travel (Etch.toWalk (nodeC x)) 0)
private lemma adore_local : LocalOn (trailV x) (adore x) := fun i j h=>congrArg (fun a=> (SU.group.adjoint a).toContinuousLinearMap) (travel_local _ _ i j fun _ u p=> h _ (List.mem_toFinset.mpr u) (List.mem_toFinset.mpr p))
private lemma adore_one : adore x 1 = ContinuousLinearMap.id ℝ ColorL:=by
 ext1 c; suffices A: travel (1:LinksC) 0 (Etch.toWalk (nodeC x))=1 by rw [adore,A]; exact SU.group.adjoint_one ..
 apply show ∀ x:Cover,∀ l:Walk,travel (1: LinksC) x l=1 from ?_; intro x y; induction y generalizing x with
 | nil=>rfl
 | cons a m h=> rw [travel,h,mul_one]; unfold Lattice.Step.read; split; exact inv_one; rfl
include p
lemma toning(e:0<ε):∀ᶠ v:ℝ in 𝓝[>] (0:ℝ),∀ (ρ:ℝ)(N:Side)(U:Pane N),Rightful (dBook N (trailV x)) U 1 v → let b:=onC N U; ‖bungalow F x ρ k b- (ᵮ ρ) b‖≤ε:=by
 let t:=ε/(1+k); have hp:0<t:=by unfold t; positivity
 let d:= adore x; filter_upwards [certified_roots (V:=Metric.ball (adore x 1) t) (adore x) (trailV x) (adore_local x) (adore_limit x).continuousAt (ball_mem_nhds _ hp)] with v u ρ N V w b
 have he:= (Metric.mem_ball.mp (u N V w)).le; let a:= (ᵮ ρ) b; rw [adore_one,dist_eq_norm] at he
 let f:= adore x b- ContinuousLinearMap.id ℝ ColorL; change ‖f a‖≤ _; exact (f.le_opNorm a).trans ((mul_le_mul he (tasteB _ p) (norm_nonneg _) hp.le).trans_eq (div_mul_cancel₀ _ (by positivity))) -- conjunction binder tune
lemma toast(e:0<ε):∀ᶠ v:ℝ in 𝓝[>] (0:ℝ),∀ (ρ:ℝ)(N:Side)(U:Pane N),Rightful (dBook N (coaster F D x y p)) U 1 v → let b:=onC N U; |matchedGauge F D x y ρ k b - inner ℝ ((ᵮ ρ) b) ((ᵯ ρ) b)| ≤ ε:=by
 let T:=ε/(1+k)/2; have ht:0<T:=by unfold T; positivity
 let U:=coaster F D x y p; filter_upwards [toning F x p ht,toning D y p ht] with v u w ρ N P' Q b
 let A:= bungalow F x ρ k b; let B:=bungalow D y ρ k b; let a:= (ᵮ ρ) b; let c:= (ᵯ ρ) b; have he:‖A-a‖≤T:= u _ N P' (Velvet.loft_rightful Q le_rfl (image_subset_image (subset_union_left.trans (show trailV x∪trailV y⊆U from subset_union_right)))) -- `subset_union_left.trans` issue
 have hv: ‖B-c‖≤T:= w _ N P' (Velvet.loft_rightful Q le_rfl (image_subset_image (subset_union_right.trans (show trailV x∪trailV y⊆U from subset_union_right))))
 have h0:‖a‖≤1+k:= tasteB _ p; have hh:‖B‖≤1+k:= (SU.group.norm_adjoint _ _).trans_le (tasteB _ p)
 change |inner ℝ A B-inner ℝ a c|≤ ε; rw [show inner ℝ A B-inner ℝ a c=inner ℝ (A-a) B+inner ℝ a (B-c) from (by rw [inner_sub_left,inner_sub_right]; abel)]; refine (abs_add_le ..).trans ((add_le_add ((abs_real_inner_le_norm ..).trans (mul_le_mul he hh (norm_nonneg _) ht.le)) ((abs_real_inner_le_norm ..).trans (mul_le_mul h0 hv (norm_nonneg _) ((norm_nonneg _).trans h0)))).trans_eq ?_); unfold T; field_simp; ring
lemma crater_bound (U:LinksC): |matchedGauge F D x y ρ k U| ≤ (1+k)^2:=by
 unfold matchedGauge bungalow; apply (abs_real_inner_le_norm ..).trans; simp_rw [SU.group.norm_adjoint]; rw [sq]; exact mul_le_mul (tasteB _ p) (tasteB _ p) (norm_nonneg _) (by positivity)
variable (R:ℕ)(L G:Twah.DirSpin)
local notation "𝒢" r:max=> coaster F D x y r
local notation "tl" r:max=> tubV F D x y ρ r
local notation "fle" v:max=>currentF F x v k R L
local notation "tue" v:max=>currentF D y v k R G
abbrev courseMenu(t:ℂ): Weaver:= fle ρ*tue ρ - t • tl p -- define
lemma menuTag (t:ℂ):Voice (courseMenu F D x y ρ p R L G t) (𝒢 p):= ((Voice.mul (currentLabel F x ρ R L p) (currentLabel D y ρ R G p)).mono (subset_trans subset_union_left subset_union_left)).sub (((tub_voice _ _ _ _ _ p).hushed t).mono (subset_trans subset_union_right subset_union_left)) -- currentLabel order ρ variable? included? test
lemma menuPower (b:ℝ)(e:0≤b) : ∃ u₀>(0:ℝ),∀ (ρ:ℝ)(t:ℂ),‖t‖≤ b→amplitude u₀ (courseMenu F D x y ρ p R L G t):=by
 obtain ⟨q,hx,H⟩:= afford_current F x R L p; obtain ⟨c,v,C⟩:= afford_current D y R G p; let p':=(1+k)^2; refine ⟨q*c+b*p',by unfold p'; positivity,fun ρ t h i Y=>?_⟩; let x':= (fle ρ) i Y; let y':=(tue ρ) i Y; let A:= tubV F D x y ρ p i Y; apply (norm_sub_le (x'*y') (t • A)).trans; refine add_le_add ((norm_mul_le ..).trans (mul_le_mul (H _ _ Y) (C _ i Y) (norm_nonneg _) hx.le)) ?_; rw [norm_smul]; exact mul_le_mul h (tub_budget F D x y ρ p i Y) (norm_nonneg _) e
variable (j:ℕ)(f:1≤j)(t:ℂ)(M:Jill.Male)
include f
lemma layoversingle (h:Kea.Pad j N) (v:0≤ε): flexTrans (fle ρ) (Px) j u ε N M:=fun A _ _ x e=>by rw [currentF,heldVoid R _ _ h f e,norm_zero]; exact v
lemma layoverMenu (w:0≤C) (v:0<ε) :∀ᶠ u:ℝ in 𝓝[>] (0:ℝ), ∃ z>(0:ℝ),∀ {N:Side}(M:Tulip.Male), Kea.Pad j N → let W:= diced R x y L G N j M; ‖W‖ ≤ C→ ∀ (ρ:ℝ)(t:ℂ),dist t W≤z → flexTrans (courseMenu F D x y ρ p R L G t) (𝒢 p) j u ε N M:=by
 let Z:=ε/(2*((1+k)^2)); have hp:0<Z:=by unfold Z; positivity
 let d:=ε/(1+C)/2; have he:0<d:=by unfold d; positivity
 filter_upwards [toast F D x y p he] with u Q
 refine ⟨Z,hp,?_⟩; intro N M hv W pW ρ t ht X h _ a tM
 let ν:=onC N X.1; let b:= (ᵮ ρ) ν; let c:= (ᵯ ρ) ν; let D':= wrapCurrent x L R N b; let E':=wrapCurrent y G R N c; let κ:= matchedGauge F D x y ρ k ν; let A:= inner ℝ b c
 change ‖alleyR (mateK N) a (D' * E' - t • tubV F D x y ρ p N X)‖≤_; rw [vacation_time,map_sub,map_smul,map_smul,cherry R x y L G hv f tM b c,alley_one f hv a tM, smul_eq_mul, smul_eq_mul,mul_one];
 change ‖W*(A:ℂ)-t*κ‖≤_; rw [show W*(A:ℂ)-t*κ=W*((A:ℂ)-κ)+(W-t)*(κ:ℂ) from (by ring)]
 have hz:‖(A:ℂ)-κ‖ ≤ d:=by rw [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_sub_comm]; exact Q ρ N X.1 h
 refine (norm_add_le ..).trans ((add_le_add ((norm_mul_le ..).trans (mul_le_mul pW hz (norm_nonneg _) w)) ((norm_mul_le ..).trans (mul_le_mul ?_ (show ‖(κ:ℂ)‖≤ (1+k)^2 from (Complex.norm_real _).trans_le (crater_bound F D x y ρ p ν)) (norm_nonneg _) hp.le))).trans (b:=C*d+Z*(1+k)^2) ?_)
 · rwa [norm_sub_rev,←dist_eq_norm]
 unfold d Z; field_simp; nlinarith only [p,w,v,sq_nonneg (1+k)]
end YM.CF.Hiro
#print axioms YM.CF.Hiro.layoverMenu
