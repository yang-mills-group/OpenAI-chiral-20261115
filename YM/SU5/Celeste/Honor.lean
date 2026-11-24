import YM.SU5.Celeste.Miter
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition
variable (P:Spine)(R : P.Register)(j:Axis)
local notation "Ω"=>P.Hil j
local notation "φ"=> P.groundZero j
local notation "μ"=> P.pillars j
local notation "W"=> P.calibration
local notation "ℓ"=> P.calibration.ℓ
local notation "Z"=> P.par
local notation "Q"=> P.par.block
local notation "Ticket"=> Lamour.Bridge.Celeste.Voice
local notation "oneT"=> Lamour.Bridge.Celeste.Voice.one
open Lamour.Bridge.Celeste.Morn
open Ballad
namespace Medal
variable (C:Lead.Clan)
def SharpEnough (η:ℝ): Prop:= η < purePrice C/2 ∧ η+(purePrice C+η)^2 < brill C-η -- useful near lower only η for ep difference
lemma oneBudget(C:Lead.Clan) : ∀ᶠ a:ℝ in nhdsWithin 0 (Set.Ioi 0), SharpEnough C a:= by
 let f(x:ℝ):=x+ (purePrice C+x)^2+x; have ht:Continuous f:=by unfold f; fun_prop
 have he:f 0< brill C:=by simpa [f] using brill_gap C; -- parser
 filter_upwards [eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds (half_pos (purePrice_p C))),eventually_nhdsWithin_of_eventually_nhds (ht.continuousAt.tendsto.eventually (gt_mem_nhds he))] with x hx p;
 exact ⟨hx,lt_sub_iff_add_lt.mpr p⟩
theorem auth {e:ℝ}(p:0<e):∃ η∈ Set.Ioo 0 e,∀ C:Lead.Clan,SharpEnough C η:=by
 have hx: ∀ᶠ x in 𝓝[>] (0:ℝ), x < e:=eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds p); exact (Filter.Eventually.and (Filter.Eventually.and (show ∀ᶠ x in 𝓝[>] (0:ℝ), 0 < x from self_mem_nhdsWithin) hx) (Filter.eventually_all.mpr oneBudget)).exists
lemma brillUp: 0< brill C:=lt_of_le_of_lt (sq_nonneg _) (brill_gap C)
variable (z:ℂ){e:ℝ}(p:0<e)
include p
lemma essence_l (q:‖z-(purePrice C:ℂ)‖ ≤ e)(u:SharpEnough C e): purePrice C/2 < ‖z‖:= by
 have ht:=norm_sub_norm_le (purePrice C:ℂ) z; rw [norm_sub_rev,Complex.norm_real,Real.norm_of_nonneg (purePrice_p C).le] at ht; linarith only [ht, u.1, q]
lemma strong_l (q:‖z-(purePrice C:ℂ)‖≤ e)(u:SharpEnough C e): 1/4≤ ‖(purePrice C:ℂ)⁻¹*z‖:=by
 have ht:= essence_l C z p q u; -- dots may weird
 rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (purePrice_p C).le,mul_comm,← div_eq_mul_inv,le_div_iff₀ (purePrice_p C)]; linarith only [ht,purePrice_p C] -- tune
lemma gives_money (q:‖z-(purePrice C:ℂ)‖≤ e)(u:SharpEnough C e){x:ℝ}(h:0≤x)(v:‖(x:ℂ)-(brill C:ℂ)‖ ≤ e) : e < x- ‖z‖^2:=by
 have hg:= norm_sub_norm_le (brill C:ℂ) (x:ℂ); rw [Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg (brillUp C).le,Real.norm_of_nonneg h,norm_sub_rev] at hg; have he: ‖z‖≤ purePrice C + e:=by
    have h':=norm_sub_norm_le z (purePrice C:ℂ); rw [Complex.norm_real,Real.norm_of_nonneg (purePrice_p C).le] at h'; linarith
 have h' := pow_le_pow_left₀ (norm_nonneg z) he 2; linarith only [u.2,h',v,hg] -- tune
end Medal
variable {z B:ℝ}(x:P.Spectrum0 (3:Axis))(s:ℕ)(A:Gaze P.par.block 4 (reserve P.par P.width) z)
local notation "BJ"=> P.par.block
local notation "Ψ"=> P.singleState 3 s x
local notation "κ"=> P.physicalEnergy (3:Axis) x
local notation "σ" q:max=> P.tuneK (Morn.Holds (BJ) A.hair q)
local notation "Λ" p:max=> P.centered 3 x (Holds (BJ) A.hair p) A.crown s
local notation "Ωm" a:max=> P.colorZero a
variable (i:Lead.Clan)
abbrev Pulsating (e:ℝ):=∀ d:Trinity, ‖(P.singleState 3 s x) (P.tuneK (A.price d))‖≤e
local notation "Z₁" i:max=> (purePrice i:ℂ)
lemma chooseOne (i:Lead.Clan) : P.tuneK (A.price (Sum.inl true,i))=(σ i)-(Z₁ i) • (1:P.Test):=by
 have he: A.label (Sum.inl true,i) = leastOne BJ A.hair i:=by rw [A.oven]
 rw [P.songsAg _ (placates_one BJ A.hair i) he]; rfl
lemma chooseTwo (i:Lead.Clan) : P.tuneK (A.price (Sum.inl false,i))= P.reflectTest 3 (σ i)*(σ i) -(brill i:ℂ) • (1:P.Test):=by
 have he: A.label (Sum.inl false,i)=leastTwo BJ A.hair i:=by rw [A.oven]
 rw [P.songsAg _ (placates_two BJ A.hair i) he,mul_comm]; rfl
lemma chooseLast (i:Lead.Clan) :
    let P':= P.tuneK (placates_one BJ A.hair i);
    P.tuneK (A.price (Sum.inr (),i)) = P.reflectTest 3 P' * P.halfShift 3 A.fare P' := by
 intro P'; let v:= placates_one BJ A.hair i; rw [P.songsAg _ ((v.turn 3 0).mul (v.tract 3 (Heat.gaugeShift (BJ) A.fare))) (by rw [A.oven]; rfl)]; rfl
lemma θSingle_u (i:Lead.Clan){e:ℝ}(h:P.Pulsating x s A e): ‖(Ψ) (σ i)-(Z₁ i)‖≤ e:=by have ht:=h (Sum.inl true,i); rw [P.chooseOne,map_sub,map_smul,show (P.singleState 3 s x) 1=1 from (by rw [P.single_state,P.reading_unit,map_one]),smul_eq_mul,mul_one] at ht; exact ht -- single_state rewrites first!
lemma θSingle_t (i:Lead.Clan){e:ℝ}(h:P.Pulsating x s A e):
    ‖(((‖P.coinK 3 (Morn.Holds BJ A.hair i) x A.crown s‖^2:ℝ):ℂ))-(brill i:ℂ)‖≤ e:=by
 have ht:=h (Sum.inl false,i); rw [P.chooseTwo,map_sub,map_smul,show (Ψ) 1=1 from ?_,smul_eq_mul,mul_one] at ht; swap; · rw [P.single_state,P.reading_unit,map_one]
 have hx:= P.refrain 3 (Morn.Holds BJ A.hair i) (Morn.Holds BJ A.hair i) x A.crown A.crown s; let q:=P.coinK 3 (Morn.Holds BJ A.hair i) x A.crown s; change ‖((↑(‖q‖^2):ℂ) - _)‖ ≤ _; push_cast; rw [← show inner ℂ q q= (↑‖q‖:ℂ)^2 from inner_self_eq_norm_sq_to_K q]; exact hx.symm ▸ ht
lemma θSingle_x {e:ℝ}(i:Lead.Clan)(h:P.Pulsating x s A e) :
    let X:=P.centered 3 x (Morn.Holds BJ A.hair i) A.crown s; let D:= P.halfTime s A.fare; Complex.re (inner ℂ X ((κ).E D X)) ≤ e :=by
 let u:= P.coinK 3 (shaded (Morn.Holds BJ A.hair i) (purePrice i:ℂ)) x A.crown s; intro X D; apply le_trans (P.center_bill 3 x (Morn.Holds BJ A.hair i) A.crown D (purePrice i:ℂ) s) _ -- (κ).E defeq
 change Complex.re (inner ℂ u (P.warming 3 x D u))≤_; apply le_trans (Complex.re_le_norm _) _; let f':= P.tuneK (placates_one BJ A.hair i);
 have he:inner ℂ u (P.warming 3 x D u)= (Ψ) (P.reflectTest 3 f' * P.halfShift 3 A.fare f'):= P.cadet 3 (shaded (Morn.Holds BJ A.hair i) (purePrice i:ℂ)) (shaded (Morn.Holds BJ A.hair i) (purePrice i:ℂ)) x A.crown A.crown s A.fare; have ht:=h (Sum.inr (),i); rw [show P.tuneK (A.price (Sum.inr (),i)) =_ from P.chooseLast A i,←he] at ht; exact ht
lemma θSingle_center {e:ℝ}(i:Lead.Clan)(v:0<e)(p:Medal.SharpEnough i e)(h:P.Pulsating x s A e): e < ‖Λ i‖^2:=by
 let T:=(Ψ) (σ i); have he:= P.center_norm 3 x (Morn.Holds BJ A.hair i) A.crown s; have hl:= Medal.gives_money i T v (P.θSingle_u x s A i h) p (sq_nonneg _) (P.θSingle_t x s A i h); linarith -- ht unfold T
open OS.Semigroup
structure TrinityState(e:ℝ)(i:Lead.Clan): Prop where
 center : e < ‖P.centered 3 x (Morn.Holds P.par.block A.hair i) A.crown s‖^2
 orthogonalRoot : inner ℂ (P.colorZero 3 x) (P.centered 3 x (Morn.Holds P.par.block A.hair i) A.crown s)=0
 away : Complex.re (inner ℂ (P.centered 3 x (Morn.Holds P.par.block A.hair i) A.crown s) ((P.physicalEnergy 3 x).E (P.halfTime s A.fare) (P.centered 3 x (Morn.Holds P.par.block A.hair i) A.crown s)))≤e
 energy : ∃ z:ℝ, (P.physicalEnergy 3 x).edge z (P.centered 3 x (Morn.Holds P.par.block A.hair i) A.crown s)≠ P.centered 3 x (Morn.Holds P.par.block A.hair i) A.crown s
lemma reelCenter {e:ℝ}(i:Lead.Clan)(v:0<e)(p:Medal.SharpEnough i e)(h:P.Pulsating x s A e): P.TrinityState x s A e i:=by
 have hl:= P.θSingle_center x s A i v p h; have ht:= P.θSingle_x x s A i h; refine ⟨hl,(P.center_value ..), ht, ?_⟩
 by_contra! V; let w:= P.centered 3 x (Morn.Holds P.par.block A.hair i) A.crown s; let v:= (κ).E (P.halfTime s A.fare); have hp:v w=w:= (heat_iff_edge 3 (P.physicalEnergy 3 x) w).2 V _
 have h₁:Complex.re (inner ℂ w w)=‖w‖^2:= inner_self_eq_norm_sq (𝕜:=ℂ) w -- implicit names
 change Complex.re (inner ℂ w (v w))≤e at ht; rw [hp,h₁] at ht; exact not_le.mpr hl ht
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.reelCenter
