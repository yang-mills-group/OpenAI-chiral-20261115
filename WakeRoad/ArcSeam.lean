import WakeRoad.Quartz
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 200000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical ContDiff
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
open OS.Semigroup YM.OS.Semigroup.Gingham
open Boundary Probe
namespace Spine.NativeSeam
open YM.OS YM.OS.Semigroup SatinRegistration YM.Velour YM.SatinMacro
variable (P:Spine)(x:P.Spectrum0 3)
local notation "jₓ"=> (3:Axis)
local notation "ξ"=> P.advocate 3 x jₓ
local notation "G"=> P.ManyF jₓ ξ
local notation "ℰ"=> P.seasons jₓ ξ
local notation "Ω"=> P.heaven jₓ ξ
local notation "W"=>carry P x
local notation "T"=>(ℰ).E
local notation "q*"=> foldSpace
variable (B D:P.Apron)
abbrev traceV (D:P.Apron):G:= flashY x D jₓ - native P x D • Ω
def songV (B:P.Apron):G:= glareY x B jₓ - star (native P x B) • Ω
local notation "s₀" => songV P x
local notation "t₀" => traceV P x
lemma stars_fee (J:P.Ellis 3 x) {A:G →L[ℂ] G} (h:A Ω = Ω) (e:A.adjoint Ω = Ω):
    inner ℂ (s₀ B) (A (t₀ D))=inner ℂ (glareY x B jₓ) (A (flashY x D jₓ)) - (native P x B)*(native P x D):=by
    unfold songV traceV
    have h0:= (lit_alone jₓ x B).trans (one_chit P x B J).symm
    have v: ⟪Ω,A (flashY x D jₓ)⟫_ℂ=native P x D:=by rw [←ContinuousLinearMap.adjoint_inner_left,e, ←one_chit P x D J]
    have w : ⟪Ω,Ω⟫_ℂ=1:=by rw [inner_self_eq_norm_sq_to_K,P.stone_norm]; norm_num
    rw [map_sub,map_smul,h,inner_sub_left,inner_sub_right,inner_smul_left,inner_sub_right,←Complex.star_def,star_star,inner_smul_right,inner_smul_right,h0,v,w]; ring
-- one half-plane in SATIN physical units
local notation "wharf" => Cheer.shore ∘ spacePart
abbrev melody (r:Vantage)(z:ℂ):ℂ:= SatinMacro.carried ℰ (s₀ B) (t₀ D) (wharf r) z
lemma chord_price(p q:Vantage)(J:P.Ellis 3 x)(h:q-p∈ P.forwardPair B D jₓ):
    let r:= q-p
    let t:=(r 3 - (B.realWidth P 3 + D.realWidth P 3)).toNNReal
    P.bodyPair x B D p q - (native P x B)*(native P x D)=melody P x B D r (SatinMacro.rise t):=by
    intro r t
    rw [P.bodyPair_fwd x B D jₓ p q J h,melody,SatinMacro.carried_rise]
    let A:= (T t).comp (W r)
    have ht:A Ω=Ω:=by unfold A; rw [ContinuousLinearMap.comp_apply,P.cart_empty,P.heaven_hot]
    have he:A.adjoint Ω=Ω:=by unfold A; rw [ContinuousLinearMap.adjoint_comp,(ℰ).sym, ContinuousLinearMap.comp_apply,P.heaven_hot,P.cart_reverses,P.cart_empty]
    change inner ℂ (glareY x B jₓ) (A (flashY x D jₓ)) - _ = _
    rw [← stars_fee P x B D J (A:=A) ht he] -- abbrev comp applies?
    unfold SatinMacro.kernel A; rw [ContinuousLinearMap.comp_apply]; unfold carry; rw [P.warm_drive,P.cart_space]; rfl

local notation "U" => (ℰ).unit.translation
lemma wharf_id (r:Vantage): SatinMacro.joinST (wharf r) (r 3)=q*.symm r:=by
    ext i; refine Fin.lastCases ?_ (fun i'=>?_) i
    · exact (SatinMacro.joinST_clock ..)
    change position (spacePart r) 0 i'.castSucc + r 3 * basis jₓ i'.castSucc = r i'.castSucc
    have e:i'.castSucc ≠(3:Axis):=Fin.castSucc_ne_last i'
    unfold position spacePart spatial; simp [e]
-- adjust only time in earning edge
lemma wharf_same (r:Vantage)(k:ℝ): wharf (update r jₓ k)=wharf r:=by
    apply congrArg Cheer.shore
    ext i; change update r jₓ k i.castSucc=r _; exact update_of_ne (Fin.castSucc_ne_last i) ..
-- Identity theorem in upper half price domain. enforces nonzero real boundary already.
lemma rim_alive {s:ℂ→ℂ}(h:AnalyticOnNhd ℂ s {z:ℂ|0<z.im})(g:Continuous s) {t:ℂ}(p:0<t.im)(e:s t≠0) {a b:ℝ}(u:a<b):∃r∈Ioo a b,s r≠0:=by
    by_contra! l
    let D:= fun z:ℂ=>s (-z)
    have he:AnalyticOnNhd ℂ D {z:ℂ|z.im<0}:=by
       intro z z'; exact AnalyticAt.comp (𝕜:=ℂ) (h (-z) (by simpa using (show z.im<0 from z'))) (analyticAt_id.neg : AnalyticAt ℂ (fun z:ℂ=>-z) z)
    let r:=-(t.im+1); have hr:r<0:=by unfold r; linarith
    have Hx(x:ℝ)(p:x∈Ioo (-b) (-a)):(0:ℂ)=D x:=by
       unfold D; rw [←Complex.ofReal_neg,l _ (by constructor <;> linarith only [p.1,p.2] : -x∈Ioo a b)]
    have k:= SatinMacro.Glue.overlap_of_edge (f:=fun _:ℂ=>(0:ℂ)) (g:=D) (neg_lt_neg u) hr analyticOnNhd_const he (g.comp continuous_neg|>.continuousOn) Hx
    have v:= k (show -t ∈ {z:ℂ|r<z.im}∩ {z:ℂ|z.im<0} from (by simp [r,p]))
    apply e; simpa [D] using v.symm
abbrev dancing (y:Vantage)(v:G):G:= U (q*.symm y) v
lemma stepV (p q:Vantage)(u v:G): inner ℂ (dancing P x p u) (dancing P x q v)=inner ℂ u (U (q*.symm (q-p)) v):=by
    rw [dancing,←ContinuousLinearMap.adjoint_inner_right]; unfold dancing; rw [←ContinuousLinearMap.star_eq_adjoint,(ℰ).unit_star, ←ContinuousLinearMap.comp_apply,(ℰ).unit.sends,map_sub,neg_add_eq_sub]
lemma chargeReal (k:ℝ)(r:Vantage): melody P x B D r k=
    inner ℂ (s₀ B) (U (q*.symm (update r jₓ k)) (t₀ D)):=by
    rw [melody,SatinMacro.carried_edge,←wharf_id (update r jₓ k),wharf_same,update_self]; rfl
-- aperture actual REAL prices & add freely chosen external padding, at that same point system
-- with associated actual operator (stage_core) & vacuum claims later
abbrev faded (k:ℝ≥0)(B:P.Apron)(p:Vantage):G:=dancing P x p (T k (glareY x B jₓ))
abbrev sounded (k:ℝ≥0)(B:P.Apron)(p:Vantage):G:= dancing P x p (T k (flashY x B jₓ))
lemma home_flight (p:E4): U p Ω=Ω:= (Spine.Gingham.home_basis P x).2 p
lemma move_cont (v:G): Continuous (fun y:Vantage=>dancing P x y v):=(ℰ).unit.moves v|>.comp q*.symm.continuous
-- centered real test at point
lemma real_kernel (r:Vantage)(p q:Vantage)(h:q-p=r)(J:P.Ellis 3 x):
    melody P x B D r (r 3)=inner ℂ (faded P x 0 B p) (sounded P x 0 D q)-native P x B*native P x D:=by
    rw [chargeReal, update_eq_self, faded, sounded,(ℰ).eZero]; dsimp only [ContinuousLinearMap.id_apply]; rw [stepV P x,h]
    refine stars_fee P x B D J (home_flight P x _) ?_
    rw [←ContinuousLinearMap.star_eq_adjoint,(ℰ).unit_star]; exact home_flight P x _
abbrev flash (k:ℝ≥0)(F:SampleDose): G:= DoseTravel.beam G F (faded P x k B)
abbrev strike (k:ℝ≥0)(F:SampleDose): G:= DoseTravel.beam G F (sounded P x k B)
-- fixed aperture unpad: commute with whole translation. with seals that retain actual allowance-<d> padded
lemma paid_dance (k:ℝ≥0)(p:Vantage)(v:G) : dancing P x p (T k v)= T k (dancing P x p v):=by
    unfold dancing; have u: T k ∘L (U (q*.symm p))= (U (q*.symm p)) ∘L T k:= (ℰ).overE k (q*.symm p)
    exact (DFunLike.congr_fun u v).symm
lemma paid_flash (k:ℝ≥0)(F:SampleDose): flash P x B k F=T k (flash P x B 0 F):=by
    unfold flash DoseTravel.beam faded; simp only [(ℰ).eZero,ContinuousLinearMap.id_apply]
    rw [←ContinuousLinearMap.integral_comp_comm _ (velvet_integrable F (move_cont P x _))]; simp_rw [paid_dance,map_smul]
lemma paid_strike (k:ℝ≥0)(F:SampleDose): strike P x B k F=T k (strike P x B 0 F):=by
    unfold strike DoseTravel.beam sounded; simp only [(ℰ).eZero,ContinuousLinearMap.id_apply]
    rw [←ContinuousLinearMap.integral_comp_comm _ (velvet_integrable F (move_cont P x _))]; simp_rw [paid_dance,map_smul]
abbrev RealCosts (F V:SampleDose)(k:ℝ≥0) : Gingham.Parts:=(inner ℂ (flash P x B k F) (strike P x D k V),inner ℂ (flash P x B k F) Ω,inner ℂ Ω (strike P x D k V))
-- needs F normalized on both. prove exact.
lemma PaidOne (F:SampleDose)(k:ℝ≥0)(h:F.Normalized)(J:P.Ellis 3 x): inner ℂ (flash P x B k F) Ω=native P x B ∧ inner ℂ Ω (strike P x B k F)= native P x B:=by
    have hx(A:G): inner ℂ Ω (DoseTravel.beam G F (fun p=> dancing P x p A))= inner ℂ Ω A:=by
       rw [DoseTravel.beam,←integral_inner (velvet_integrable F (move_cont P x _))]; simp_rw [inner_smul_right,dancing, ←ContinuousLinearMap.adjoint_inner_left, ←ContinuousLinearMap.star_eq_adjoint,(ℰ).unit_star,home_flight]; rw [integral_mul_const,integral_complex_ofReal,h.2]; simp
    rw [paid_flash,paid_strike]
    rw [OS.Semigroup.swing,P.heaven_hot,← OS.Semigroup.swing,P.heaven_hot]
    unfold flash faded strike sounded
    simp only [(ℰ).eZero,ContinuousLinearMap.id_apply]
    constructor
    · rw [← @inner_conj_symm ℂ _ _ _ _ _ Ω] -- args
      rw [hx]; simpa only [inner_conj_symm] using (lit_alone jₓ x B).trans (one_chit P x B J).symm
    rw [hx]; exact (one_chit P x B J).symm
lemma real_unpad (F V:SampleDose): Tendsto (RealCosts P x B D F V) (𝓝[>] 0) (𝓝 (RealCosts P x B D F V 0)):=by
    unfold RealCosts
    have h₀(v:G): Tendsto (fun k=>T k v) (𝓝[>] (0:ℝ≥0)) (𝓝 v):=by
       have he: Tendsto (fun k=>T k v) (𝓝[>] (0:ℝ≥0)) (𝓝 (T 0 v)):= ((ℰ).continuousE v).continuousWithinAt
       simpa only [(ℰ).eZero,ContinuousLinearMap.id_apply] using he
    have he:Tendsto (fun k=>flash P x B k F) (𝓝[>] (0:ℝ≥0)) (𝓝 (flash P x B 0 F)) := (h₀ _).congr fun i=>(paid_flash P x B i F).symm
    have hh:Tendsto (fun k=>strike P x D k V) (𝓝[>] (0:ℝ≥0)) (𝓝 (strike P x D 0 V)) := (h₀ _).congr fun i=>(paid_strike P x D i V).symm
    exact (he.inner hh).prodMk_nhds ((he.inner tendsto_const_nhds).prodMk_nhds (tendsto_const_nhds.inner hh))
#print axioms PaidOne
end Spine.NativeSeam
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
