import YM.SatinExist.Pillared
import YM.SatinExist.Prices
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 680000
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
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set
namespace Spine
open SatinJets OS.Semigroup

-- position conventions: no Eu rescale here.
def lens : E4 ≃L[ℝ] Vantage := (WithLp.linearEquiv 2 ℝ Vantage).toContinuousLinearEquiv
lemma lens_cal : MeasurePreserving lens.toHomeomorph.toMeasurableEquiv volume volume:= PiLp.volume_preserving_ofLp Axis
variable (F U : SampleDose)
private lemma lens_strict : HasCompactSupport (fun x:E4=> (F.val (lens x):ℂ)):= (F.budget.comp_homeomorph lens.toHomeomorph).comp_left Complex.ofReal_zero
def approvedM : _root_.YM.Boundary.Probe E4 := (lens_strict F).toSchwartzMap (Complex.ofRealCLM.contDiff.comp (F.smooth.comp lens.contDiff))
lemma approve_arrives : HasCompactSupport ⇑(approvedM F):= lens_strict F
lemma approve_support : tsupport (approvedM F)=lens ⁻¹' tsupport F.val:=by
 have h : Function.support (approvedM F)=Function.support (F.val ∘ lens):=by ext; simp only [Function.mem_support]; dsimp only [approvedM]; simp
 rw [tsupport,h,←tsupport]; exact tsupport_comp_eq_preimage F.val lens.toHomeomorph
private lemma earlier_ok (p:tsupport F.val⊆reviewEarlierBox.invites):
    ∀ x∈tsupport (approvedM F), 1 ≤ -(time x) :=by
 intro x u; rw [approve_support] at u; have he: (lens x) (3:Axis) < -1:= ((p u) (3:Axis) (Set.mem_univ _)).2
 change time x < -1 at he; linarith
private lemma later_ok (p:tsupport F.val⊆reviewLaterBox.invites):
    ∀ x∈tsupport (approvedM F), 1 ≤ time x:=by
 intro x u; rw [approve_support] at u
 exact ( (show 1 < (lens x) (3:Axis) from ((p u) (3:Axis) (Set.mem_univ _)).1)).le

lemma actual_room (p:tsupport F.val⊆reviewEarlierBox.invites)(q:tsupport U.val⊆reviewLaterBox.invites)
    (s:ℝˣ)(u:0 < (s:ℝ))(v:(s:ℝ)<1/2)(x y:E4)(h:x∈ tsupport (inFlow s (approvedM F)))(z:y∈ tsupport (inFlow s (approvedM U))) :
    2 < ‖spatial (x-y)‖ ∧ x-y∈Mink.spacelike:=by
 rw [tide_scope] at h z
 obtain ⟨x,h,rfl⟩:=h; obtain ⟨y,w,rfl⟩:=z; rw [approve_support] at h w
 let A:=spatial x-spatial y
 have he(k:Axis): -2<lens x k ∧ lens x k < -1:= p h k (Set.mem_univ _)
 have hw(k:Axis): 1<lens y k ∧ lens y k< 2:= q w k (Set.mem_univ _)
 let B:=(0:Fin 3); have hB: (2:ℝ) < ‖A‖:=by
   have ha: -(A B) ≤ ‖A‖:=by
     let Y:= position A 0; have he: Y B.castSucc=A B:= rfl
     have ht:= norm_inner_le_norm (𝕜:=ℝ) (basis B.castSucc) Y; rw [_root_.YM.basis_inner,Real.norm_eq_abs] at ht
     apply le_trans (neg_le_abs (A B))
     rw [← he]; rw [show ‖basis B.castSucc‖ = 1 from ?_,one_mul] at ht; apply ht.trans; have hx:= Mink.squares Y; change ‖Y‖≤‖A‖; rw [spatial_position,time_position] at hx; nlinarith only [hx,norm_nonneg Y,norm_nonneg A]
     rw [← sq_eq_sq₀ (norm_nonneg _) (zero_le_one),← real_inner_self_eq_norm_sq]; simp
   have h₁: spatial x B < -1:= (he B.castSucc).2
   have h₂: 1 < spatial y B:= (hw B.castSucc).1
   have ht:A B=spatial x B-spatial y B:=rfl
   linarith only [h₁,h₂,ha,ht]
 have hx: spatial (tide s x - tide s y)=A:=by simp [tide_at,A, sub_eq_add_neg]
 rw [hx,Mink.lateral,hx]; refine ⟨hB,lt_trans ?_ hB⟩
 have hA: -2 < time x ∧ time x< -1:= he (3:Axis); have hy: 1<time y ∧ time y <2:= hw (3:Axis)
 simp only [sub_eq_add_neg,Mink.clock_add,Mink.clock_neg, tide_at,time_position]
 rw [←sub_eq_add_neg,_root_.mul_sub .. |>.symm,abs_mul,abs_of_pos u, abs_of_neg (by linarith only [hA.2,hy.1] : time x-time y<0)]; nlinarith only [mul_lt_mul_of_pos_left (show -(time x-time y)<4 from by linarith only [hA.1,hy.2]) u,v]

variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "M"=> P.ColorHil 3 (P.advocate 3 x 3)
local notation "G"=> P.ManyF 3 (P.advocate 3 x 3)
local notation "E"=> P.seasons 3 (P.advocate 3 x 3)
local notation "Y"=> P.physicalEnergy 3 (P.advocate 3 x 3)
local notation "Ω"=> P.heaven 3 (P.advocate 3 x 3)
local notation "Γ"=> P.cartage 3 (P.advocate 3 x 3)
variable (V:∀ j:Axis,List Axis → ℝ → P.ColorHil j (P.advocate 3 x j)) (w:Lead.Clan→ Prism)
local notation "ℒ"=> Lead.Clan
local notation "Λ" a:max => P.profilesZ x V w a
local notation "Y₁" a:max=> DoseTravel.beam (G) F (P.earlierProfile x V w 1 a)
local notation "Y₂" a:max=> DoseTravel.beam (G) U (P.laterProfile x V w 1 a)
lemma uses_actual (p:E4) : (E).U (SEP timeAxis p) = Γ (lens p):=by
 rw [P.uses_cart]; apply congrArg _; rw [eyes_toFace timeAxis (SEP timeAxis p)]; apply congrArg _
 funext i; let b:=(3:Axis); change (p-p timeAxis • basis timeAxis) i.val=p i.val; have ht:i.val ≠ timeAxis:=i.property; simp only [PiLp.sub_apply,PiLp.smul_apply]; simp [ht]

private lemma stamp_neg (h:tsupport F.val⊆reviewEarlierBox.invites)(a:ℒ): latePoint (E) (Λ a) (approvedM F) (-1) = Y₁ a :=by
 unfold latePoint DoseTravel.beam
 rw [← lens_cal.integral_comp']
 refine integral_congr_ae (Eventually.of_forall fun p=>?_)
 change ((approvedM F p):ℂ) • (E).U _ _ = ((approvedM F p):ℂ) • Γ (lens p) ((Λ a) (max 1 (- time p)))
 by_cases e:p∈ tsupport (approvedM F)
 · rw [neg_mul,one_mul, max_eq_right (earlier_ok F h p e), P.uses_actual]; rfl
 rw [image_eq_zero_of_notMem_tsupport e,zero_smul,zero_smul]

private lemma stamp_pos (h:tsupport U.val⊆reviewLaterBox.invites)(a:ℒ): latePoint (E) (Λ a) (approvedM U) 1 = Y₂ a:=by
 unfold latePoint DoseTravel.beam
 rw [← lens_cal.integral_comp']; refine integral_congr_ae (Eventually.of_forall fun p=>?_)
 change ((approvedM U p):ℂ) • (E).U _ _ = ((approvedM U p):ℂ) • Γ (lens p) ((Λ a) (max 1 (time p)))
 by_cases e:p∈tsupport (approvedM U)
 · rw [one_mul,max_eq_right (later_ok U h p e),P.uses_actual]; rfl
 rw [image_eq_zero_of_notMem_tsupport e,zero_smul,zero_smul]

private lemma unit_morning (p:E4): (E).unit.translation p Ω = Ω:=by
 have h: Ω∈(E).ground:= ((E).fixed _).2 (P.heaven_hot 3 ξ)
 change (E).edge (time p) ((E).U (SEP timeAxis p) Ω) = Ω
 rw [P.uses_actual,P.cart_empty]; exact Spectral.Alps.mink_invar (E) Ω (time p) h

private lemma veil {Z:ℝ→G}(w:VacuumVector (G))(p:Rim (E) Z w)(v:∀ s:ℝ,0<s → (E).orth (Z s)=0)(f: _root_.YM.Boundary.Probe E4): inner ℂ Ω (w f)=0:=by
 let Ht:=Z 1; have h: Ω∈(E).ground:= ((E).fixed _).2 (P.heaven_hot 3 ξ)
 have ht(u:G): inner ℂ Ω u=inner ℂ Ω ((E).orth u):=by
    nth_rw 1 [← (show (E).orth Ω=Ω from Submodule.starProjection_eq_self_iff.mpr h)]; exact Submodule.inner_starProjection_left_eq_right ..
 let a:= (1:ℝ).toNNReal
 have hp: Integrable (fun i:E4=> f i • (E).unit.translation i Ht):=by rw [← exchange_pay f]; exact SNAG.over ..
 have hu(i:E4): inner ℂ Ω ((E).unit.translation i Ht) = 0:=by
    rw [← P.unit_morning x i]
    let V:= (E).unit.translation i; let U:G→ₗᵢ[ℂ] G:=⟨V.toLinearMap, (E).unit.unitary i⟩
    change inner ℂ (U Ω) (U Ht)=0; rw [U.inner_map_map,ht Ht, show (E).orth Ht=0 from v 1 zero_lt_one,inner_zero_right]
 calc
    _= inner ℂ ((E).E a Ω) (w f):=by rw [P.heaven_hot]
    _= inner ℂ Ω (advancing (E) Ht f):=by rw [OS.Semigroup.swing]; exact congrArg (inner ℂ Ω) (p.pays 1 zero_lt_one f)
    _=_:=by rw [advancing_eq,← integral_inner hp]; simp_rw [inner_smul_right,hu]; simp

structure E4bridge (A:ℕ→P.Apron)(c r n:ℕ→ℕ)(T:P.HandleWith x c r A n) (W:ℒ→ VacuumVector (G)):Prop where
 costs (a:ℒ): Rim (E) (Λ a) (W a)
 means (a:ℒ)(f: _root_.YM.Boundary.Probe E4): inner ℂ Ω (W a f)=0
 leg : WickLeg (S:=P.seasons 3 (P.advocate 3 x 3)) («Y»:=fun a=> P.profilesZ x V w a) W (fun a=> Y₁ a) (fun a=> Y₂ a) (approvedM F) (approvedM U)
 real_mark (p q:ℝ)(v:p<q)(u:0≤p)(z:q≤1/2): ∃ s:ℝˣ,(s:ℝ) ∈ Ioo p q ∧
   (∀ i∈ tsupport (inFlow s (approvedM F)),∀ h∈tsupport (inFlow s (approvedM U)),2< ‖spatial (i-h)‖ ∧ i-h∈Mink.spacelike) ∧
   let Z0:=desk (H:=G) (fun i=> W i (inFlow s (approvedM F))) (fun i=> W i (inFlow s (approvedM U))); Z0.det≠0 ∧ ∀ i,Z0 i i≠0
 unpad (a:ℒ)(f: _root_.YM.Boundary.Probe E4): ∃ q:ℝ→G,(Tendsto q (𝓝[>] (0:ℝ)) (𝓝 (W a f))) ∧
   ∀ t:ℝ,0< t → Tendsto (fun i=> advancing (E) (P.cradleG x (P.soldTrumpet A c r n w a i) (P.sold_birth x A c r n w a i T) t) f) atTop (𝓝 (q t))
-- unpad pays physical rotations on the limit explicitly; no amount of unitary continuity in the
-- spatial directions on **full marks** is asserted. Uses ManyF, not pretending full net generated.

lemma bridge_from_costs (p:P.PolynomialControl w (V:=V)) {A:ℕ→P.Apron}{c r n:ℕ→ℕ}
    {T:P.HandleWith x c r A n}{g h s k:ℕ}{K:P.Register}
    (Q:P.FullPrismLab x A c r n w V g h T 1 F U reviewEarlierBox reviewLaterBox s k K):
      ∃ W:ℒ→ VacuumVector (G), P.E4bridge F U x V w A c r n T W :=by
   have he:= fun a=> (Q.armada.energy a).2.1
   choose W hz using fun a=> unpad (E) _ (he a) (p.channels a).2
   have hu : charges timeAxis (-1) (approvedM F):= fun t v=> by rw [neg_mul,one_mul]; exact zero_lt_one.trans_le (earlier_ok F Q.supports.1 t v)
   have hp: charges timeAxis 1 (approvedM U):= fun t v=> by rw [one_mul]; exact zero_lt_one.trans_le (later_ok U Q.supports.2 t v)
   have ht:= WickLeg.earn W _ _ (approve_arrives F) (approve_arrives U) hu hp hz (fun a=>(p.channels a).2) he
   simp_rw [P.stamp_neg F x V w Q.supports.1, P.stamp_pos U x V w Q.supports.2] at ht
   refine ⟨W,hz,fun a f=>P.veil x (W a) (hz a) (fun i b=> ((((Q.armada.energy a).2.2 i b).2).1)) f,ht,?_,?_⟩
   · intro p q v u z
     obtain ⟨s,h,k⟩:= ht.sights W _ _ Q.all_six.1 Q.all_six.2 v u
     exact ⟨s,h, actual_room F U Q.supports.1 Q.supports.2 s (u.trans_lt h.1) (lt_of_lt_of_le h.2 z) -- quant order
       |>(fun g=>fun i w k =>g i k w),k⟩
   intro a f; refine ⟨fun t=> advancing (E) ((Λ a) t) f,(hz a).costs f,fun t e=>?_⟩
   simp_rw [advancing_paid]; exact ((SNAG.send (E).unit (exchange f)).continuous.tendsto _).comp (Q.armada.heated_points a t e).2
-- prices for near angles made on THIS probe, before refund at height t.
lemma rotates_by_marks {A:ℕ→P.Apron}{c r n:ℕ→ℕ}
    {T:P.HandleWith x c r A n}{g h s k:ℕ}{K:P.Register}
    (Q:P.FullPrismLab x A c r n w V g h T 1 F U reviewEarlierBox reviewLaterBox s k K)
    (σ:ℝ)(u:ℝ)(p:0 < u)(D:SampleDose)(z:ℂ)(a:ℒ):
     Tendsto (fun i=> fareR (E) σ (approvedM D) (P.cradleG x (P.soldTrumpet A c r n w a i) (P.sold_birth x A c r n w a i T) u) z) atTop (𝓝 (fareR (E) σ (approvedM D) ((Λ a) u) z)):= ((RollCost (E) σ z (approvedM D)).continuous.tendsto _).comp (Q.armada.heated_points a u p).2
lemma rank_from_steam {W:ℒ→ VacuumVector G}{A:ℕ→P.Apron}{c r n:ℕ→ℕ}
    {T:P.HandleWith x c r A n}(B:P.E4bridge F U x V w A c r n T W)(p q:Vantage)(u:p 3<q 3)(a b:ℒ):
    let t:ℝ:= (q-p) 3/2
    Tendsto (fun i:ℕ=> inner ℂ ((E).E t.toNNReal (W a (homePad i))) (Γ (q-p) ((E).E t.toNNReal (W b (homePad i))))) atTop (𝓝 (P.pointPrism x V w (q-p) a b)):=by
 intro t; have ht: 0<t:= half_pos (sub_pos.mpr u); let U:= Γ (q-p)
 exact ((B.costs a).reclaim t ht).inner (𝕜:=ℂ) ((U.continuous.tendsto _).comp ((B.costs b).reclaim t ht))

-- Any representation of this vacuum that treats the limiting point consult from these
-- two-point/signal families by positive heat recovery, also obtains the same CP18 positive
-- profile irrespective of analytic representative. Real wave answers are unique, with that
-- orientation. See `Unpad.lean`. No assertion that the physical comparison descends.
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
