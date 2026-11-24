import GaugeFieldConstruction.TillQ
/- cap Gate option with kink in Haar integration only (see Poft) -/
set_option autoImplicit false
set_option maxHeartbeats 70000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Precision Laurent Finset MeasureTheory Gauge RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.Frobenius Classical
open Push.Uniform Buffered.Region FlightFlux Work Tensor
variable {E:Type} [NormedAddCommGroup E][NormedSpace ℝ E] {K d v t r u c:ℝ}{j k:ℕ}{n:Side}{G:Gauge}
namespace Shield
open F03
local notation "GS"=> SU.group
variable (o:Site n)
abbrev Score(q:Clip)(U:Config SU.group n)(i:Face (Per n)):= coinF q (faceValue U i)
-- lantern includes all faces involving root site.
def slab(o:Site n):=univ.filter fun i:Face (Per n)=>o ∈ touched i
abbrev Pach(o:Site n):= halo 24 ({o}:Support n)
abbrev Dorm (q:Clip) (U:Config SU.group n):=∑ i∈slab o,Score q U i
abbrev ding_B (q:Clip) (U:Config SU.group n):=∑ i:Face (Per n),Score q U i
lemma slab_q {i:Face (Per n)}: i ∈ slab o ↔ o∈ touched i:=by simp [slab]
lemma slab_p{f:Face (Per n)} (p:f∈slab o): touched f⊆ Pach o:=fun i v=> halo_spec.mpr ⟨o,mem_singleton_self _,((separation_triangle _ _ _).trans (Nat.add_le_add (visit_near f ((slab_q o).1 p)) ((separation_comm i f.1) ▸ visit_near f v))).trans (by decide:2+2≤24)⟩
abbrev plac :=49^4* Fintype.card PlaqAxes
lemma slab_count: (slab o).card ≤ plac:=by
 apply (card_le_card (show slab o⊆Pach o×ˢ (univ:Finset PlaqAxes) from fun i v=> mem_product.mpr ⟨slab_p o v (anchor_visit _),mem_univ _⟩)).trans; rw [card_product,card_univ]; refine Nat.mul_le_mul_right _ ?_; exact (show (Pach o).card≤49^4 from (by simpa [Pach] using Corona.halo_size ({o}:Support n) 24))
abbrev TestVe (t:ℝ)(i:Face (Per n))(U:Config G n):= (1 - (faire G U i^2/t^2)^2)^2
abbrev Turret(t:ℝ)(U:Config G n):= ∏ i∈ slab o,TestVe t i U
lemma turret_inv (t:ℝ): GaugeInvariant (Turret o t (G:=G)):=by intro u A; apply Finset.prod_congr rfl; intro i _; simp only [TestVe,faire,face_gauge,G.chord_conj]
lemma hotel_inv(q: Clip): GaugeInvariant (Dorm o q):=by intro u A; apply sum_congr rfl; intro i _; unfold Score; rw [face_gauge,(coin_s q).conj]
lemma turret_sees(t:ℝ) : LocalOn (Pach o) (Turret o t (G:=G)):=by intro A B p; apply Finset.prod_congr rfl; intro i h; unfold TestVe faire; rw [show faceValue A i=faceValue B i from face_local i A B (agrees_mono p (slab_p o h))]
lemma hotel_sees(q:Clip): LocalOn (Pach o) (Dorm o q):=fun U V p=> sum_congr rfl fun i h=> congrArg (coinF q) (face_local (G:=SU.group) i U V (agrees_mono p (slab_p o h)))
lemma score_π (U:Config SU.group n)(q:Clip)(f:Face (Per n)): ContDiffAt ℝ ω ((fun u=> Score q u f) ∘ increment U) 0:= loads_E q f _ (mat_face_inc f U).contDiffAt
lemma dorm_π(U:Config SU.group n)(q:Clip): ContDiffAt ℝ ω (Dorm o q ∘ increment U) 0 := ContDiffAt.sum fun i _=> score_π U q i -- section o unused
lemma ding_π (U:Config SU.group n)(q:Clip) : ContDiffAt ℝ ω (ding_B q ∘ increment U) 0:= ContDiffAt.sum fun i _=> score_π U q i
lemma lineTur (U:Config G n)(t:ℝ)(f: Face (Per n)): ContDiffAt ℝ ω (TestVe t f ∘ increment U) 0:=by
 simp only [TestVe, Function.comp_def, faire]; simp_rw [G.chord_price]; exact (contDiffAt_const.sub ((contDiffAt_const.mul (price_smooth (mat_face_inc f U).contDiffAt)).div_const _|>.pow 2)).pow _
lemma turret_π(t:ℝ)(U:Config G n): ContDiffAt ℝ ω (Turret o t ∘ increment U) 0:=by
 suffices h : ∀ s : Finset (Face (Per n)), ContDiffAt ℝ ω (fun x=> ∏ i∈s, TestVe t i (increment U x)) 0 from h _
 intro s
 induction s using Finset.induction_on with
 | empty => simp only [Finset.prod_empty]; exact contDiffAt_const
 | @insert i s k ih=> simp_rw [Finset.prod_insert k]; exact (lineTur U t i).mul ih -- tune name
private abbrev MultFee (j:ℕ):ℝ:=2^j*‖ContinuousLinearMap.mul ℝ ℝ‖
private lemma arm_TM {f g:E→ℝ}(h:Allows j f 0 d)(p:Allows j g 0 c): Allows j (f*g) 0 (MultFee j*d*c):= (h.bilinear (ContinuousLinearMap.mul ℝ ℝ) p le_rfl)
private lemma arm_sq {f:E→ℝ}(h:Allows j f 0 d): Allows j (fun i=> f i^2) 0 (MultFee j*d*d):= (arm_TM h h).germ (Eventually.of_forall (fun i=> Eq.symm (pow_two _)))
lemma armCap(k:ℕ)(q:Clip) :∃ R V:ℝ,0≤R∧0≤V∧∀ {n:Side}(t:ℝ),0<t→t≤1→∀ (o:Site n)(U:Config SU.group n),pingS t (Pach o) U→ Allows k (Turret o t ∘ βten t U) 0 R ∧ Allows k (Dorm o q ∘ βten t U) 0 (V*t^2):=by
 obtain ⟨v,e,H⟩:= carves k q
 let x:= MultFee k; have he:0≤x:=mul_nonneg (by positivity) (norm_nonneg (ContinuousLinearMap.mul ℝ ℝ)); let y:=x*v*v; let C:=x*(1+y)*(1+y); let R:=max 1 (x*C); have hc:0≤C:=by unfold C y; positivity
 have hr:1≤R:=le_max_left ..; refine ⟨R^plac,(plac:ℝ)*v,(by positivity),(by positivity),@fun n t p T' o U h=>?_⟩; have hw(i:Face (Per n))(g:i∈ slab o):= H U i t p T' (h i (Finset.not_disjoint_iff.mpr ⟨o,halo_subset _ _ (mem_singleton_self _),(slab_q _).mp g⟩)).le
 constructor
 · have hp(s: Finset (Face (Per n))): s⊆ slab o → Allows k (fun x'=> ∏ i∈s, TestVe t i (βten t U x')) 0 (R^s.card):=by
      induction s using Finset.induction_on with
      | empty => intro _; simp only [card_empty,pow_zero, Finset.prod_empty]; exact allows_const _ (norm_one.le)
      | @insert i s u ih =>
        intro e; have hx:Allows k (fun x'=> faire _ (βten t U x') i^2/t^2) 0 v:=by
            refine Allows.mono ((((hw _ (e (mem_insert_self ..))).2).smul (t^2)⁻¹).germ (Eventually.of_forall (fun i=>?_))) ?_
            · change _* _ =_ /_; rw [div_eq_mul_inv]; exact mul_comm _ _
            rw [abs_of_pos (by positivity)]; apply le_of_eq; field_simp
        simp_rw [Finset.prod_insert u]; refine (arm_TM (arm_sq (minus_B (allows_const _ (show ‖(1:ℝ)‖ ≤1 from norm_one.le)) (arm_sq hx))) (ih fun i v=>e (mem_insert_of_mem v))).mono ?_
        change x*C*R^s.card≤_; rw [card_insert_of_notMem u,pow_succ,mul_comm (R^s.card)]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (by have hp:=zero_le_one.trans hr; positivity)
   exact (hp _ (subset_refl _)).mono (pow_le_pow_right₀ hr (slab_count o))
 refine Allows.mono (allows_sum (f:=fun i x'=> Score q (βten t U x') i) (C:=fun _=> v*t^2) (x:=0) (s:=slab o) fun i g=> (hw i g).1) ?_; rw [sum_const,nsmul_eq_mul,mul_assoc]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast slab_count o) (by positivity)
-- unit/slope extraction. for cost,K use horizon first perturbation. flat at gate−1
private lemma budBall (f:E→ℝ) (u:ContDiffAt ℝ ω f 0)(h:f 0=0)(p:fderiv ℝ f 0=0) : let X:=fun i=> 1-f i^2; let g:=fun i=> X i^2; g 0=1 ∧ fderiv ℝ g 0=0 ∧∀ i j, iteratedFDeriv ℝ 2 g 0 ![i,j]=0:=by
 intro X g; let F:=fun i=>f i^2; let Z(x:ℝ):=(1-x)^2; have hh:g=Z ∘ F:=rfl; let q(x:ℝ):=x^2
 have hu: HasFDerivAt F (0:E→L[ℝ]ℝ) 0:=by have hv:=(u.differentiableAt (by simp)).hasFDerivAt.pow 2; rw [p,smul_zero] at hv; exact hv
 rw [hh]; have hZ:ContDiffAt ℝ ω Z (F 0):=((contDiff_const.sub contDiff_id|>.pow 2):ContDiff ℝ ω Z).contDiffAt; refine ⟨by simp [Z,F,h], by rw [fderiv_comp 0 (hZ.differentiableAt (by simp)) hu.differentiableAt, hu.fderiv]; simp,?_⟩
 intro i j; -- if f' zero but outer z''f'f' & z'f''; F''0=0. use Hess formula
 have hs:ContDiffAt ℝ ω F 0:=u.pow 2
 let U:=fderiv ℝ F; have ht : U 0=0:=hu.fderiv
 have he :fderiv ℝ U 0 i=0:=by apply ContinuousLinearMap.ext; intro l; change fderiv ℝ (fderiv ℝ F) 0 i l=0; rw [← (show iteratedFDeriv ℝ 2 F 0 ![i,l]= fderiv ℝ (fderiv ℝ F) 0 i l from iteratedFDeriv_two_apply F 0 ![i,l]),show F=q ∘ f from rfl, tariff_comp f q _ u ((contDiff_id.pow 2|>.contDiffAt)) (by rw [h]; exact (show HasFDerivAt q (0:ℝ→L[ℝ]ℝ) 0 from (by have hv:=(hasFDerivAt_id (𝕜:=ℝ) (0:ℝ)).pow 2; simp at hv; exact hv)).fderiv),p]; rw [iteratedFDeriv_two_apply]; simp -- tariff uses fderiv q=0 not f; tune
 rw [iteratedFDeriv_two_apply]; let L:= fderiv ℝ (Z∘F); let R:= fderiv ℝ Z; let H(x):=R (F x) ∘L U x
 have hv:L=ᶠ[𝓝 0] H:=by
    filter_upwards [hs.eventually (by simp),hs.continuousAt.eventually (hZ.eventually (by simp))] with i hi hq; exact fderiv_comp _ (hq.differentiableAt (by simp)) (hi.differentiableAt (by simp))
 change fderiv ℝ L 0 i j=0
 have hx:= (((hZ.fderiv_right (m:=1) (by simp)).differentiableAt (by norm_num)).hasFDerivAt.comp _ hu).clm_comp (((hs.fderiv_right (m:=1) (by simp)).differentiableAt (by norm_num)).hasFDerivAt)
 rw [hv.fderiv_eq (𝕜:=ℝ), show fderiv ℝ H 0= _ from hx.fderiv]; simp [show fderiv ℝ F 0=0 from ht, show fderiv ℝ (fderiv ℝ F) 0 i=0 from he]
lemma light_F(i:Face (Per n))(t:ℝ): let F:=TestVe (G:=G) t i ∘ increment 1; F 0=1 ∧ fderiv ℝ F 0=0∧∀ x y,iteratedFDeriv ℝ 2 F 0 ![x,y]=0:=by
 -- use price_low (private) expose
 intro F; let V(x:Directions G n):= faceValue (increment 1 x) i; let A(x):=G.price (V x); let s (x):=2*A x/t^2; have he:F=fun x=> (1 - s x^2)^2:=funext fun x=>by unfold F TestVe; dsimp only [Function.comp_apply]; unfold faire; rw [G.chord_price]
 rw [he]; obtain ⟨hx,hk,ht⟩:= priced0 (G:=G) i
 have hv:ContDiffAt ℝ ω A 0:= price_smooth ((mat_face_inc i 1).contDiffAt); apply budBall s ((contDiffAt_const.mul hv).div_const _) (by change 2*A 0/_=0; rw [show A 0=0 from hx,mul_zero,zero_div])
 have hh:s=fun x=> (2/(t^2)) * A x:=funext fun i=>by unfold s; ring
 have hp:= ((hv.differentiableAt (by simp)).hasFDerivAt.const_mul (2/t^2)).fderiv; rw [hh,hp,show fderiv ℝ A 0=0 from hk]; simp
end Shield
end YM.CF.XGarden
end
