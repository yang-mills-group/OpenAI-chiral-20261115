import SatinThinBilateral
import SatinPP.Corners
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3500
set_option maxHeartbeats 650000
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

variable (P:Spine)(x:P.Spectrum0 3)(j:Axis)
local notation "ξ"=> P.advocate 3 x j
local notation "G"=> P.ManyF j ξ
local notation "Γ"=> P.cartage j ξ
local notation "Θ"=> P.seasons j ξ
local notation "E"=> (Θ).E
local notation "κ"=> P.wealth j ξ
local notation "D" s:max=>P.lengthP s
local notation "Xρ" s:max=> P.basePlay x (P.pointEra s) s


local notation "St" s:max l:max=> (Xρ s).pivot P l
abbrev faceWidth (s:ℕ):ℝ:= (P.roomy:ℝ)*P.paceN s
lemma face_t : Tendsto P.faceWidth atTop (𝓝 0):= by simpa only [mul_zero] using P.paceN_t.const_mul (P.roomy:ℝ)
lemma lengthP_pos (s:ℕ):0< D s:=P.flight_pos _
lemma width_face(s:ℕ)(l:List Axis) : (St s l).realWidth P j=P.lengthP s*P.faceWidth s:=by rw [Apron.pivot_w,P.play_width]; unfold faceWidth; rw [←P.paceN_width];ring
def lightKet (s:ℕ)(l:List Axis)(t:ℝ): G:=P.factor s • P.beam j x (St s l) (D s*t)
lemma lamplight (s:ℕ)(l:List Axis){v t:ℝ} (h:P.faceWidth s ≤ v)(q:v ≤ t): P.lightKet x j s l t = E ((D s)*(t-v)).toNNReal (P.lightKet x j s l v):= by
 have hv:= (P.lengthP_pos s).le
 unfold lightKet; rw [P.beam_twice j x (St s l) ((P.width_face x j s l).trans_le (mul_le_mul_of_nonneg_left h hv)) (mul_le_mul_of_nonneg_left q hv),map_smul,mul_sub]

lemma light_mono (s:ℕ)(l:List Axis){v t:ℝ} (h:P.faceWidth s ≤ v)(q:v ≤ t): ‖P.lightKet x j s l t‖ ≤ ‖P.lightKet x j s l v‖:= by
 rw [P.lamplight x j s l h q]; exact (ContinuousLinearMap.le_opNorm ..).trans (mul_le_of_le_one_left (norm_nonneg _) ((Θ).shrinks _))
lemma scene_issue (s:ℕ)(l:List Axis)(y:Vantage): P.issuing s (St s l) (P.tap y s)= P.centeredQ x s (P.pix l y s):= by
 let Z:= St s l; have he:Z.s=s:= Apron.pivot_s ..
 have hu:=P.issuing_here Z (P.tap y s); rw [he] at hu; rw [show _=P.chartAll (P.tap y s) (St s l).F from hu,P.baseP_F,P.chart_center]
variable {r:ℕ→ℕ}
local notation "Lk" s:max l:max=> P.lightKet x j s l
-- upper bounds via tie
lemma stocks_ties (s:ℕ)(l:List Axis)(y:Vantage)(w:P.faceWidth s ≤ P.roundPose y s j):
    ‖(Lk s l) (P.roundPose y s j)‖^2 ≤ (P.paidPix x s (P.pix l y s) (opposeQ j (P.pix l y s))).re:= by
 let a:=P.tap y s
 have ht:P.meshPose s a j=P.lengthP s*(P.roundPose y s j):= by unfold a; rw [P.tap_scale];rfl
 obtain ⟨b,z⟩:=P.beam_grid_pose_view j x (St s l) s a ((P.width_face x j s l).trans_le ((mul_le_mul_of_nonneg_left w (P.lengthP_pos s).le).trans_eq ht.symm)) (Apron.pivot_s P _ l).le

 let Y:= P.factor s • P.beamGridRay j x (St s l) s a
 have hY: inner ℂ Y Y=P.paidPix x s (P.pix l y s) (opposeQ j (P.pix l y s)):= by
    unfold Y; rw [←z, inner_smul_left,inner_smul_right,P.released_gram,P.single_agrees]; unfold a; rw [P.scene_issue,P.reflect_any,←mul_assoc];rfl
 refine (pow_le_pow_left₀ (norm_nonneg _) (?_: ‖(Lk s l) (P.roundPose y s j)‖ ≤ ‖Y‖) _).trans_eq (by rw [←hY]; exact (inner_self_eq_norm_sq (𝕜:=ℂ) Y).symm)
 unfold Y beamGridRay; rw [←map_smul,P.truck_norm]; unfold lightKet; rw [ht,P.beam_bank,←map_smul]; exact P.bank_cost ..

variable (H:P.Spots r x)(τ:Tendsto r atTop atTop)
include H τ
lemma enough_ties (l:List Axis){b:ℝ}(n:ℕ)(e:0<spl n j)(z:spl n j<b){δ:ℝ}(q:0<δ):
 ∀ᶠ i in atTop,∀ c:ℝ, b ≤ c→ ‖(Lk (r i) l) c‖^2 ≤ (gloss (spl n - opposeR j (spl n))).re + δ:= by
 let w:=spl n
 have hu:w≠ opposeR j w:= by intro h; have t:=congrFun h j; rw [show opposeR j w j = -w j from if_pos rfl] at t; have he:0<w j:=e;linarith only [t,he]
 let f(s):=P.paidPix x s (P.pix l w s) (opposeQ j (P.pix l w s))
 let c:= (gloss (w-opposeR j w)).re
 have he:Tendsto (fun i=> (f (r i)).re) atTop (𝓝 c):=Complex.continuous_re.continuousAt.tendsto.comp (P.paid_sight H τ (n,l,none) (n,l,some j) hu)
 let t(s):=P.roundPose w s j; have ht:Tendsto (fun i=> t (r i)) atTop (𝓝 (spl n j)):= (tendsto_pi_nhds.mp (P.tap_t w) j).comp τ

 filter_upwards [he.eventually (ge_mem_nhds (lt_add_of_pos_right _ q)),ht.eventually (ge_mem_nhds z), (P.face_t.comp τ).eventually_lt ht e] with i p a d c' h
 exact (pow_le_pow_left₀ (norm_nonneg _) (P.light_mono x j _ l d.le (a.trans h)) _).trans ((P.stocks_ties x j _ l w d.le).trans p)
-- Rough enough
lemma rough_bound (l:List Axis){b:ℝ}(u:0<b): ∃ c:ℝ,0<c ∧ ∀ᶠ i in atTop,∀ e, b ≤ e→ ‖(Lk (r i) l) e‖ ≤ c:= by
 obtain ⟨n,h⟩:= spl_dense.exists_mem_open (s:={y:Vantage | (y j)∈Set.Ioo 0 b}) (isOpen_Ioo.preimage (continuous_apply (A:= fun _:Axis => ℝ) j)) (⟨fun _=>b/2,half_pos u,half_lt_self u⟩)
 let z:= (gloss (spl n-opposeR j (spl n))).re+1
 refine ⟨|z|+1,by positivity,?_⟩
 filter_upwards [P.enough_ties x j H τ l n h.1 h.2 zero_lt_one] with i p e t
 have he: ‖(Lk (r i) l) e‖^2≤|z|:=(p _ t).trans (le_abs_self _)
 nlinarith only [he, abs_nonneg z]

omit H τ
local notation "ord₂"=> ([false,true]:List Bool)
local notation "U%" s:max l:max t:max=> usher (St s l) (St s t)
local notation "Ch"=> P.commonWell 3 x
-- 0,p version
def sparkle (s:ℕ)(l t:List Axis)(p:Vantage):ℂ:= (starRingEnd ℂ) (P.factor s)*(P.factor s)*(Ch) (U% s l t) (usher (0:Vantage) ((D s) • p)) ord₂
variable (J:P.Ellis 3 x)
include J
lemma sparkle_plus (s:ℕ)(l t:List Axis)(p:Vantage)(h:P.faceWidth s<p j/2):
 P.sparkle x s l t p = inner ℂ ((Lk s (j::l)) (p j/2)) (Γ ((D s) • p) ((Lk s t) (p j/2))) := by
 let d:= D s; let q:= d • p
 have he:(q-0) j/2=d*(p j/2):=by unfold q; rw [sub_zero,Pi.smul_apply,smul_eq_mul,mul_div_assoc]
 have hz (L:List Axis): (St s L).realWidth P j < (q-0) j/2:= by rw [P.width_face,he]; exact mul_lt_mul_of_pos_left h (P.lengthP_pos s)
 unfold sparkle
 rw [P.bilateral_plus x j J (St s l) (St s t) _ _ (hz l) (hz t), he, sub_zero]
 unfold lightKet; rw [Apron.pivot_cons,map_smul,inner_smul_left,inner_smul_right,mul_assoc]

lemma sparkle_minus(s:ℕ)(l t:List Axis)(p:Vantage)(h:P.faceWidth s< (-p) j/2):
 P.sparkle x s l t p = P.sparkle x s t l (-p):= by
 let d:= D s; let q:=d • p
 have he:(0-q) j/2=d*((-p) j/2):=by unfold q; rw [zero_sub,←smul_neg,Pi.smul_apply,smul_eq_mul,mul_div_assoc]
 have hz (L:List Axis): (St s L).realWidth P j < (0-q) j/2:= by rw [P.width_face,he]; exact mul_lt_mul_of_pos_left h (P.lengthP_pos s)
 rw [sparkle]
 rw [P.bilateral_minus x j J (St s l) (St s t) _ _ (hz t) (hz l), P.sparkle_plus x j J s t l (-p) h] -- rw sparkle unfolded fails → replace unfolding selective
 rw [P.bilateral_plus x j J (St s t) (St s l) _ _ (hz t) (hz l),he,zero_sub,←smul_neg]
 unfold lightKet; rw [Apron.pivot_cons,map_smul,inner_smul_left,inner_smul_right,mul_assoc]
lemma grid_sparkle(s:ℕ)(l t:List Axis)(p q:Vantage)
  (h:P.faceWidth s < (P.roundPose q s-P.roundPose p s) 3/2)
  (a:∀ k:Axis,P.faceWidth s < |(P.roundPose q s-P.roundPose p s) k|/2):
  P.sparkle x s l t (P.roundPose q s-P.roundPose p s)= P.paidPix x s (P.pix t q s) (P.pix l p s):= by
 let y:=P.tap p s; let z:=P.tap q s; let u:=P.gridSpot s y; let v:=P.gridSpot s z
 let g:= v-u; let d:=P.roundPose q s-P.roundPose p s
 have hv:(D s) • d = g:=by
    change _=P.meshPose s (P.tap q s)-P.meshPose s (P.tap p s)
    rw [P.tap_scale,P.tap_scale]; exact smul_sub ..
 let L₀:=ord₂; let f:=U% s l t; let r₀:=usher u v
 let w:=P.lengthP s * P.faceWidth s
 have price(k:Axis)(b:d k/2>P.faceWidth s): w+w< v k - u k:= by
    change _ < g k
    rw [←hv, Pi.smul_apply,smul_eq_mul]; unfold w; have h':= mul_lt_mul_of_pos_left b (P.lengthP_pos s); linarith only [h']

 have left (k:Axis)(b:d k/2>P.faceWidth s):P.Turnstile k f L₀ r₀:= List.pairwise_pair.mpr (show u k+(St s l).realWidth P k<v k-(St s t).realWidth P k from by rw [P.width_face,P.width_face]; unfold w at price; linarith only [price k b])
 have both: P.Plenum f L₀ r₀:= by
    constructor; intro k; have hz:P.faceWidth s < |d k|/2:=a k
    rcases le_total 0 (d k) with he|he
    · rw [abs_of_nonneg he] at hz; exact ⟨_,List.Perm.refl _,left k hz⟩
    rw [abs_of_nonpos he] at hz; have hq:w+w<u k-v k:= by
       rw [← neg_sub]; change _< -g k; rw [←hv, Pi.smul_apply, smul_eq_mul]; unfold w; have h':= mul_lt_mul_of_pos_left hz (P.lengthP_pos s); linarith only [h']
    exact ⟨[true,false],List.Perm.swap .., List.pairwise_pair.mpr (show v k+(St s t).realWidth P k<u k-(St s l).realWidth P k from by rw [P.width_face,P.width_face]; unfold w at hq; linarith only [hq])⟩
 have hx:P.gridSpot s ∘ usher y z=r₀:= by funext i; cases i <;> rfl
 have ht:=P.spot_full x f L₀ (usher y z) J s (fun b _=> by cases b <;> exact (Apron.pivot_s P _ _).le) (hx.symm ▸ left 3 h) (hx.symm ▸ both)

 have he:P.fullScroll s f (usher y z) L₀=P.centeredQ x s (P.pix l p s)*P.centeredQ x s (P.pix t q s):= by
    change P.issuing s (St s l) y* (P.issuing s (St s t) z*1)=_
    rw [mul_one, P.scene_issue x s l p, P.scene_issue x s t q]
 rw [hx, he] at ht
 let b : r₀ ∈ P.Federation f L₀:= ⟨3,L₀,List.Perm.refl _,left 3 h⟩
 have hz: settler r₀ (-u) = usher 0 g:= by funext i; cases i; exact neg_add_cancel u; exact neg_add_eq_sub u v
 unfold paidPix; rw [ht]
 unfold sparkle; change _ * (Ch) f (usher 0 ((D s) • d)) L₀=_
 rw [hv,← hz,(P.common_shift 3 x f r₀ L₀ J b (-u)).2]

abbrev castAway(n:ℕ):Vantage:=spl n - spl 0
omit J
lemma cast_dense:DenseRange castAway:= by
 suffices h: Function.Surjective (fun y:Vantage=>y-spl 0) from h.denseRange.comp spl_dense (continuous_id'.sub continuous_const)
 exact fun y=> ⟨_,add_sub_cancel_right y (spl 0)⟩
abbrev candle (n s:ℕ):= P.roundPose (spl n) s-P.roundPose (spl 0) s
lemma candle_t (n:ℕ):Tendsto (P.candle n) atTop (𝓝 (castAway n)):= (P.tap_t _).sub (P.tap_t _)
include J H τ
lemma candle_price (l t:List Axis)(n:ℕ)(q: 0<castAway n 3)(a:∀k,castAway n k ≠ 0):
 Tendsto (fun i=>P.sparkle x (r i) l t (P.candle n (r i))) atTop (𝓝 (gloss (castAway n))):= by
 have h: spl n≠ spl 0:=fun h=> by unfold castAway at q; rw [h,sub_self] at q; exact (lt_irrefl (0:ℝ) q).elim
 let d:= castAway n; let y(i):=P.candle n (r i)
 have hy:= tendsto_pi_nhds.mp ((P.candle_t n).comp τ)
 have z:∀ᶠ i in atTop,P.faceWidth (r i) < y i 3/2:= (P.face_t.comp τ).eventually_lt ((hy _).div_const 2) (half_pos q)
 have e:∀ᶠ i in atTop,∀ k, P.faceWidth (r i)< |y i k|/2:= eventually_all.mpr fun k=>(P.face_t.comp τ).eventually_lt ((hy k).abs.div_const 2) (half_pos (abs_pos.mpr (a k)))

 refine (P.paid_sight H τ (n,t,none) (0,l,none) h).congr' ?_
 filter_upwards [z,e] with i c v; exact (P.grid_sparkle x J (r i) l t _ _ c v).symm
