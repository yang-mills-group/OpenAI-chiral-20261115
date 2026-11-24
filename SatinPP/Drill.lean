import SatinPP.Bastille
import SatinPP.Terps
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

local notation "Lk" s:max l:max=>P.lightKet x j s l
variable (J:P.Ellis 3 x){r:ℕ→ℕ}(H:P.Spots r x)(τ:Tendsto r atTop atTop)
include J H τ
local notation "K" l:max g:max i:max=> P.sparkle x (r i) l g
lemma tapestry (l g:List Axis){p:ℕ→ Vantage}{d: Vantage}(y:Tendsto p atTop (𝓝 d))(e:0<d 3)(a:∀ k,d k≠0):
  Tendsto (fun i=>(K l g i) (p i)) atTop (𝓝 (gloss d)):= by
 apply Metric.tendsto_nhds.mpr; intro ε h; have h₀:= show 0<ε/4 from by positivity
 obtain ⟨N,u,v⟩:=P.parchment x J l g H τ a h₀
 have hd:d≠0:= fun y=>(a 0 (congrFun y _))
 have ha: {w:Vantage|∀ j,w j≠0}∈𝓝 d:= eventually_all.mpr fun k=> ((continuous_apply k).continuousAt.tendsto.eventually (eventually_ne_nhds (a k)))
 have he:{w:Vantage|0<w 3}∈𝓝 d:= (continuous_apply _).continuousAt.preimage_mem_nhds (Ioi_mem_nhds e)

 obtain ⟨O,hf,w,q⟩:=_root_.mem_nhds_iff.mp (inter_mem (inter_mem (inter_mem u ha) he) ((joyous d hd).preimage_mem_nhds (ball_mem_nhds _ h₀)))
 obtain ⟨n,b⟩:=cast_dense.exists_mem_open w ⟨_,q⟩
 obtain ⟨⟨⟨_,z⟩,f⟩,t⟩:=hf b
 have hg:N∈𝓝 (castAway n):=mem_of_superset (w.mem_nhds b) fun p h=> (hf h).1.1.1
 have hx:=P.candle_price x H τ J l g n f z -- args?
 have hy:= (P.candle_t n).comp τ
 filter_upwards [y.eventually u,hy.eventually hg,v,Metric.tendsto_nhds.mp hx _ h₀] with i p₀ pc h₁ h₂
 exact lt_of_le_of_lt (dist_triangle4 _ _ _ _)
    (lt_of_le_of_lt (add_le_add (add_le_add (h₁ _ p₀ _ pc) h₂.le) (Metric.mem_ball.mp t).le)
     (by linarith only [h]))
omit J H τ in
lemma gloss_neg {p:Vantage}(e:p≠0):gloss (-p)=gloss p:=by
 rw [heyday _ (neg_ne_zero.mpr e),heyday _ e]
 simp only [pth,tilt, Pi.neg_apply]; congr 1 <;> ring
lemma away_p (l g:List Axis){p:ℕ→ Vantage}{d: Vantage}(y:Tendsto p atTop (𝓝 d))(a:∀ k,d k≠0):
  Tendsto (fun i=>(K l g i) (p i)) atTop (𝓝 (gloss d)):= by
 rcases lt_or_gt_of_ne (a 3) with v|v; swap; · exact P.tapestry x J H τ l g y v a
 have e:d≠0:=fun t=> a 3 (congrFun t _)
 have h:0< (-d) 3:= neg_pos.mpr v
 have ht:= P.tapestry x J H τ g l y.neg h (fun k=> neg_ne_zero.mpr (a k))
 rw [gloss_neg e] at ht
 refine ht.congr' ?_
 filter_upwards [(P.face_t.comp τ).eventually_lt ((tendsto_pi_nhds.mp y.neg 3).div_const 2) (half_pos h)] with i p₀
 rw [P.sparkle_minus x 3 J _ l g _ p₀] -- h needs opposite sign! minus spark x s l g p

omit J H τ in
private lemma twinkle (A:P.Apron): glareY x A j=flashY x (A.kiss P j) j:=by
 unfold glareY flashY; rw [P.lives_twin,P.tableMaps,show mirrorΩ j (0:Vantage)=0 from (by funext i; by_cases h:i=j<;> simp [mirrorΩ,h]), P.cart_zero]; rfl
omit J H τ in
lemma match_light (s:ℕ)(t:ℝ)(l:List Axis) : (Lk s (j::j::l)) t=(Lk s l) t:=by
 unfold lightKet; rw [Apron.pivot_cons,Apron.pivot_cons,beam,beam,Apron.kiss_width,Apron.kiss_width,← P.twinkle,flashY_glare]
variable (l:List Axis)
local notation "Υ"=> aglow j
omit J H τ in
def starLane (y:Vantage)(t:ℝ): Vantage:=Function.update y j t
local notation "posn"=>starLane j
local notation "Φ" i:max l:max=> P.lightKet x j (r i) l
omit J H τ in
lemma lane_j(y:Vantage)(t:ℝ):posn y t j=t:= by simp [starLane]
omit J H τ in
lemma lane_side(y:Vantage)(t:ℝ){k:Axis}(p:k≠j):posn y t k=y k:= by simp [starLane,p]

omit J H τ in
lemma lanes {α:Type*}{ρ:Filter α}{u:α→ Vantage}{v:α→ℝ}{y:Vantage}{z:ℝ}(p:Tendsto u ρ (𝓝 y))(t:Tendsto v ρ (𝓝 z)):
 Tendsto (fun i=>posn (u i) (v i)) ρ (𝓝 (posn y z)):= (continuous_update j|>.continuousAt.tendsto).comp (p.prodMk_nhds t)
omit J H τ in
lemma lane_nz (y:Vantage){a:ℝ}(p:a≠0) : posn y a ≠0:= fun h=> p ((lane_j j y a).symm.trans (congrFun h j))
omit J H τ in
lemma lane_cart (d:ℝ)(u:Vantage)(t:ℝ): Γ (d • posn u t)=Γ (d • u):= P.cart_j x j _ _ <|fun k e=>by rw [Pi.smul_apply,Pi.smul_apply,lane_side j u t e]
variable {t:ℕ→ℝ}{z:ℝ}(p:Tendsto t atTop (𝓝 z))(v:0<z)
include p v
local notation "Δ" i:max g:max=> ((Φ i g) (t i))

local notation "A#" k:max=>D (r k)
lemma good_light (g:List Axis){y:ℕ→ Vantage}{d:Vantage}(h:Tendsto y atTop (𝓝 d))(e:∀ k≠j,d k≠0):
 Tendsto (fun i=>inner ℂ (Δ i l) (Γ ((A# i) • y i) (Δ i g))) atTop (𝓝 (gloss (posn d (z+z)))):= by
 have ht:∀ k,posn d (z+z) k≠0:=by
    intro k;by_cases c:k=j
    · subst k;rw [lane_j];linarith only [v]
    rw [lane_side j _ _ c]; exact e k c
 let w i:=posn (y i) (t i+t i)
 refine (P.away_p x J H τ (j::l) g (lanes j h (p.add p)) ht).congr' ?_
 filter_upwards [(P.face_t.comp τ).eventually_lt p v] with i u
 have hz:w i j/2=t i:=by unfold w; rw [lane_j];ring
 rw [P.sparkle_plus x j J (r i) _ _ (w i) (u.trans_eq hz.symm),hz,P.match_light]
 unfold w; rw [P.lane_cart]

omit J in
lemma upper_light {δ:ℝ}(h:0<δ): ∀ᶠ i in atTop, ‖(Δ i l)‖^2 ≤ (gloss (posn 0 (z+z))).re + δ:=by
 let w(a:ℝ):= (gloss (posn 0 (a+a))).re
 have y: Tendsto w (𝓝 z) (𝓝 (w z)):= Complex.continuous_re.continuousAt.tendsto.comp ((joyous _ (lane_nz j 0 (show z+z≠0 by linarith))).tendsto.comp (lanes j tendsto_const_nhds (tendsto_id.add tendsto_id)))
 obtain ⟨r',q,x'⟩:= Metric.mem_nhds_iff.mp (y.eventually (gt_mem_nhds (lt_add_of_pos_right _ (half_pos h))))
 let b:=z-min r' z; have hm:b<z:= sub_lt_self _ (lt_min q v)
 obtain ⟨n,h₁,h₂⟩:=spl_dense.exists_mem_open (s:={x:Vantage| x j ∈ Set.Ioo b z})
      (isOpen_Ioo.preimage (continuous_apply (A:=fun _:Axis=>ℝ) j)) ⟨fun _=>(b+z)/2,(by apply left_lt_add_div_two.mpr hm),add_div_two_lt_right.mpr hm⟩

 let a:=spl n j; have hv:0<spl n j:=lt_of_le_of_lt (sub_nonneg.mpr (min_le_right _ _)) h₁
 have d:a∈ball z r':= by
    rw [mem_ball,Real.dist_eq,abs_of_neg (sub_neg.mpr h₂)]; change z-min r' z < a at h₁
    linarith only [h₁,min_le_left r' z]
 let b':=(a+z)/2
 have he:(spl n)-opposeR j (spl n)=posn 0 (a+a):= by
    ext k; by_cases t:k=j
    · subst k; rw [lane_j,Pi.sub_apply, show opposeR j (spl n) j= -a from if_pos rfl]; unfold a; ring
    rw [lane_side j _ _ t,Pi.zero_apply,Pi.sub_apply,show opposeR j (spl n) k=spl n k from if_neg t,sub_self]
 have h' : a<z:=h₂
 have T: w a < w z + δ/2:=x' d
 filter_upwards [P.enough_ties x j H τ l n hv (show a<b' by unfold b';linarith) (half_pos h), p.eventually (le_mem_nhds (show b'<z by unfold b';linarith))] with i c e; specialize c (t i) e
 rw [he] at c; change _≤ w a + δ/2 at c; change _≤ w z + δ; linarith
private lemma prep_closeness {b:Vantage}{ε:ℝ}(k:0<ε)(d:∀ i≠j,b i≠0)
    (e:(gloss (posn 0 (z+z))).re < (gloss (posn b (z+z))).re + ε^2/8):
 ∀ᶠ i in atTop, ‖(Δ i l)-Γ ((A# i) • b) (Δ i l)‖ ≤ ε:= by
 have h:= P.good_light x j J H τ l p v l (tendsto_const_nhds (x:=b)) d -- args
 let c:=ε^2/8; have u:0<c:= by unfold c;positivity
 let w(y):=(gloss (posn y (z+z))).re
 filter_upwards [(Complex.continuous_re.continuousAt.tendsto.comp h).eventually (le_mem_nhds (show w b-c<w b from sub_lt_self _ u)), P.upper_light x j H τ l p v u] with i h₁ h₂
 apply (sq_le_sq₀ (norm_nonneg _) k.le).mp
 rw [norm_sub_sq (𝕜:=ℂ),P.cart_norm]
 let Y:=Δ i l; let W:=Γ ((A# i) • b)
 change w b-c ≤ (inner ℂ Y (W Y)).re at h₁;change w 0 < w b+c at e;change ‖Y‖^2≤w 0+c at h₂
 change ‖Y‖^2- 2*(inner ℂ Y (W Y)).re+‖Y‖^2≤_
 unfold c at h₁ h₂ e; linarith only [h₁,h₂,e,sq_nonneg ε]

omit J H τ p in
lemma hush (d:Vantage) (ε δ:ℝ)(e:0<ε)(a:0<δ):
 ∃ b: Vantage, (∀k≠ j,b k ≠ 0)∧(∀k≠j,(d+b) k ≠0)∧
 (gloss (posn 0 (z+z))).re < (gloss (posn b (z+z))).re +δ ∧
 dist (gloss (posn (d+b) (z+z))) (gloss (posn d (z+z))) < ε:=by
 let f(y):=gloss (posn y (z+z))
 have h(y): ContinuousAt f y:= (joyous _ (lane_nz j y (ne_of_gt (add_pos v v)))).tendsto.comp ((lanes j (y:=y) tendsto_id (tendsto_const_nhds (x:=z+z))))
 let b(w:ℝ): Vantage:= fun _=>w
 let α:= 𝓝[>] (0:ℝ)
 have hw:Tendsto b α (𝓝 (0:Vantage)):= tendsto_pi_nhds.mpr fun _=> tendsto_id.mono_left nhdsWithin_le_nhds -- wrong

 have wn:Tendsto (fun w=>d+b w) α (𝓝 d):= by simpa only [add_zero] using hw.const_add d
 have hg:∀ᶠ w in α,0<w :=self_mem_nhdsWithin
 have hc:∀ᶠ w in α,∀ i,(d+b w) i≠0:=by
    apply eventually_all.mpr; intro i; by_cases q:d i=0; · filter_upwards [hg] with w p; rw [Pi.add_apply,q,zero_add];exact p.ne'
    exact (tendsto_pi_nhds.mp wn i).eventually (eventually_ne_nhds q)
 have hs: Tendsto (fun w=>(f (b w)).re+δ) α (𝓝 ((f 0).re+δ)):= (Complex.continuous_re.continuousAt.tendsto.comp ((h 0).tendsto.comp hw)).add_const δ
 obtain ⟨w,hw,hc,ht,hx⟩:= (hg.and (hc.and ((hs.eventually (lt_mem_nhds (lt_add_of_pos_right _ a))).and (Metric.tendsto_nhds.mp ((h d).tendsto.comp wn) _ e)))).exists
 exact ⟨b w,fun _ _=>hw.ne',fun i _=>hc i,ht,hx⟩
lemma all_light (g:List Axis){y:ℕ→ Vantage}{d:Vantage}(h:Tendsto y atTop (𝓝 d)):
 Tendsto (fun i=>inner ℂ (Δ i l) (Γ ((A# i) • y i) (Δ i g))) atTop (𝓝 (gloss (posn d (z+z)))):= by
 apply Metric.tendsto_nhds.mpr;intro ε e
 obtain ⟨C,h₁,F⟩:= P.rough_bound x j H τ l (half_pos v)
 let a:=ε/4; let L:=a/C; have a0:0<a:=by unfold a;positivity
 have L0:0<L:=div_pos a0 h₁
 obtain ⟨b,h₂,h₃,h₄,h₅⟩:=hush j v d a (L^2/8) a0 (by positivity)
 have ha:= P.good_light x j J H τ l p v g (h.add_const b) h₃
 have he:= P.prep_closeness x j J H τ g p v L0 h₂ h₄
 filter_upwards [Metric.tendsto_nhds.mp ha _ a0, F,p.eventually (le_mem_nhds (half_lt_self v)),he] with i Y Z m q
 let y₀:=Δ i g; let y₁:=Δ i l
 let R(x:Vantage):= Γ ((A# i) • x)

 have h': dist (inner ℂ y₁ (R (y i) y₀)) (inner ℂ y₁ (R (y i+b) y₀)) ≤ a:=by
    rw [dist_eq_norm,←inner_sub_right]
    rw [show R (y i+b)=R (y i)*R b from (by unfold R; rw [smul_add,P.cart_paves];rfl),ContinuousLinearMap.mul_apply,←map_sub]
    refine (norm_inner_le_norm ..).trans ?_; unfold R;rw [P.cart_norm]
    exact (mul_le_mul (Z _ m) q (norm_nonneg _) h₁.le).trans_eq (mul_div_cancel₀ _ h₁.ne')
 exact lt_of_le_of_lt (dist_triangle4 _ _ _ _) (lt_of_le_of_lt (add_le_add (add_le_add h' Y.le) h₅.le) (by unfold a;linarith))

omit J H τ p v
lemma bracket_scale (a:ℕ)(g:List Axis){t₁ t₂:ℝ}(h:P.faceWidth a ≤ t₁)(q:P.faceWidth a ≤ t₂)(y:Vantage):
  inner ℂ ((Lk a l) t₁) (Γ y ((Lk a g) t₂)) =
  inner ℂ ((Lk a l) ((t₁+t₂)/2)) (Γ y ((Lk a g) ((t₁+t₂)/2))):= by
 let b:=P.faceWidth a; have hp:b ≤ _:= h; have ht:b ≤ _:=q; let t':=(t₁+t₂)/2; have L:b≤t':=by unfold t';linarith only [hp,ht]
 rw [P.lamplight x j a l le_rfl L,P.lamplight x j a g le_rfl L,P.lamplight x j a l le_rfl h,P.lamplight x j a g le_rfl q] -- test rw hits wrong?
 let f(s:ℝ):= ((D a)*(s-b)).toNNReal
 have hu:f t'+f t'=f t₁+f t₂:=by
    have ha(s:ℝ)(e:b≤ s):0≤(D a)*(s-b):=mul_nonneg (P.lengthP_pos a).le (sub_nonneg.mpr e)
    unfold f t'; rw [←Real.toNNReal_add (ha _ L) (ha _ L),←Real.toNNReal_add (ha _ h) (ha _ q)]
    congr 1;ring
 rw [←P.warm_drive,←P.warm_drive,beam_join,beam_join]
 change inner ℂ _ ((E (f t₁+f t₂)) _) = _ 
 rw [← hu]

include J H τ p v
lemma crystal (g:List Axis){y:ℕ→ Vantage}{d:Vantage}(h:Tendsto y atTop (𝓝 d))
 {t₁:ℕ→ℝ}{u:ℝ}(w:Tendsto t₁ atTop (𝓝 u))(q:0<u) :
 Tendsto (fun i=>inner ℂ (Δ i l) (Γ ((A# i) • y i) ((Φ i g) (t₁ i)))) atTop (𝓝 (gloss (posn d (z+u)))):= by
 have W:= P.all_light x j J H τ l ((p.add w).div_const 2) (half_pos (add_pos v q)) g h
 rw [add_halves] at W
 refine W.congr' ?_
 filter_upwards [(P.face_t.comp τ).eventually_lt p v, (P.face_t.comp τ).eventually_lt w q] with i p₀ q₀
 exact (P.bracket_scale x j l (r i) g p₀.le q₀.le _).symm

