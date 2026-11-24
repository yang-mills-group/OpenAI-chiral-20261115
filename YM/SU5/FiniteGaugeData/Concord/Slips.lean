import YM.SU5.FiniteGaugeData.Concord.BannerWord
import YM.SU5.FiniteGaugeData.Concord.SeamFoot
/-! # Issued palette & microscopic realizations of the fixed-state OS candidates. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical TensorProduct ComplexConjugate
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Heat
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
namespace Banner
open Bilinear
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
variable {i k:ℕ→ℕ}(W:Traced Y H i k F E P)
variable (s n d:ℕ)
variable (x:junior (tent Y H))

structure Pledge (K: Calibration)(x:junior K)(c:ℝ) :Prop where
 house : x∈ club K (zone K)
 color : x∈singlets K
 pay (m:Side)(v:Fields (K.c m)): ‖x.val m v‖ ≤ c

lemma pledge_bulb (K:Calibration): Pledge K (bulb K) (5*(K.vertex:ℝ)^3):= ⟨lodge K _ subset_union_right (bulb_b K),bulb_color K,heart_norm K⟩ -- K notation parse? replace
lemma pledge_center (K:Calibration) (x:ℂ): Pledge K (center K x) (voice K x) := ⟨center_heart K x,center_color K x,beacon K x⟩
lemma pledge_reflected (K:Calibration)(x:ℂ) : Pledge K (turn K 3 K.plane0 (center K x)) (voice K x):= ⟨center_ref K x,turn_gauge 3 K.plane0 (center_color K x),fun m v=> blade_bound 3 K.plane0 m (beacon K x m) v⟩
lemma pledge_echo (K:Calibration)(x y:ℂ): Pledge K (centered_echo K x y) (voice K x*voice K y):= ⟨echo_house K x y,echo_color K x y,beacon_echo K x y⟩

local notation "K"=> tent Y H
local notation "πt" => portfolio Y H W
local notation "Ω" => ConeFilter Y i k
local notation "θb" => turn (tent Y H) 3 (K).plane0
local notation "U"=> wing (tent Y H) 3 (K).plane0 (K).ℓ

local notation "S₀"=> zone (tent Y H)


-- eventually large at all periods on the course (one resolution)
def Land (m: Side):Prop:= (let Q:Side:=(tent Y H).c m; Hosp (zone K) Q ∧ 2*(2*(K).vertex)≤(More Q).val ∧ region (Bilinear.support K) Q⊆ band Q (3:Axis) (K).plane0 (K).ℓ)
lemma landing : ∀ᶠ n in atTop,Land Y H (momentm Y n s):= by
 apply (momentum Y s).eventually; filter_upwards [suitable S₀ K,(c_grows (tent Y H)).eventually_ge_atTop (4*(K).vertex), hosted (tent Y H) 3 (K).plane0 (K).ℓ (situated (tent Y H)).1] with m d h v
 refine ⟨d,?_ ,v⟩; change 4*(tent Y H).vertex ≤ ((tent Y H).c m).val at h; change _≤ ((tent Y H).c m).val*2; omega

local notation "ν"=>side Y n s
lemma located (p:Land Y H (momentm Y n s)) :
    Hosp (zone (tent Y H)) (side Y n s) ∧ region (Bilinear.support (tent Y H)) (side Y n s)⊆ band (side Y n s) (3:Axis) (K).plane0 (K).ℓ ∧
    separation (wrap (More (side Y n s)) (nodeC creatorSite)) (wrap (More (side Y n s)) (nodeC (removerSite K)))=2*(K).vertex := by
 let Q(m:Side):= Hosp (zone K) m ∧ region (Bilinear.support K) m ⊆ band m (3:Axis) (K).plane0 (K).ℓ ∧ separation (wrap (More m) (nodeC creatorSite)) (wrap (More m) (nodeC (removerSite K)))=2*(K).vertex
 exact Eq.mp (congrArg Q (terrain Y H (Y.ir n) s)) (show Q ((K).c _) from ⟨p.1,p.2.2,leg (tent Y H) _ p.2.1⟩)

abbrev sample (x:junior (tent Y H)): ℂ:= Journey.sharp Y H s n d x.val
lemma sample_script : sample Y H s n d x=Journey.compass Y n d s (observe Y H n s x.val):= rfl
lemma sample_port (p:(Y.voyage n).kick≤d)(v:s ≤ Y.uv d): sample Y H s n d x= reader Y H n d s W ((cameo Y H s x).val):=by
 change _=compass _ _ _ _ (realizeStage _ _ _ _ _ W (Style.stepFactor s x)).val; rw [stage_cameo Y H n d s W x p v]; rfl

variable {c:ℝ}(p:Pledge (tent Y H) x c)
local notation "fee"=> (local_cost Y H s (zone K)).choose
include p
lemma polish_price : ‖polish K (zone K) x p.house‖ ≤ c :=by
 obtain ⟨m,h⟩:= (suitable (zone K) K).exists; have he:= congrArg Subtype.val (polish_eq (tent Y H) (zone K) x p.house); apply palette_norm _ _ h; exact fun z=> (congrArg (fun i:junior K => ‖i.val m z‖) (polish_eq (tent Y H) (zone K) x p.house)).trans_le (p.pay ..) -- tc

local notation "δ"=> cameo Y H s x
local notation "tQ"=> Y.uv d
lemma burned : observe Y H n s x.val = nativeHere Y H n s (zone K) (polish K (zone K) x p.house):=by
 have ht:pigment (zone K) K (polish K _ x p.house)=x.val:= congrArg Subtype.val (polish_eq ..)
 rw [nativeHere_eq,ht]

lemma scrip (a:(Y.voyage n).kick ≤ d)(v:s ≤ Y.uv d):
    (cameo Y H s x).val∈limited (fun _=> singlets K) s ∧ (cameo Y H s x).val∈ physical (tent Y H) ∧
    let f:= δ; let g:= (realizeStage Y H n d s W f.val).val; let z:= realizeStage Y H n d (Y.uv d) W f.val
    g=observe Y H n s x.val ∧ AtSupport false (region (zone K) (side Y n s)) g ∧ (∀ x,‖g x‖≤c) ∧
    AtSupport false (region (area Λ l (zone K) ((Y.uv d)-s)) (side Y n (Y.uv d))) z.val ∧
    covariant z.val ∧ (∀ y,‖z.val y‖≤ winch Y s n d (Y.uv d-s)*c) ∧ reader Y H n d (Y.uv d) W f.val=sample Y H s n d x:=by
 let F:= realizeStage Y H n d s W (Style.stepFactor s x)
 let m:=Y.uv d; have hk: s+(Y.uv d-s)=Y.uv d:=by omega
 have ht : (cameo Y H s x).val∈limited (fun _=>singlets K) s:= resident (fun _=>singlets K) s x p.color
 have He: (δ).val∈Style.atLeast s:=Style.stepAt s x -- notation (δ).val issue
 have h:F.val=observe Y H n s x.val:=congrArg Subtype.val (stage_cameo Y H n d s W x a v)
 have hg:AtSupport false (region (zone K) (ν)) F.val:= h.symm ▸ observe_support Y H n s (show InTest K true (zone K) false x.val from p.house)
 have hv: ∀ i, ‖F.val i‖ ≤ c:=by rw [h,observe_formula]; exact (Copies.constantCost ..).mpr (p.pay (momentm Y n s)) -- order
 have hz:= scenic_wind Y H W s n d (zone K) He hg a c hv (m-s) hk.le; unfold m at hz; rw [hk] at hz
 refine ⟨ht, Style.to_pub _ _ ht, h,hg,hv,hz.1,currently_gauge Y H W (Y.uv d) n d (cameo Y H s x).val (Style.to_pepper _ v ht) a le_rfl,hz.2,?_⟩
 rw [sample_port Y H W s n d x a v]; exact (memorable Y H n d s W v He a le_rfl).symm

include W
omit p in
lemma placing : πt (cameo Y H s x) = E s x.val:= cameo_physical ..
lemma advert : ‖E s x.val‖ ≤ fee*c ∧ (∀ n:ℕ, ‖F s x.val n‖ ≤ fee*c) ∧ ∀ (n d:ℕ), Ready Y H (zone K) s n d→ ‖sample Y H s n d x‖≤ fee*c:=by
 let f:= polish K (zone K) x p.house
 have he(V:Music (zone K))(p':‖V‖ ≤ fee) : ‖V f‖ ≤ fee*c:= (V.le_of_opNorm_le p' _).trans (mul_le_mul_of_nonneg_left (polish_price Y H x p) (xcost ..))
 have hp:pigment (zone K) K f=x.val:=congrArg Subtype.val (polish_eq ..)
 refine ⟨hp ▸ he (finale Y H _ s W.own) (finale_cap ..),fun n=>?_,fun n d r=>?_⟩ -- hp ▸ cast?
 · rw [←hp]; exact he (gaugeEar Y H _ s W.own n) (fiscal ..)
 unfold sample; rw [←hp, ←sharply_s, ←onPitch Y H (zone K) s r]; exact he _ (critics ..)

omit p
local notation "Λm" n:max=>momentm Y n s

/-- Uniform support/stencil & center pledge propagation both ways, READY and interpretation prices. -/
theorem pledge_run :
    (∀ᶠ n in atTop,Land Y H (momentm Y n s) ∧ ∀ ε:ℝ, 0<ε→∀ᶠ j in atTop,
        Ready Y H (zone K) s n (k j) ∧∀ (x:junior (tent Y H))(c:ℝ), Pledge (tent Y H) x c→ ‖sample Y H s n (k j) x-F s x.val n‖ ≤ ε*c) ∧
    (∀ᶠ r in atTop, Land Y H (momentm Y (i r) s) ∧ ∀ (x:junior (tent Y H))(c:ℝ),Pledge (tent Y H) x c→
        ‖F s x.val (i r)-E s x.val‖≤ Meter r*c ∧ ∀ d,legacy Y (i r) (k d) → Ready Y H S₀ s (i r) (k d) ∧ ‖sample Y H s (i r) (k d) x-E s x.val‖≤ Meter r*c):=by
 constructor
 · filter_upwards [landing Y H s,(Satin.boutique Y H W.own S₀ s).1] with n e p
   refine ⟨e,fun ε h=>?_⟩; filter_upwards [p ε h,ready_row Y H S₀ s W.own n] with d h k; exact ⟨k,fun x c t=> h _ t.house _ e.1 _ (t.pay _)⟩
 filter_upwards [W.crimson S₀ s,W.own.pick.grow_i.tendsto_atTop.eventually (landing Y H s),meshed Y H S₀ s W] with r k v g
 exact ⟨v,fun x c t=>⟨(k.2 _ t.house _ (t.pay _)).1,fun d p=> ⟨(g.2 d p).1,(k.2 _ t.house _ (t.pay _)).2 d p⟩⟩⟩

lemma cone_sample : Tendsto (fun v:ℕ×ℕ=> sample Y H s (i v.1) (k v.2) x) (ConeFilter Y i k) (𝓝 (E s x.val)):= (ConeFilter.tendsto_iff_paths W.own.pick.grow_k).2 (W.own.together s x.val x.property).paths
end Banner
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.Banner.scrip
#print axioms YM.CF.Buffered.Concord.Banner.pledge_run
#print axioms YM.CF.Buffered.Concord.Banner.advert
