import GaugeFieldConstruction.JadeSkyRP
/-! propagation of vanishing at neighborhood of translated configurations. Tiny factors. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.NSF.Boundary
open YM.Boundary Function Mink Set Filter MeasureTheory Analysis Distribution LD Bid Work.C22 Work.C23 Work.C24 OS Small Complex Metric Poincare
open scoped BigOperators Topology ContDiff InnerProductSpace NNReal
variable {n m:ℕ}{G:Gauge}{L:Register G}{S T:Table L}{C:LRoom T timeAxis}
variable {B:Small S C}{p q:ℝ≥0}{F:Waves S}{K:Spins S}{W:Surface S}{J:StarOp S}{D:∀ i,Blanket i}{R:S.Rotation}{s:S.RealSpin}
variable (d:PredictionL W F K J B R s){X:W.Aurora D}(H:X.FullBody F)(b: Hull B F J)
variable (v:Fin n→ Letter S)(w:Fin m→ Letter S)
local notation "${Y}"=> d.system.operators
local notation "${T}"=> d.system.action
local notation "${K}"=> d.system.spin
local notation "P"=> d.course.covariance
-- use exact labels translated tests
lemma goTowerRP (t:Sentence S)(p:Poincare): ${T}.V p (${Y}.vector t)= ${Y}.vector (${K}.po p t):=by
 induction t with
 | nil=> exact (P).vacuum p
 | cons x z ih =>
   change ${T}.V p (${Y}.field x.1 x.2 (${Y}.evaluates z)).val = (${Y}.field (${K}.rail p.Λ x.1) (Joint.push p x.2) _).val
   rw[(P).covariance]; exact congrArg (fun q:${Y}.domain=> (${Y}.field (${K}.rail p.Λ x.1) (Joint.push p x.2) q).val) (Subtype.ext ih)
lemma twistTowerRP (p:Lorentz)(x:Points n): forwardRP (Letter.read ${K} (motion p) ∘ v) (togetherL p n x)= Letter.read ${K} (motion p) ∘ forwardRP v x:=by
 ext1 i; refine Prod.ext rfl ?_; ext1 t; simp [forwardRP,Letter.read,Poincare.motion]
lemma towerTrodRP (p:Lorentz)(x:Points n): ${T}.V (motion p) (${Y}.vector (List.ofFn (forwardRP v x)))= ${Y}.vector (List.ofFn (forwardRP (Letter.read ${K} (motion p) ∘ v) (togetherL p n x))):=by
 rw [goTowerRP]; simp [Spins.po,twistTowerRP]
def dingRP (v:Fin n→ Letter S)(u:d.system.operators.H)(x:Points n):ℂ:= inner ℂ u (${Y}.vector (List.ofFn (forwardRP v x)))
def loudRP (v:Fin n→ Letter S)(u:d.system.operators.H): Set (Points n):= {x| dingRP d v u =ᶠ[𝓝 x] 0}
lemma speakTrodRP (x y:Points n):forwardRP (forwardRP v x) y=forwardRP v (x+y):=by ext1 i; refine Prod.ext rfl ?_; ext1 t; simp [forwardRP,sub_sub,add_comm]
variable (Ωv: d.system.operators.H)
lemma depthOpenRP:IsOpen (loudRP d v Ωv):=by
 apply isOpen_iff_mem_nhds.mpr; intro x p; exact eventually_eventually_nhds.mpr p
lemma soundsAtRP (x:Points n)(h:x∈loudRP d v Ωv): dingRP d v Ωv x=0:=by change dingRP d v Ωv x=(0: Points n→ ℂ) x; exact Eventually.self_of_nhds (p:=fun i=>dingRP d v Ωv i=(0:Points n→ℂ) i) (show dingRP d v Ωv =ᶠ[𝓝 x] 0 from h)
lemma readsTrodRP (p:Lorentz)(x:Points n): dingRP d (Letter.read ${K} (motion p) ∘ v) (${T}.V (motion p) Ωv) (togetherL p n x)=dingRP d v Ωv x:=by
 unfold dingRP; rw [← towerTrodRP]; exact LinearIsometry.inner_map_map (⟨(${T}.V (motion p)).toLinearMap,${T}.usual (motion p)⟩ : ${Y}.H →ₗᵢ[ℂ] ${Y}.H) _ _
lemma loudTrodRP (p:Lorentz)(x:Points n): togetherL p n x∈ loudRP d (Letter.read ${K} (motion p) ∘ v) (${T}.V (motion p) Ωv) ↔ x∈ loudRP d v Ωv:=by
 let e:=togetherL p n; have he: Filter.map e (𝓝 x)=𝓝 (e x):= e.toHomeomorph.map_nhds_eq _
 unfold loudRP; simp only [mem_setOf]; rw [← he,eventuallyEq_map]; simp only [Function.comp_def,e]; change ((fun x=>dingRP d (Letter.read ${K} (motion p) ∘ v) (${T}.V (motion p) Ωv) (togetherL p n x)) =ᶠ[𝓝 x] 0)↔ _; simp only [readsTrodRP]
variable (x:Points n){a:Heights n}(e:a∈positiveHeight n)
include H b e
lemma tackFootRP (h:x∈loudRP d v Ωv)(r:ℝ):dingRP d v Ωv (x+r • dawn a)=0:=by
 have hp:= (show dingRP d v Ωv =ᶠ[𝓝 x] 0 from h)
 unfold dingRP; rw[← speakTrodRP]
 apply FrostFillRP d H b _ e
 have hc:Tendsto (fun r:ℝ=>x+r • dawn a) (𝓝 0) (𝓝 x):=by simpa using (show Continuous (fun r:ℝ=>x+r • dawn a) from continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
 filter_upwards [hc.eventually hp] with t p; rw [speakTrodRP]; exact p
lemma tackLoudRP (h:x∈ loudRP d v Ωv)(r:ℝ): x+r • dawn a∈ loudRP d v Ωv:=by
 let f:= r • dawn a; unfold loudRP; refine Eventually.mono ?_ (fun i (t:i-f∈loudRP d v Ωv)=> ?_)
 · have hc:Tendsto (fun i:Points n=> i-f) (𝓝 (x+f)) (𝓝 x):=by simpa using (show Continuous (fun i:Points n=> i-f) from continuous_id.sub continuous_const).tendsto (x+f)
   exact hc.eventually ((depthOpenRP d v Ωv).mem_nhds h)
 · simpa only [f,sub_add_cancel,Pi.zero_apply] using tackFootRP d H b v Ωv (i-f) e t r
lemma tackBoostRP (h:x∈ loudRP d v Ωv)(p:Lorentz)(r:ℝ):x+ r • togetherL p n (dawn a)∈ loudRP d v Ωv:=by
 rw [← loudTrodRP _ _ _ p⁻¹]; rw [map_add,map_smul]
 rw [show togetherL p⁻¹ n (togetherL p n (dawn a))=dawn a by ext i; simp]
 exact tackLoudRP d H b _ _ _ e ((loudTrodRP d v Ωv p⁻¹ _).2 h) r
#print axioms tackBoostRP
end YM.NSF.Boundary
end
