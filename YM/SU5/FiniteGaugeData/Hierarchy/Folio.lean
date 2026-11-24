import YM.SU5.FiniteGaugeData.Hierarchy.Lotus
/-! # thin the actual election (again, independent of Printed). Additional UV and IR choices made simultaneously, preserve all Universal receipts. Need the limits on identified rooms via `Solvent` and compare two-step prices in operator norm.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)

local notation "W₀"=> GridStep Λ l S
local notation "Pt"=> PaidPt Y S s
-- coupled iteration selection
abbrev Slip (Λ:Preparation)(l:ℕ)(S:Finset Cover) := Catalog S →L[ℂ] Catalog (GridStep Λ l S)
abbrev Wicket (Λ:Preparation)(l:ℕ) := (S:Finset Cover) → ℕ→ ℕ→ Slip Λ l S
abbrev Call (Λ:Preparation)(l:ℕ) := (S:Finset Cover) → ℕ→ Slip Λ l S
abbrev eligiblePath (f g:ℕ→ℕ)(w:ℕ→ℕ): Prop := ∀ᶠ t in atTop, legacy Y (f t) (g (w t))
open scoped Classical
def snag :Slip Λ l S:= if p: Offered Y S s i k then transitionQ Y h S s ⟨(i,k),p⟩ else 0

lemma snag_pay (p:Offered Y S s i k): snag Y h S s i k=transitionQ Y h S s ⟨(i,k),p⟩:= dif_pos p
lemma snag_size : ‖snag Y h S s i k‖ ≤ salary Y h S s := by unfold snag; split; exact transitionQ_budget ..; rw [norm_zero (E:=Slip Λ l S)]; exact salary_nn Y h S s

structure Rolled (u v:ℕ→ℕ)(J:Wicket Λ l)(P:Call Λ l):Prop where
  evening (S:Finset Cover) (s:ℕ): Couplet u v (snag Y h S s) (J S s) (P S s) (eligiblePath Y u v)

-- reusable tail patch
lemma path_budget {T:Type*}[PseudoMetricSpace T]{v w:ℕ→ℕ}{A:ℕ→ℕ→T}{z:T}(p:StrictMono w) (V:∀ k:ℕ→ℕ, eligiblePath Y v w k → Tendsto (fun i=>A (v i) (w (k i))) atTop (𝓝 z)) (ε:ℝ)(e:0<ε) :
    ∀ᶠ i in atTop,∀ k, legacy Y (v i) (w k)→ dist (A (v i) (w k)) z < ε := by
  have hp(i:ℕ): ∃ k,legacy Y (v i) (w k):= ((Y.uv_grows.comp p).tendsto_atTop.eventually_ge_atTop ((Y.ir (v i)).val^5)).exists
  let P(i k:ℕ):Prop:= legacy Y (v i) (w k) ∧ ε ≤ dist (A (v i) (w k)) z; let K(i:ℕ):=if h:∃ k,P i k then h.choose else (hp i).choose
  have W : eligiblePath Y v w K := Eventually.of_forall (fun i=> by
    unfold K; split
    next h=> exact h.choose_spec.1
    next => exact (hp i).choose_spec)
  filter_upwards [Metric.tendsto_nhds.mp (V K W) ε e] with i hi
  intro k h; by_contra! H; have hz:∃ k,P i k:=⟨k,h,H⟩; exact not_le.mpr hi (show _ ≤ _ from (Eq.subst (dif_pos hz).symm hz.choose_spec).2)
lemma eligible_exists (f g:ℕ→ℕ)(p:StrictMono g): ∃ v, eligiblePath Y f g v:=by
  choose k h using fun i=> ((Y.uv_grows.comp p).tendsto_atTop.eventually_ge_atTop ((Y.ir (f i)).val^5)).exists; exact ⟨k,Eventually.of_forall h⟩

section
variable {v w x y :ℕ→ℕ} (hw:StrictMono w) (p:StrictMono x)(t:StrictMono y)
include hw p t
lemma repeter {T:Type*}[PseudoMetricSpace T]{A:ℕ→ℕ→T}{J Z} (q: Couplet v w A J Z (eligiblePath Y v w)): Couplet (v∘x) (w ∘ y) A J Z (eligiblePath Y (v∘x) (w ∘ y)):= by
  refine ⟨fun i=> (q.inner i).comp t.tendsto_atTop, q.periods.comp p.tendsto_atTop,fun r a=>?_⟩
  refine Metric.tendsto_nhds.mpr fun ε e=>?_
  filter_upwards [p.tendsto_atTop.eventually (path_budget Y hw q.paths ε e),a] with i b c using b (y (r i)) c
omit hw
variable {I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}(K:Universal Y h v w I E)
include K
lemma uni_roll : Universal Y h (v ∘ x) (w ∘ y) I E:=
  ⟨⟨K.pick.grow_i.comp p,K.pick.grow_k.comp t,fun i j=>K.pick.ticket (x i) (y j),fun s S a b=>by obtain ⟨l,z,f⟩:=K.pick.prices s S a b; exact ⟨l,z, Hierarchy.repeter Y K.pick.grow_k p t f⟩⟩,fun s f a=> Hierarchy.repeter Y K.pick.grow_k p t (K.together s f a),K.gaugeMatter⟩
lemma roll_thin {J P}(V: Rolled Y h v w J P):Rolled Y h (v ∘ x) (w ∘ y) J P:=⟨fun i j=> Hierarchy.repeter Y K.pick.grow_k p t (V.evening i j)⟩
end

section
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}(K:Universal Y h u v I E)

private lemma presents : ∃ F:Set (Slip Λ l S), IsCompact F ∧ ∀ i k,snag Y h S s i k∈ F:=by
  refine ⟨insert 0 (closure (Set.range (transitionQ Y h S s))), (compactum Y h S s).insert _,fun i k=>?_⟩; unfold snag; split
  next h=>exact Set.mem_insert_of_mem _ (subset_closure ⟨_,rfl⟩)
  next h=>exact Set.mem_insert _ _

include K
-- with possibility of controlling **extra** growing supports/levels along this refinement.
set_option maxHeartbeats 460000 in
lemma floral : ∃ x y, StrictMono x ∧ StrictMono y ∧ Universal Y h (u∘x) (v∘y) I E ∧
    ∃ J: Wicket Λ l, ∃ P: Call Λ l, Rolled Y h (u∘x) (v∘y) J P := by
  let A:= Finset Cover × ℕ
  obtain ⟨f,hf⟩:= exists_surjective_nat A
  let F(z:A):= snag Y h z.1 z.2; let P(i j):= legacy Y i j; let i₁:= K.pick.grow_i; let v₁:= K.pick.grow_k
  have hu(i:ℕ): ∀ᶠ k in atTop,legacy Y i k:= Y.uv_grows.tendsto_atTop.eventually_ge_atTop _
  have e(k:ℕ) : ∀ᶠ i in atTop,¬ legacy Y i k:= (((tendsto_pow_atTop (α:=ℕ) (by decide : (5:ℕ)≠0)).comp Y.ir_grows.tendsto_atTop).eventually_gt_atTop _).mono fun _ t=> not_le.mpr t
  let D(i:ℕ):= (range (i+1)).image f
  let ε(i:ℕ):= (1/2:ℝ)^i
  obtain ⟨x,y,H,M,hx,hy,P'⟩:= YM.SU5.FiniteGaugeData.LocalLimit.Rings.two_steps (ι:=A) (f:=fun v:A=>Slip Λ l v.1) F (fun _ _=> True) (fun _ _ _=>True) P D ε (fun j=>presents Y h _ _) (fun _=> Eventually.of_forall fun _=> trivial) (fun i _ _=>Eventually.of_forall fun _=>trivial) hu e (fun i=>pow_pos (by positivity) _) u v i₁ v₁
  have he:Tendsto ε atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  refine ⟨x,y,hx,hy, uni_roll Y h hx hy K,fun s t=> H (s,t),fun s t=> M (s,t),⟨fun S s=>⟨P'.cut (S,s), P'.ir (S,s),?_⟩⟩⟩
  intro k t
  refine Metric.tendsto_nhds.mpr fun r p=>?_
  obtain ⟨m,hm⟩:=hf (S,s); filter_upwards [eventually_ge_atTop m,t,he.eventually (gt_mem_nhds p)] with i hi u w
  exact (P'.line i (k i) ((P'.card i (k i)).mp u) (S,s) (mem_image.mpr ⟨_,mem_range.mpr (show m < i+1 by omega),hm⟩)).2.trans_lt w

lemma eligible_offer (r:ℕ→ℕ)(p:eligiblePath Y u v r): ∀ᶠ i in atTop, Offered Y S s (u i) (v (r i)):=by
  filter_upwards [K.pick.grow_i.tendsto_atTop.eventually (solvent_often Y h S s), (Y.uv_grows.tendsto_atTop.comp (Cabinet.walks Y h K.pick p)).eventually_gt_atTop s,p] with i x t H
  exact ⟨K.pick.ticket i (r i) H,t,x⟩
lemma often_offer_inner (p:Solvent Y S s i): ∀ᶠ k in atTop,Offered Y S s i (v k):=(K.pick.grow_k.tendsto_atTop).eventually (((eventually_ge_atTop _).and (Y.uv_grows.tendsto_atTop.eventually_gt_atTop _)).mono fun _ u=>⟨u.1,u.2,p⟩)

/-- late upper bound on every cone path. -/
lemma often_offer : ∀ᶠ i:ℕ in atTop,∀ k:ℕ,legacy Y (u i) (v k) → Offered Y S s (u i) (v k):=by
  let a:= ((tendsto_pow_atTop (α:=ℕ) (by decide : (5:ℕ) ≠ 0)).comp (Y.ir_grows.comp K.pick.grow_i).tendsto_atTop)
  filter_upwards [a.eventually_gt_atTop s,K.pick.grow_i.tendsto_atTop.eventually (solvent_often Y h S s)] with i b q k e
  exact ⟨K.pick.ticket i k e, b.trans_le e,q⟩
set_option maxHeartbeats 500000

variable {J: Wicket Λ l}{P:Call Λ l}(R:Rolled Y h u v J P)
include R
omit K in
lemma calls (k:ℕ→ℕ)(p: eligiblePath Y u v k):
    Tendsto (fun i=>snag Y h S s (u i) (v (k i))) atTop (𝓝 (P S s)):= (R.evening S s).paths k p
omit K in
lemma salaries_I : ‖J S s i‖ ≤ salary Y h S s:=by
  have hv:= (continuous_norm (E:=Slip Λ l S)).continuousAt (x:=J S s i) |>.tendsto; exact le_of_tendsto (hv.comp ((R.evening S s).inner i)) (Eventually.of_forall fun (k:ℕ)=> snag_size Y h S s i (v k)) 
omit K in
lemma salaries_P : ‖P S s‖ ≤ salary Y h S s:=by
  have hv:= (continuous_norm (E:=Slip Λ l S)).continuousAt (x:=P S s) |>.tendsto; exact le_of_tendsto (hv.comp (R.evening S s).periods) (Eventually.of_forall fun (k:ℕ)=> salaries_I Y h S s (u k) R)

lemma hired (ε:ℝ)(a:0<ε): ∀ᶠ i:ℕ in atTop, ‖J S s (u i) - P S s‖ ≤ ε ∧
    ∀ k:ℕ, legacy Y (u i) (v k)→ Offered Y S s (u i) (v k) ∧ ‖snag Y h S s (u i) (v k)-P S s‖ ≤ ε:=by
  filter_upwards [Metric.tendsto_nhds.mp (R.evening S s).periods ε a, path_budget (v:=u) (T:=Slip Λ l S) (z:=P S s) (A:=snag Y h S s) Y K.pick.grow_k (calls Y h S s R) ε a, often_offer Y h S s K] with i t x p
  exact ⟨(show dist (J S s (u i)) (P S s)<_ from t).le.trans_eq' (dist_eq_norm _ (P S s)),fun k a=> ⟨p k a,(x k a).le.trans_eq' (dist_eq_norm _ (P S s))⟩⟩
end
#print axioms often_offer
#print axioms floral
end YM.CF.Buffered.Afterglow.Hierarchy
