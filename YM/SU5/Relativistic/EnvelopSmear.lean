import YM.SU5.Relativistic.Envelopes
/-! # Lift smeared packets.

`Bochner in K` uses canonical ℝ real restriction. Chosen locally to avoid
instance conflicts. No Bochner integrability required in unprojected joint.
-/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 240000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Reconstruction
open Function Set Filter Metric MeasureTheory
open MeshClock Germ Vacancy _root_.YM.SelectionAnalysis Analysis
open scoped Topology Classical BigOperators NNReal ENNReal InnerProductSpace

-- canonical Bochner R spaces in local proof (keep specific instance! consumers via center_tends typically)
-- state only result in terms of mesh samples to not expose undocumented instance (internal def).
noncomputable def boch {I:Type*} [Fintype I] (W:Hilbert) (F:(I→ℝ)→W) : W:= by
 letI := NormedSpace.restrictScalars ℝ ℂ W.space
 exact ∫ x in OBox I, F x
lemma bochPrice {I:Type*} [Fintype I] (W:Hilbert) {M:Mesh}(T:(I→ℝ)→W) (p: ContinuousOn T (UBox I)) : Tendsto (fun i:ℕ=> Average.center (fun v:I→ Fin (M.L^i)=> T (smallCorner _ v))) atTop (𝓝 (boch W T)):=by
 letI : NormedSpace ℝ W.space:= NormedSpace.restrictScalars ℝ ℂ W.space
 haveI : IsScalarTower ℝ ℂ W.space:= RestrictScalars.isScalarTower ℝ ℂ W.space
 change Tendsto _ _ (𝓝 (∫ x in OBox I,T x))
 have hc:=center_tends T p
 exact hc.comp (tendsto_pow_atTop_atTop_of_one_lt (show 1<M.L from lt_of_lt_of_le (by decide) M.Llarge))

lemma avg_any {I : Type*}{a b:Fintype I}{B:Type*}[NormedAddCommGroup B][NormedSpace ℂ B] {f g:I→B} (p:∀i,f i=g i): @Average.center I a B _ _ f = @Average.center I b B _ _ g:= by rw [funext p, Subsingleton.elim a b] -- tune

section gate
variable {H:Hilbert}{M:Mesh}{j:Axis}(P:Sunbelt j (marks M) H)(E:OS.Semigroup H j)
variable (e:∀ i,∀ (z : marks M) (t:ℝ≥0), ((P.track.crew i).play z).comp (E.E t)=(E.E t).comp ((P.track.crew i).play z))
local notation "L"=> P.track.Realm P.list
local notation "P₀"=> (P.track.aviator P.list).orthogonalProjectionOnto
local notation "X₀"=> P.track.aviator P.list
local notation "π"=> P.track.stackS P.list
local notation "U₁" u:max=> P.track.raw P.list (fun i=> (u i.val:Stamp M))
local notation "G₀"=> glass P (daylight M) E e
variable (B:H.Op)(S T:Slab M) (F:Packet M)
local notation "Ε"=> envelope P E e B S T
local notation "Υ"=> nativeE P E B S T
local notation "R"=> deliberate P E e B S T
local notation "Z" k:max=> (Axis→ Fin (M.L^k))
local notation "Zb" k:max i:max=> smallCorner (M.L^k) i
noncomputable def collecting (k:ℕ) : H.Op:= Average.center (fun i:Axis→Fin (M.L^k)=> F.score k i • Υ (F.near k i))
local notation "ℳ" k:max=> collecting P E B S T F k
lemma collecting_value (x:H)(k:ℕ) : (ℳ k) x = Average.center (fun i:Axis→Fin (M.L^k)=> F.score k i • ((Υ (F.near k i)) x)):= (Average.natural _ (ContinuousLinearMap.apply ℂ H.space x)).symm
lemma collecting_worth {C:ℝ}(c:∀ i:ℕ,∀ x:Axis→Fin (M.L^i), ‖F.score i x‖ ≤ C)(v:ℕ): ‖ℳ v‖ ≤ C*‖B‖:=by
 haveI:=avg_lives M v
 apply Average.norm_worth; intro i; rw [norm_smul]; exact mul_le_mul_of_nonneg_left (native_cost P E B S T (F.near v i)) (by positivity) |>.trans (mul_le_mul_of_nonneg_right (c v i) (norm_nonneg _)) -- norm_smul equality? includes real NormOne
local notation "Zc" k:max i:max=> (U₁ (F.near k i))
lemma collecting_gap (x:P.track.Realm P.list) :
    Tendsto (fun i:ℕ=> ((ℳ i) x.val)- (Average.center (fun u:Axis→Fin (M.L^i)=> (F.score i u) • ((Ε (F.region (Zb i u))) x:X₀))).val) atTop (𝓝 (0:H)) := by
 let D(u:Axis→ℝ):H:= F.weight u • (R x (F.region u))
 have h:ContinuousOn D (UBox Axis):= F.closed_weight.smul (((deliberate_cont P E e B S T x).comp (Packet.sweeps_cont F)).continuousOn)
 have hz:= variable_gap M P.track Subtype.val D P.list F.size (fun i=>F.base i.val) h P.unique_list Subtype.val_injective
 have hX(k:ℕ)(i:Z k):F.score k i • (Υ (F.near k i) x.val)=(Zc k i) (D (Zb k i)):= by
    rw [native_price P E e B S T x,show (fun a: Axis=>_) = F.region (Zb k i) from funext (F.points_near k i), ←map_smul]; rfl -- implicit infer
 have hV(k:ℕ)(i:Z k): ((F.score k i) • (show P.track.Realm P.list from (Ε (F.region (Zb k i))) x): X₀).val=(Zc k i) (π (D (Zb k i))):=by
    change F.score k i • ((Ε _ x: X₀).val:H)=_; rw [← funext (F.points_near k i),enmeshed, ← map_smul, ← map_smul]; unfold D; rw [←funext (F.points_near k i)]; rfl
 refine hz.congr' (Eventually.of_forall fun k=> ?_)
 let hQ(Z' : Z k): (P.track.Realm P.list):= F.score k Z' • (Ε (F.region (Zb k Z')) x)
 let g(Z' : Z k):H:= F.score k Z' • ((Υ (F.near k Z')) x.val)
 change _ = (ℳ k) (x.val:H) - ((X₀).subtypeL (Average.center hQ))
 have hp : (ℳ k) (x.val:H)= Average.center g:= collecting_value P E B S T F x.val k
 have hi : Average.center (fun i=> (X₀).subtypeL (hQ i))=(X₀).subtypeL (Average.center hQ) := Average.natural hQ (X₀).subtypeL
 rw [hp,←hi,←Average.minus]
 apply avg_any
 intro i
 change (Zc k i) (D _- _) = g i - (X₀).subtypeL (hQ i); rw [map_sub]
 exact congrArg₂ (· - ·) (hX k i).symm (hV k i).symm

noncomputable def assembled₀ (x:P.track.Realm P.list):P.track.Realm P.list:= boch (P.track.Realm P.list) (fun u:Axis→ℝ=> F.weight u • ((envelope P E e B S T (F.region u)) x))
local notation "B₁" x:max=> assembled₀ P E e B S T F x
lemma projected_collect (x:P.track.Realm P.list) :
    Tendsto (fun i:ℕ=> Average.center (fun u:Axis→ Fin (M.L^i)=> F.score i u • (Ε (F.region (Zb i u)) x))) atTop (𝓝 (B₁ x)) := by
  let D(u:Axis→ℝ): L:= F.weight u • (Ε (F.region u) x)
  have h: ContinuousOn D (UBox Axis):= F.closed_weight.smul (((envelope_cont P E e B S T x).comp (Packet.sweeps_cont F)).continuousOn)
  apply (Tendsto.congr' ?_ (bochPrice (M:=M) (L) D h)) -- order cong?
  refine Eventually.of_forall fun i =>?_
  apply avg_any; intro a; rfl
lemma collecting_strength (x:P.track.Realm P.list):
    Tendsto (fun i:ℕ=> (ℳ i) (x.val:H)) atTop (𝓝 (((B₁ x).val) : H)) := by
  have p:=(collecting_gap P E e B S T F x).add ((X₀).subtypeL.continuous.continuousAt.tendsto.comp (projected_collect P E e B S T F x))
  change Tendsto (fun i:ℕ=> ((ℳ i) _ - (Average.center (fun u:Axis→Fin (M.L^i)=> (F.score i u) • ((Ε (F.region (Zb i u))) x:X₀))).val)+ (Average.center (fun u:Axis→Fin (M.L^i)=> (F.score i u) • ((Ε (F.region (Zb i u))) x:X₀))).val) _ (𝓝 (0+(B₁ x).val)) at p
  simpa only [sub_add_cancel,zero_add] using p
lemma assembled_cost (x:P.track.Realm P.list) {C:ℝ}(p:∀ i:ℕ,∀ z: Z i, ‖F.score i z‖≤ C) : ‖B₁ x‖ ≤ C * ‖B‖ * ‖x‖:= le_of_tendsto (collecting_strength P E e B S T F x|>.norm) (Eventually.of_forall fun i=> ((ℳ i).le_opNorm _).trans (mul_le_mul_of_nonneg_right (collecting_worth P E B S T F p _) (norm_nonneg _)))
noncomputable def envelop : (P.track.Realm P.list).Op:=
   LinearMap.mkContinuous (show (P.track.Realm P.list)→ₗ[ℂ]P.track.Realm P.list from {
     toFun:= assembled₀ P E e B S T F
     map_add' x y:= by
         apply Subtype.ext; exact tendsto_nhds_unique (collecting_strength P E e B S T F (x+y)) ((collecting_strength P E e B S T F x).add (collecting_strength P E e B S T F y)|>.congr' (Eventually.of_forall fun i=> ((ℳ i).map_add x.val y.val).symm))
     map_smul' c x:= by
         apply Subtype.ext; exact tendsto_nhds_unique (collecting_strength P E e B S T F (c•x)) (((tendsto_const_nhds (x:=c)).smul (collecting_strength P E e B S T F x)).congr' (Eventually.of_forall fun i=>((ℳ i).map_smul c x.val).symm)) }) ((F.span_score).choose*‖B‖) (fun x=> assembled_cost P E e B S T F x (F.span_score).choose_spec.2)
lemma envelop_price (x:P.track.Realm P.list):
    Tendsto (fun i:ℕ=> (ℳ i) (x.val:H)) atTop (𝓝 (((envelop P E e B S T F x).val):H)):= collecting_strength P E e B S T F x
end gate
end YM.CF.Buffered.Afterglow.Tower.Reconstruction
#print axioms YM.CF.Buffered.Afterglow.Tower.Reconstruction.envelop_price
