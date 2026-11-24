import YM.SU5.FiniteGaugeData.Tapestry.Sensitivity
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-!
# Same-election sharp reader and step. Passing both limits in local norm.

The simultaneous statement below is on a genuine **filter of all pairs** in
the Exhibition's cone (both indices after its further thinnings), uniform in
the choice of their cutoff stages. Also available per row, separately removing
cutoff. Neither period-unitarity nor any common step-schedule is assumed.
-/
set_option quotPrecheck false

structure WedgeStage where
  vol : ℕ
  uv : ℕ
  inside : vol ≤ uv
def followStage : Filter WedgeStage := comap WedgeStage.vol atTop
lemma overStage : Tendsto WedgeStage.vol followStage atTop := tendsto_comap
lemma aboveStage : Tendsto WedgeStage.uv followStage atTop := tendsto_atTop_mono WedgeStage.inside overStage
instance : NeBot followStage := NeBot.comap_of_surj (inferInstanceAs (atTop: Filter ℕ).NeBot) (fun i=> ⟨⟨i,i,le_rfl⟩,rfl⟩)
lemma eventuallyReflection (p:WedgeStage→Prop) : (∀ᶠ t in followStage,p t) ↔ ∀ᶠ r in atTop,∀ j,∀ h:r ≤ j, p ⟨r,j,h⟩ := by
  unfold followStage; rw [eventually_comap]; apply eventually_congr; refine Eventually.of_forall ?_; intro i; constructor
  · exact fun h j x=> h _ rfl
  rintro x ⟨v,j,q⟩ (e : v=i); subst i; exact x j q -- tune
lemma propeller_fades : Tendsto propeller atTop (𝓝 0):= tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

section
variable {X Y:Type*}[NormedAddCommGroup X][NormedAddCommGroup Y][NormedSpace ℂ X][NormedSpace ℂ Y]
omit [NormedSpace ℂ X] in
lemma steam {I:Type*}{L:Filter I} (g:I→ℝ)(w:X)(f:I→ X)(h:Tendsto g L (𝓝 0)) (p:∀ᶠ i in L,‖f i-w‖≤g i): Tendsto f L (𝓝 w):=by
  apply Metric.tendsto_nhds.mpr; intro ε e; filter_upwards [p,h.eventually (gt_mem_nhds e)] with i a h; exact (show dist (f i) w=‖f i-w‖ from dist_eq_norm ..) ▸ lt_of_le_of_lt a (show g i<ε from h)

lemma skimEnvelope {x y : X→L[ℂ]Y}{A:ℝ}(f:0≤A)(p:∀ i:X, ‖i‖=1 → ‖x i-y i‖ ≤ A): ‖x-y‖≤ A := ContinuousLinearMap.opNorm_le_of_unit_norm f p
lemma cn_apply {I:Type*}{L:Filter I}{v:I→X→L[ℂ]Y}{x:I→X}{A:X→L[ℂ]Y}{X':X}(p:Tendsto v L (𝓝 A))(h:Tendsto x L (𝓝 X')) : Tendsto (fun i=> v i (x i)) L (𝓝 (A X')):= (show Continuous (fun x:(X→L[ℂ]Y)×X=> x.1 x.2) from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp (p.prodMk_nhds h)
lemma approx_op (f g:X→L[ℂ] Y)(x:X){C:ℝ}(h:‖f-g‖≤C) : ‖f x-g x‖ ≤ C*‖x‖:= (f-g).le_of_opNorm_le h x
-- also for individual rows too small for Swatch op-norm estimate
lemma sliceApply {D:Type*}{L:Filter D}{A:D→ X →L[ℂ] Y}{u:X→L[ℂ]Y}{t:D→ X}{v:X}{C:ℝ} (p:Tendsto (fun i=> A i v) L (𝓝 (u v))) (q:Tendsto t L (𝓝 v)) (h:∀ᶠ i in L,∀ x, ‖A i x‖ ≤ C*‖x‖): Tendsto (fun i=> A i (t i)) L (𝓝 (u v)):=by
  have he:Tendsto (fun i=>A i (t i-v)) L (𝓝 0):=by
    apply steam (g:=fun i=> C * ‖t i-v‖)
    · simpa using (((q.sub_const v).norm).const_mul C)
    exact h.mono fun i h=>by simpa using h (t i-v)
  simpa only [map_sub,sub_add_cancel,zero_add] using he.add p

-- explicit for resolving in large swatch space with pi topology
lemma steamStep {D:Type*}{L:Filter D}{A:D→X→L[ℂ]Y} (x:X→L[ℂ]Y) (f:D→ℝ)(p:Tendsto f L (𝓝 0))(h:∀ᶠ i in L, ‖A i-x‖ ≤ f i): Tendsto A L (𝓝 x):= steam (X:=X→L[ℂ]Y) f x A p h
lemma leStep {D:Type*}{L:Filter D}[L.NeBot]{A:D→X→L[ℂ]Y}{x:X→L[ℂ]Y}(y:X→L[ℂ]Y) {f:ℝ}(p:Tendsto A L (𝓝 x))(h:∀ᶠ i in L, dist (A i) y ≤ f):‖x-y‖≤ f:= (dist_eq_norm x y) ▸ le_of_tendsto (p.dist tendsto_const_nhds) h

end
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
section
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (S:Finset Cover)(s i k:ℕ)
variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l} (X:Exhibition Y H a b I E L B)
local notation "K"=> tent Y H
local notation "U" => followBox (Λ:=Λ) (l:=l) S
local notation "β"=> coupon Y H S s
local notation "τ"=> tapReader Y H S s
local notation "g"=> propeller
namespace Exhibition
local notation "Ξ" => X.rowsRead Y H S s -- X conflict TYPE? open
local notation "W"=> X.thermodynamic Y H S s
local notation "i₀" t:max=> a (WedgeStage.vol t)
local notation "k₀" t:max => b (WedgeStage.uv t)
include X
lemma matineeRow (v:Matinee Y S s i): ∀ᶠ j in atTop, Spanned Y S s i (b j) := (X.univ_.pick.grow_k.tendsto_atTop.eventually (eventualPairIdx Y s i)).mono fun k p=>⟨p,v⟩
lemma cone_bill : ∀ᶠ t in followStage, Spanned Y S s (i₀ t) (k₀ t) ∧ ‖β (i₀ t) (k₀ t) - B S s‖ ≤ g t.vol := by
  filter_upwards [overStage.eventually (X.road S s)] with t p; have h:=(p.2 t.uv t.inside); exact ⟨h.1,(dist_eq_norm (β (i₀ t) (k₀ t)) (B S s)) ▸ h.2⟩
lemma payStage : ∀ᶠ t in followStage, Tapestry.Pay Y s (i₀ t) (k₀ t) := (X.cone_bill Y H ∅ s).mono fun t h=> ⟨h.1.1.1,h.1.1.2.le⟩
lemma coneAdvance : Tendsto (fun t=> β (i₀ t) (k₀ t)) followStage (𝓝 (B S s)) := by
  refine (Metric.tendsto_nhds (a:=B S s) (f:=followStage) (u:=fun t=>coupon Y H S s (i₀ t) (k₀ t))).mpr ?_; intro ε e
  filter_upwards [overStage.eventually (X.road S s),(propeller_fades.comp overStage).eventually (gt_mem_nhds e)] with t p h
  exact ((p.2 t.uv t.inside).2).trans_lt (show propeller t.vol < ε from h)

lemma rattle : ∀ᶠ i in atTop, ‖X.rowsRead Y H S s (a i) - X.thermodynamic Y H S s‖ ≤ g i*spread S := by
  filter_upwards [X.parallel S s] with i h; apply skimEnvelope (by unfold propeller spread; positivity); intro x u
  let m:= momentm Y (a i) s; change ‖I s _ (a i)- E s _‖≤ _; exact (h.2 (render S K x) (texture ..) (spread S) (fun y=> (renderLe S K m x y).trans (by rw [u,mul_one]))).1 -- tune syntax
lemma stability : ∀ᶠ t in followStage, ‖tapReader Y H S s (i₀ t) (k₀ t) - X.thermodynamic Y H S s‖ ≤ propeller t.vol * spread S:=by
  filter_upwards [overStage.eventually (X.parallel S s),X.payStage Y H s] with t h p
  let m:=momentm Y (i₀ t) s; apply skimEnvelope (by unfold propeller spread; positivity); intro x u
  rw [tapReader_sharp _ _ _ _ _ _ _ p]; exact (h.2 (render S K x) (texture ..) (spread S) (fun y=> (renderLe S K m x y).trans (by rw [u,mul_one]))).2 t.uv ((X.status ..).2 t.inside)
lemma coneReader : Tendsto (fun t=> tapReader Y H S s (i₀ t) (k₀ t)) followStage (𝓝 (X.thermodynamic Y H S s)) := steamStep (X:=Swatch S) (Y:=ℂ) (A:=fun (t:WedgeStage)=> tapReader Y H S s (i₀ t) (k₀ t)) (W) (fun (t:WedgeStage)=>g t.vol * spread S) (by simpa using (propeller_fades.comp overStage).mul_const (spread S)) (X.stability Y H S s)
lemma periodReader : Tendsto (fun i=> X.rowsRead Y H S s (a i)) atTop (𝓝 (X.thermodynamic Y H S s)) := steamStep (X:=Swatch S) (Y:=ℂ) (A:=fun i=>Ξ (a i)) (W) (fun i=>g i*spread S) (by simpa using propeller_fades.mul_const (spread S)) (X.rattle Y H S s)
-- uniform row statement as in boutique
lemma horizonReaders : ∀ᶠ i in atTop, Tendsto (fun k : ℕ=> τ i (b k)) atTop (𝓝 (X.rowsRead Y H S s i)) := by
  filter_upwards [(boutique Y H X.univ_ S s).1, (roomyTail Y H s S)] with i p v
  refine (Metric.tendsto_nhds (a:=(X.rowsRead Y H S s i))).2 ?_; intro ε e; let G:=ε/(spread S+1); have h:0<G:=by unfold G spread; positivity
  filter_upwards [p G h, X.sharper Y H s i] with k H' J
  let M:= Ξ i; rw [dist_eq_norm (tapReader Y H S s i (b k)) M]; apply (skimEnvelope (A:=G*spread S) (by unfold spread; positivity) ?_).trans_lt; swap
  · intro x u; rw [tapReader_sharp Y H S s i (b k) _ J]; let m:=momentm Y i s
    exact H' (render S K x) (texture ..) m ((terrain Y H (Y.ir i) s).symm ▸ Roomy.seats v) _ (fun y=> (renderLe S K m x y).trans (by rw [u,mul_one]))
  have hu:G*(spread S+1)=ε:= div_mul_cancel₀ _ (by unfold spread; positivity); nlinarith
lemma noPeriodError : ∀ᶠ r in atTop, ‖L S s (a r) - B S s‖ ≤ g r:=by
  filter_upwards [X.road S s] with r p
  have h := X.inner S s (a r)
  have g' : Tendsto (fun i=>dist (coupon Y H S s (a r) (b i)) (B S s)) atTop (𝓝 (dist (L S s (a r)) (B S s))) := h.dist (tendsto_const_nhds (x:=B S s))
  exact (dist_eq_norm (L S s (a r)) (B S s)) ▸ (show dist (L S s (a r)) (B S s) ≤ propeller r from le_of_tendsto g' ((eventually_ge_atTop r).mono fun i q=> (p.2 i q).2))


lemma compactRow : IsCompactOperator (L S s i):= isCompactOperator_of_tendsto (X.inner S s i) (Eventually.of_forall fun k=> compact_coupon Y H S s i (b k))
lemma compactBridge : IsCompactOperator (B S s):= isCompactOperator_of_tendsto (X.IR S s) (Eventually.of_forall fun i=> X.compactRow Y H S s (a i))
end Exhibition

lemma onSpanned (p:Spanned Y S s i k)(f:Swatch S): present Y H (s+1) i U (coupon Y H S s i k f)=ascender Y s i k (present Y H s i S f):=by
  rw [coupon,dif_pos p]; rw [offerMap]; exact costumed ..
lemma readAdvance (p:Spanned Y S s i k)(f:Swatch S) : tapReader Y H U (s+1) i k (coupon Y H S s i k f)= tapReader Y H S s i k f := by
  rw [tapReader_compass Y H S s i k _ ⟨p.1.1,p.1.2.le⟩,tapReader_compass Y H U (s+1) i k _ ⟨p.1.1,p.1.2⟩,onSpanned Y H S s i k p]; exact (partake Y s i k p.1 ((presented Y H s i S f).mono (subset_univ _))).symm
namespace Exhibition
include X
/-- Compatibility of every supported adjacent-level family of readers with a
meaningful common physical inter-level map on the **row** when qualified. -/
lemma exactRow (p:Matinee Y S s i)(f:Swatch S):
   I s (render S K f) i= I (s+1) (render U K (L S s i f)) i:=by
  have t:= X.inner S s i; let v:=(fun (k:ℕ)=> coupon Y H S s i (b k) f)
  have h:Tendsto v atTop (𝓝 (L S s i f)):= cn_apply (X:=Swatch S) (Y:=Swatch U) t (tendsto_const_nhds (x:=f))
  have u:Tendsto (fun k:ℕ=> tapReader Y H U (s+1) i (b k) (v k)) atTop (𝓝 (rowsRead Y H U (s+1) i X (L S s i f))) := by
    obtain ⟨C,c,H'⟩:= late_bound Y H U (s+1)
    exact sliceApply (X:=Swatch U) (Y:=ℂ) (A:=fun k=> tapReader Y H U (s+1) i (b k)) (u:=X.rowsRead Y H U (s+1) i) (pointRow Y H U (s+1) i X _) h ((X.univ_.pick.grow_k.tendsto_atTop.eventually H').mono (fun k m=> m i))
  exact tendsto_nhds_unique_of_eventuallyEq (pointRow Y H S s i X f) u ((matineeRow Y H S s i X p).mono fun k q=> (readAdvance Y H S s i (b k) q f).symm)
lemma exactFamily (f:Swatch S): E s (render S K f) = E (s+1) (render U K (B S s f)):=by
  have h:= cn_apply (X:=Swatch U) (Y:=ℂ) (X.periodReader Y H U (s+1)) (cn_apply (X:=Swatch S) (Y:=Swatch U) (X.IR S s) (tendsto_const_nhds (x:=f) (f:=atTop)))
  exact tendsto_nhds_unique_of_eventuallyEq (pointIR Y H S s X f) h ((X.road S s).mono fun i p=> exactRow Y H S s (a i) X p.1 f)
lemma exactStep : (X.thermodynamic Y H U (s+1)).comp (B S s)= X.thermodynamic Y H S s := ContinuousLinearMap.ext (fun x=> (X.exactFamily Y H S s x).symm)
end Exhibition
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.coneReader
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.horizonReaders
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.exactStep
