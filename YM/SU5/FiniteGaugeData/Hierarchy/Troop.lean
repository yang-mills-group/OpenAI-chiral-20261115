import YM.SU5.FiniteGaugeData.Hierarchy.Lana
/-! # Same-level algebra and overlapping regions -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
section base
variable (K:Calibration){S T:Finset Cover}

-- resolution still external; using same Families at every s means stencil scales change.
def wideAlg : Subalgebra ℂ (Family K) where
  carrier := {p | TestFamily K true p}
  mul_mem' := TestFamily.mul
  add_mem' := TestFamily.add
  algebraMap_mem' v := by rw [Algebra.algebraMap_eq_smul_one]; exact TestFamily.oneT.scale _

abbrev localWide (K:Calibration)(S:Finset Cover): Subalgebra ℂ (Family K) := {
  carrier := {f | InTest K true S false f}
  mul_mem' := fun x y=> InTest.mul x y
  add_mem':= InTest.add
  algebraMap_mem':= fun _=> by rw [Algebra.algebraMap_eq_smul_one]; exact InTest.smul _ InTest.one
}

lemma wide_mem {f:Family K}: f∈ wideAlg K ↔ TestFamily K true f := Iff.rfl
lemma localWide_le (S:Finset Cover):localWide K S≤ wideAlg K:= fun f p=> show TestFamily K true f from ⟨⟨S,p⟩,by simp⟩
lemma localWide_mono (h:S⊆T):localWide K S≤localWide K T:= fun _ (p : InTest K true S false _)=> p.mono h
lemma assemble (S:Finset Cover):LinearMap.range (composeQ K S)=(localWide K S).toSubmodule:= by
  ext x; constructor
  · rintro ⟨f,rfl⟩; exact compose_t S K f
  exact fun t=>certify S K x t

def insertL (h:S⊆T):Catalog S →ₗ[ℂ] Catalog T where
  toFun x := certifyAs T K (composeQ K S x) ((compose_t ..).mono h)
  map_add' x y:= by apply compose_inj T K; rw [certified,map_add,map_add,certified,certified]
  map_smul' c x:=by apply compose_inj T K; rw [certified,map_smul,RingHom.id_apply,map_smul,certified]
lemma insertL_id (h:S⊆T)(x:Catalog S): composeQ K T (insertL K h x)=composeQ K S x:= certified T K _ ((compose_t ..).mono h)
lemma price_incl (h:S⊆T)(x:Catalog S):‖insertL K h x‖ ≤ duration S * ‖x‖:=by
  obtain ⟨i,t⟩:= (roomy_sides T K).exists; exact offered_bound T K _ (roomy_hosp _ t) fun v=> by rw [insertL_id]; exact compose_price ..
def incl (h:S⊆T): Catalog S →L[ℂ] Catalog T:= (insertL K h).mkContinuous (duration S) (price_incl K h)
lemma incl_id (h:S⊆T)(x:Catalog S): composeQ K T (incl K h x)=composeQ K S x:= insertL_id K h x
lemma norm_incl (h:S⊆T): ‖incl K h‖ ≤ duration S:=LinearMap.mkContinuous_norm_le _ (duration_pos _).le _
lemma incl_inj (h:S⊆T): Injective (incl K h):= fun x y e=>compose_inj S K (by rw [←incl_id K h x,←incl_id K h y,e])
lemma incl_refl (S:Finset Cover)(x:Catalog S): incl K (Subset.refl S) x=x:= compose_inj S K (incl_id ..)
lemma incl_comp {U:Finset Cover}(h:S⊆T)(p:T⊆U)(x:Catalog S): incl K p (incl K h x)=incl K (Subset.trans h p) x:= compose_inj U K (by rw [incl_id,incl_id,incl_id])

def paired {D:Finset Cover}(p:S⊆D)(v:T⊆D)(x:Catalog S)(y:Catalog T):Catalog D:= certifyAs D K _ (((compose_t S K x).mono p).mul ((compose_t T K y).mono v))
lemma paired_id {D:Finset Cover}(p:S⊆D)(v:T⊆D)(x:Catalog S)(y:Catalog T): composeQ K D (paired K p v x y)= composeQ K S x * composeQ K T y := certified ..

def timesL {D:Finset Cover}(p:S⊆D)(v:T⊆D) : Catalog S →ₗ[ℂ] Catalog T →ₗ[ℂ] Catalog D :=
 LinearMap.mk₂ ℂ (paired K p v) (fun x y z=>compose_inj D K (by rw [paired_id,map_add,map_add,paired_id,paired_id,add_mul])) (fun x y z=>compose_inj D K (by rw [paired_id,map_smul,map_smul,paired_id,Algebra.smul_mul_assoc])) (fun x y z=>compose_inj D K (by rw [paired_id,map_add,map_add,paired_id,paired_id,mul_add])) (fun x y z=>compose_inj D K (by rw [paired_id,map_smul,map_smul,paired_id,Algebra.mul_smul_comm]))
lemma norm_timesL {D:Finset Cover}(p:S⊆D)(v:T⊆D)(x:Catalog S)(y:Catalog T): ‖timesL K p v x y‖≤ duration S*duration T*‖x‖*‖y‖:=by
  obtain ⟨i,t⟩:= (roomy_sides D K).exists
  refine offered_bound D K (paired K p v x y) (roomy_hosp D t) ?_; intro z; rw [paired_id,Pi.mul_apply,Pi.mul_apply]; exact (norm_mul_le ..).trans ((mul_le_mul (compose_price S K x i z) (compose_price T K y i z) (norm_nonneg _) (mul_nonneg (duration_pos S).le (norm_nonneg _))).trans_eq (by ring))

def timesQ {D:Finset Cover}(p:S⊆D)(v:T⊆D) := LinearMap.mkContinuous₂ (timesL K p v) (duration S*duration T) (norm_timesL K p v)
lemma timesQ_budget {D:Finset Cover}(p:S⊆D)(v:T⊆D): ‖timesQ K p v‖ ≤ duration S * duration T:= LinearMap.mkContinuous₂_norm_le _ (mul_nonneg (duration_pos S).le (duration_pos T).le) _
lemma timesQ_id {D:Finset Cover}(p:S⊆D)(v:T⊆D)(x:Catalog S)(y:Catalog T): composeQ K D (timesQ K p v x y)= composeQ K S x * composeQ K T y:= paired_id K p v x y

def unitQ (S:Finset Cover):Catalog S:= certifyAs S K 1 .one
lemma unitQ_id (S:Finset Cover): composeQ K S (unitQ K S)=1:= certified ..
lemma unitQ_cost (S:Finset Cover): ‖unitQ K S‖≤1:= by obtain ⟨i,h⟩:= (roomy_sides S K).exists; apply offered_bound _ K _ (roomy_hosp _ h); intro x; rw [unitQ_id, Pi.one_apply, Pi.one_apply,norm_one]
end base
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
local notation "W₀" => GridStep Λ l S
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable {P:Call Λ l}{J:Wicket Λ l}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)
local notation "ξ" => GridStep Λ l

lemma grid_mono (p:S⊆T) : GridStep Λ l S ⊆ GridStep Λ l T := by
  intro a h; obtain ⟨b,v,e⟩:= mem_biUnion.mp h; exact mem_biUnion.mpr ⟨b,image_subset_image p v,e⟩

lemma snag_lift (e:Offered Y S s i k)(g:Offered Y T s i k)(p:S⊆T)(x:Catalog S) :
    incl Kₜ (grid_mono S T (Λ:=Λ) (l:=l) p) (snag Y h S s i k x)= snag Y h T s i k (incl Kₜ p x):=by
  apply sold_catalog_inj Y h ((ξ) T) _ _ (roomy_hosp _ g.bill.upper)
  dsimp only; rw [incl_id,snag_pay _ _ _ _ _ _ e, snag_pay _ _ _ _ _ _ g, transitionQ_apply, transitionQ_apply,exchanged,exchanged,incl_id]
include K R
lemma nearby (p:S⊆T)(z:Solvent Y S s i)(t:Solvent Y T s i)(x:Catalog S) :
    incl Kₜ (grid_mono S T (Λ:=Λ) (l:=l) p) (J S s i x)= J T s i (incl Kₜ p x):=
  let V:= incl Kₜ (grid_mono S T (Λ:=Λ) (l:=l) p);
  tendsto_nhds_unique_of_eventuallyEq ((V.continuous.tendsto _).comp (audition _ _ ((R.evening S s).inner i) (tendsto_const_nhds (x:=x)))) (audition _ _ ((R.evening T s).inner i) (tendsto_const_nhds (x:=incl Kₜ p x))) (((often_offer_inner Y h S s i K z).and (often_offer_inner Y h T s i K t)).mono fun _ v=> snag_lift Y h S T s i _ v.1 v.2 p x)
lemma coherence (p:S⊆T)(x: Catalog S) : incl Kₜ (grid_mono S T (Λ:=Λ) (l:=l) p) (P S s x)=P T s (incl Kₜ p x):=by
  obtain ⟨k,g⟩:= eligible_exists Y u _ K.pick.grow_k
  let f:= incl Kₜ (grid_mono S T (Λ:=Λ) (l:=l) p)
  exact tendsto_nhds_unique_of_eventuallyEq ((f.continuous.tendsto _).comp (audition _ _ (calls Y h S s R k g) (tendsto_const_nhds (x:=x)))) (audition _ _ (calls Y h T s R k g) (tendsto_const_nhds (x:=incl Kₜ p x))) (((eligible_offer Y h S s K k g).and (eligible_offer Y h T s K k g)).mono fun i v=> snag_lift Y h S T s _ _ v.1 v.2 p x)
-- input vessel checks
omit R in
lemma access_restrict (p:S⊆T) (a: Catalog S): urn Y h S s i K a=urn Y h T s i K (incl Kₜ p a) := by rw [urn_eval,urn_eval,incl_id]
omit R in
lemma approach_restrict (p:S⊆T)(a:Catalog S): singer Y h S s K a=singer Y h T s K (incl Kₜ p a):=by rw [singer_eval, singer_eval,incl_id]
omit K R in
lemma price_restrict (p:S⊆T)(x:Catalog S) : mkForm Y h S s i k x=mkForm Y h T s i k (incl Kₜ p x) := by
  by_cases v:MarkGate Y s i k; · rw [mk_read _ _ _ _ _ _ v,mk_read _ _ _ _ _ _ v,incl_id]
  unfold mkForm; rw [dif_neg v,dif_neg v]; rfl
#print axioms coherence
end YM.CF.Buffered.Afterglow.Hierarchy
