import YM.SU5.Reconstruction.Cone.Pressure
import YM.SU5.Selected.CompassGlass
/-!
# Checks for one-axis grid U/E dynamics. Works with abstract chambers also. Keeps relative normalization exactly.
`S.U` itself not used! pretend projected group only via `glass`. Goal no spatial modes dropped.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section

namespace YM.ConePrice
open Function Set Filter MeasureTheory Measure InnerProductSpace Spectral OS Semigroup CF.Buffered.Afterglow.Tower MeshClock Germ SelectionAnalysis
open scoped BigOperators NNReal ENNReal Topology InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} {Γ : AddSubgroup ℝ} (S : OS.Semigroup H a)
variable (d : Dense (Γ:Set ℝ)) (X : Sunbelt a Γ H)
  (g : ∀ i,∀ (z : Γ) (t:ℝ≥0), ((X.track.crew i).play z).comp (S.E t)=(S.E t).comp ((X.track.crew i).play z))
local notation "Gt" => (Axis→Γ)
local notation "C₀" => X.track.aviator X.list
local notation "U" => glass X d S g
local notation "G₀" => X.track.Realm X.list
local notation "H₀" => H.space
-- specifically choose `diameter`, spectral pressure bills accordingly
abbrev face {M : AddSubgroup ℝ} (p : Axis→M) : Axis→ℝ := fun i=> (p i:ℝ)
include d in
lemma face_dense : DenseRange (@face Γ) := DenseRange.piMap (X:=fun _ : Axis => Γ) (fun _=> d.denseRange_val)

abbrev transverse_play (p : Axis→Γ) := X.track.raw X.list (fun i=>p i.val)
local notation "β" => diameter (a:=a)

def CostDomain (a : Axis) (e : ℝ) : Set (Axis→ℝ) := {p| 0 < p a ∧ ‖diameter (a:=a) p‖≤ p a ∧ p a < e}

def GridHeat (e : ℝ) : Prop := ∀ p : Axis→Γ, face p ∈ CostDomain a e → ∀ x:H,
    let t:= (face p a).toNNReal; ‖(S.E t) (transverse_play X p x) - S.E t x‖ ≤ ‖x-S.E t x‖
section clock_height
include d in
lemma time_piece {p : ℝ} (hp : 0<p) (ε : ℝ) (t : 0<ε) (x:H) : ∃ u:Γ, 0 < u.val ∧ u.val < p ∧ dist x (S.E u.val.toNNReal x)< ε := by
  have h : ∀ᶠ v in 𝓝 (0:ℝ), dist x (S.E v.toNNReal x) < ε ∧ v < p := by
    apply Filter.Eventually.and _ (Iio_mem_nhds hp)
    refine (dist_continuous x).continuousAt.eventually_lt continuousAt_const ?_ -- need conv?
  -- tune, factor function complete in where
    rw [Real.toNNReal_zero,S.eZero]; simpa using t
  have ht:= show ∃ u > (0:ℝ), ∀ r:ℝ, |r| < u → dist x (S.E r.toNNReal x)< ε ∧ r < p from ?_
  swap
  · obtain ⟨r,c,v⟩:= Metric.mem_nhds_iff.mp h; exact ⟨r,c,fun a b => v (show _ from Metric.mem_ball.mpr (by rwa [Real.dist_0_eq_abs]))⟩
  obtain ⟨u,hu,hx⟩:=ht
  obtain ⟨v,t,e⟩:=d.exists_mem_open isOpen_Ioo (Set.nonempty_Ioo.mpr hu)
  obtain ⟨hv,h⟩ := hx v (by rw [abs_of_pos e.1]; exact e.2)
  exact ⟨⟨v,t⟩,e.1,h,hv⟩
where
  dist_continuous (x:H) : Continuous (fun v:ℝ => dist x (S.E v.toNNReal x)) := continuous_const.dist ((S.continuousE x).comp continuous_real_toNNReal)
local notation "D₁"=> {i:Axis//i≠a}
local notation "Π" i:max=> ((X.track.crew i).play)
lemma spotlight2 (p : Γ) (i : {i:Axis//i≠a}) (t : Γ) :
    let s := Function.update (Function.update (0:Axis→Γ) a p) i.val t
    (diameter (a:=a) (face s)).val = (t:ℝ) • basis i.val ∧ face s a = (p:ℝ) ∧ transverse_play X s= (X.track.crew i).play t := by
  intro s
  refine ⟨?_,?_,?_⟩
  · ext v; by_cases h:v=a
    · subst v; rw [show (diameter (a:=a) _).val a =0 from (diameter (a:=a) (face s)).property]; simp [i.property.symm]
    rw [diameter_at (face s) v h]; by_cases u:v=i.val
    · subst v; simp [face,s]
    simp [face,s,update_of_ne,u,h]
  · simp [face,s,i.property.symm]
  unfold transverse_play; rw [show (fun b:D₁=> s b.val)= Function.update (0 : D₁→Γ) i t from ?_]; exact spotlight X.track X.list X.unique_list (X.traverses i) t -- arg
  funext b; by_cases h : b=i
  · subst b; simp [s]
  have hv : b.val≠i.val := fun e=> h (Subtype.ext e)
  simp [s,update_of_ne,hv,h,b.property]
include d g
lemma all_saunter {b : ℝ} (hb : 0 < b) (h : GridHeat S X b) : C₀=⊤ := by
  apply le_antisymm le_top; intro x _
  apply (X.track.assembled X.list x).mpr; intro i hi
  let E:= X.track.crew i
  apply E.living.mpr; intro ε t
  obtain ⟨T,e,v,r⟩ := time_piece S d hb (ε/3) (by positivity) x
  let u:= (T:ℝ).toNNReal; refine ⟨T.val,e,fun w l=>?_⟩
  obtain ⟨hx,hu,hy⟩:= spotlight2 X T i w
  let s:= Function.update (Function.update (0:Axis→Γ) a T) i.val w
  have H₁:= h s (by
    change 0 < face s a ∧ ‖(diameter (a:=a) (face s)).val‖ ≤ face s a ∧ face s a < b
    dsimp only [s]; rw [hu,hx]; refine ⟨e,?_,v⟩; rw [norm_smul]; simpa using l.le) x
  dsimp only [s] at H₁; rw [hu,hy] at H₁
  have h₁ : dist (E.play w (S.E u x)) (S.E u x) < ε/3 := by
    rw [dist_eq_norm] at *; refine lt_of_le_of_lt ?_ r
    unfold E; rw [← ContinuousLinearMap.comp_apply,g]; exact H₁
  calc
    _ ≤ dist (E.play w x) (E.play w (S.E u x)) + (dist (E.play w (S.E u x)) x) := dist_triangle ..
    _ ≤ dist x (S.E u x) + (dist (E.play w (S.E u x)) (S.E u x) + dist (S.E u x) x) := by rw [E.rigid H]; gcongr; exact dist_triangle ..
    _ < ε := by rw [dist_comm (S.E u x) x]; change dist x (S.E u x)< ε/3 at r; linarith
end clock_height
section continuity
abbrev clears (v : H) (p : Axis→ℝ) :=
    let t := (p a).toNNReal; ‖S.U (diameter p) (S.E t v)-S.E t v‖ ≤ ‖v-S.E t v‖
lemma closure_price (x:H) : IsClosed {p : Axis→ℝ | clears S x p} := by
  have h : Continuous (fun p : Axis→ℝ => S.E (p a).toNNReal x) := (S.continuousE _).comp (continuous_real_toNNReal.comp (continuous_apply _))
  exact isClosed_le (((S.cont_cross _ diameter h (by unfold diameter; fun_prop)).sub h).norm) ((continuous_const.sub h).norm) -- β inferred

include d in
-- surface by moving time slightly after fixed displacement; avoid hard closure at apex
lemma face_closure {t : ℝ} {e : ℝ} (_he : 0<t) (b : t<e) (x : Cross a) (hx : ‖x‖≤ t) :
    ∃ p : Axis→ℝ, p a=t ∧ diameter (a:=a) p=x ∧ p ∈ closure (range (@face Γ) ∩ CostDomain a e) := by
  let f (z : ℝ) := WithLp.ofLp (z • basis a+x.val:E4)
  have hf : Continuous f := by unfold f; fun_prop
  have ht z : f z a=z := by simp [f,(show x.val a=0 from x.property)] -- val simpl
  have hv z : diameter (a:=a) (f z) = x := by unfold f diameter; rw [WithLp.toLp_ofLp, map_add,sep_along]; simp only [map_smul]; rw [show SEP a (basis a)=0 from Subtype.ext (by change basis a - _ • basis a=(0:E4); simp), smul_zero,zero_add]
  let T:= {p:Axis→ℝ| ‖diameter (a:=a) p‖<p a ∧ p a<e}
  have hT : IsOpen T := IsOpen.inter (isOpen_lt (by exact (show Continuous (diameter (a:=a)) by unfold diameter; fun_prop).norm) (continuous_apply a)) ((isOpen_lt (continuous_apply a) (continuous_const (y:=e))))
  have hU : T⊆ CostDomain a e:= fun p ⟨c,d⟩ => ⟨(norm_nonneg _).trans_lt c, c.le,d⟩
  refine ⟨f t, ht t,hv t,?_⟩
  have hy := hf.continuousAt (x:=t); apply IsClosed.mem_of_tendsto isClosed_closure (hy.tendsto.mono_left (nhdsWithin_le_nhds (s:= Ioi t)))
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds b)] with i hi hz
  apply closure_mono (inter_subset_inter_right _ hU) -- maybe left
  have hs : f i ∈ T:= by change ‖_‖<f i a ∧ f i a<e; rw [ht,hv]; exact ⟨hx.trans_lt hi,hz⟩
  exact hT.closure_inter ⟨face_dense d (f i),hs⟩

lemma buy_clear (v : G₀) (p:Axis→Γ) :
    clears (U) v (face p) ↔
      let t:= (face p a).toNNReal
      ‖(S.E t) (transverse_play X p (v.val:H))- S.E t (v.val:H)‖ ≤ ‖v.val- S.E t (v.val:H)‖ := by
  dsimp only [clears]; let t:= (face p a).toNNReal
  erw [← ContinuousLinearMap.comp_apply ( (U).U _), ← (U).independent, ContinuousLinearMap.comp_apply];
  change ‖(((U).E t ((U).U _ v):C₀).val:H)- ((U).E t v:C₀).val‖ ≤ ‖v.val-((U).E t v:C₀).val‖ ↔ _
  rw [glass_heat,glass_heat,glass_move]
lemma compass_cools {e : ℝ} (h : GridHeat S X e) : Cools (U) e := by
  intro t ht hb y b v; obtain ⟨p,u,ga,r⟩ := face_closure d (show 0 < (t:ℝ) from ht) hb y b
  have hs := closure_minimal ?_ (closure_price (U) v) r
  swap
  · rintro w ⟨⟨p,rfl⟩,k⟩; exact (buy_clear S d X (by assumption) v p).mpr (h p k v.val)
  change clears (U) v p at hs
  dsimp only [clears] at hs
  rw [u,ga,Real.toNNReal_coe] at hs; exact hs
lemma glass_price {e : ℝ} (h : Cools (U) e) (v : C₀=⊤) : GridHeat S X e := by
  rintro p ⟨ht,he,hu⟩ x; let y:G₀ := (⟨x,show x∈ C₀ from v.symm ▸ (show x ∈ (⊤:Submodule ℂ H) from Submodule.mem_top)⟩ : C₀)
  apply (buy_clear S d X g y p).mp
  let t:= (face p a).toNNReal; have ht' : (t:ℝ)=face p a:= Real.coe_toNNReal _ ht.le
  exact h t ((by exact Real.toNNReal_pos.mpr ht)) (by rw [ht']; exact hu) _ (by rw [ht']; exact he) y
end continuity

-- Combining: a single operator difference price equivalence for the actual physical grid.
theorem operator_pressure {b : ℝ} (hb : 0 < b) : GridHeat S X b ↔ C₀=⊤ ∧ Forward (U) := by
  constructor
  · intro h; exact ⟨all_saunter S d X g hb h, prices_spectrum (U) hb (compass_cools S d X g h)⟩
  rintro ⟨hs,h⟩; exact glass_price S d X g ((true_spectrum_price _ hb).1 h) hs
end YM.ConePrice
