import YM.CF.BPress.Mood
import YM.CF.BPress.Selector
/-!
Lifts and `eq:B-mood`: nearest point argument in the tube. Use a measurable
section. We'll alter the choice later as needed near the center labels to make
parameter 1 (= center 0) detect the lift near identity.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Mag
open Function Filter Set Metric MeasureTheory SU
open scoped Topology ContDiff BigOperators NNReal Matrix.Norms.Frobenius Classical
attribute [local instance] Gauge.frobInner

def shade (h : E) : Hue := paint h⁻¹
lemma shade_cont : Continuous shade:= paint_cont.comp continuous_inv
@[simp] lemma shade_one : shade 1=magnet:= by rw [shade,inv_one,paint,spin_one]
lemma center_spin_inv (i : Fin 5) (H : Hue) : spin (center i)⁻¹ H=H:= by nth_rw 1 [←spin_cent i H]; rw [spin_seq,inv_mul_cancel,spin_one]
lemma center_shade (i : Fin 5) (h : E) : shade (center i * h)=shade h:= by simp only [shade,paint,mul_inv_rev,←spin_seq,center_spin_inv]
lemma shade_gauge (a h : E) : shade (h*a⁻¹)=spin a (shade h):= by rw [shade,paint,mul_inv_rev,inv_inv,←spin_seq]; rfl
lemma shade_rel (h k : E) : shade h=shade k ↔ ∃ i, k=center i * h:=by
  constructor
  · intro e; have he:=congrArg (spin k) e; unfold shade paint at he; rw [spin_seq,spin_seq,mul_inv_cancel,spin_one] at he; obtain ⟨i,r⟩:=stab.mp he; exact ⟨i,by rw [←r]; group⟩ -- `group` tactic shadow ok
  rintro ⟨i,rfl⟩; exact (center_shade ..).symm

def Chosen (H : Hue) (h : E) := ∀ k, dist H (shade h) ≤ dist H (shade k)
lemma chosen_exists (H : Hue) : ∃ h, Chosen H h:=by obtain ⟨h,t,g⟩:= isCompact_univ.exists_isMinOn univ_nonempty (continuous_const.dist shade_cont).continuousOn (f:=fun k=> dist H (shade k)); exact ⟨h,fun k=> g (mem_univ k)⟩
lemma chosen_closed : IsClosed { x : Hue × E | Chosen x.1 x.2 }:= by
  simp only [Chosen,setOf_forall]; exact isClosed_iInter fun i=> isClosed_le (continuous_fst.dist (shade_cont.comp continuous_snd)) (continuous_fst.dist continuous_const)
lemma Chosen.gauge {H : Hue} {h : E} (p : Chosen H h) (a : E) : Chosen (spin a H) (h*a⁻¹):=by
  intro k; rw [shade_gauge, spin_dist]; nth_rw 1 [← mul_inv_cancel_right k a]; rw [shade_gauge,spin_dist]; exact p _
lemma Chosen.shift {H : Hue} {h k : E} (p : Chosen H h) (e : shade k=shade h): Chosen H k:= fun l=> by rw [e]; exact p l

/-- Distance to the orbit, tested by existence (the orbit is compact). -/
def Mood (δ : ℝ) := {H : Hue| ∃ h, dist H (shade h) ≤ δ }
lemma Mood.test (H : Hue) (h : E) (p : Chosen H h) (δ : ℝ) : H∈Mood δ ↔ dist H (shade h) ≤ δ := by
  constructor; · rintro ⟨i,v⟩; exact (p i).trans v
  intro g; exact ⟨h,g⟩
lemma mood_closed (δ : ℝ) : IsClosed (Mood δ):= by
  have he : IsClosed {x : Hue × E| dist x.1 (shade x.2) ≤ δ}:= isClosed_le (continuous_fst.dist (shade_cont.comp continuous_snd)) continuous_const
  rw [show Mood δ=Prod.fst '' {x : Hue × E| dist x.1 (shade x.2)≤δ} from by ext i; simp [Mood]]
  exact isClosedMap_fst_of_compactSpace _ he
lemma chosen_magnet (h : E) : Chosen magnet h ↔ ∃ i, h=center i:=by
 rw [← show (∃ i,h=center i*1) ↔ (∃ i,h=center i) by simp]; rw [← shade_rel,shade_one]; constructor
 · intro g; have e:=g 1; rw [shade_one,dist_self] at e; exact dist_le_zero.mp e
 intro e k; rw [←e,dist_self]; exact dist_nonneg -- worry e recursive

-- Nearest minimizers lie in center sheets on a small neighborhood of magnet:
-- they are ONE fiber (coset of the stabilizer), and we can find a representative with
-- an L1 estimate in terms of the distance to *magnet*, not the distance to the orbit.
-- radius of reference patch for this claim is uniform in data.
theorem near_magnet : ∃ ε K : ℝ, 0<ε ∧ 0<K ∧ ∀ H : Hue, dist H magnet ≤ ε →
    ∃ h : E, Chosen H h ∧ chord h 1 ≤ K * dist H magnet ∧ ∀ k : E, Chosen H k → shade h=shade k := by
  obtain ⟨K,a,s,t,g⟩:= strict_lower (picture_diff.hasStrictFDerivAt (x:=0) (by simp)) picture_injD
  obtain ⟨C,W,r,c⟩:= group.exp_jet.hasStrictFDerivAt (x:=0) (by simp)|>.exists_lipschitzOnWith
  obtain ⟨v,l,Q,p,e⟩:= unique_stationary picture_diff picture_injD; rw [picture_zero] at l; obtain ⟨δ,b,o⟩:= Metric.mem_nhds_iff.mp l
  let V := W∩s∩Q; have hV : V∈𝓝 0:=inter_mem (inter_mem r t) p
  let P:=Inv.inv ⁻¹' (group.lieExp '' V); have he : P∈𝓝 (1:E):=by
    have hp: group.plog ∘ group.mat = LocalH.snap group:=rfl -- plog inverts
    have ht: Tendsto (group.plog ∘ group.mat) (𝓝 (1:E)) (𝓝 0):= by
      have he:= group.plog_diff.continuousAt.tendsto
      rw [group.plog_one] at he -- continuousAt?
      exact he.comp (show Tendsto group.mat (𝓝 1) (𝓝 1) from group.continuous_mat.tendsto _)
    apply (show ContinuousAt (Inv.inv : E→E) 1 from continuous_inv.continuousAt).preimage_mem_nhds; rw [inv_one]
    exact ((show ∀ᶠ x:E in 𝓝 1,(group.plog (group.mat x))∈V from ht hV).and group.plog_right).mono fun x h=>⟨_,h.1,h.2⟩
  -- compact uniform approach: every minimizer has a nearby sheet at the identity, can move using its center element.
  obtain ⟨P',hh,T,HQ⟩:= _root_.mem_nhds_iff.mp he
  let A : Set E:= ⋃ i:Fin 5, (fun x:E=> (center i)⁻¹*x) ⁻¹' P'; have hA : IsOpen A:=isOpen_iUnion fun i=> T.preimage (continuous_const.mul continuous_id)
  let D := Prod.fst '' ({x:Hue × E | Chosen x.1 x.2} ∩ Prod.snd ⁻¹' Aᶜ)
  have hm:IsOpen Dᶜ:= (isClosedMap_fst_of_compactSpace _ (chosen_closed.inter (hA.isClosed_compl.preimage continuous_snd))).isOpen_compl
  have hm':magnet∈Dᶜ:= by
    rintro ⟨⟨H,v⟩,⟨e,x⟩,f⟩; change H=magnet at f; change v ∉ A at x; subst H; obtain ⟨i,g⟩:=(chosen_magnet v).mp e; apply x; apply mem_iUnion.mpr; exact ⟨i,show _ from (show (center i)⁻¹*v∈P' from by rw [g, inv_mul_cancel]; exact HQ)⟩
  obtain ⟨u,d,Z⟩:= Metric.mem_nhds_iff.mp (hm.mem_nhds hm')
  let A' := (C:ℝ)/group.colorScale; have ht:0≤ A':= div_nonneg C.property group.colorScale_pos.le
  refine ⟨(min u δ)/2,1+A'* (2*K),half_pos (lt_min d b),by positivity, fun H L=>?_⟩
  have hx: H∈ v:= o (lt_of_le_of_lt L (lt_of_lt_of_le (half_lt_self (lt_min d b)) (min_le_right ..)))
  have entries (k:E)(l:Chosen H k) : ∃ x∈V, shade k=picture x:=by
    have e: k∈ A:= by by_contra ht; exact Z (mem_ball.mpr (lt_of_le_of_lt L ((half_lt_self (lt_min d b)).trans_le (min_le_left ..)))) ⟨(H,k),⟨l,ht⟩,rfl⟩
    obtain ⟨i,p⟩:= mem_iUnion.mp e; let t:=(center i)⁻¹*k; obtain ⟨x,s,f⟩:= show t⁻¹∈ group.lieExp '' V from hh p; exact ⟨x,s,by rw [picture,f,← show shade t = paint t⁻¹ from rfl, ←center_shade i t]; unfold t; rw [mul_inv_cancel_left]⟩
  obtain ⟨k,q⟩:=chosen_exists H; obtain ⟨x,j,f⟩:=entries k q; have hs: Chosen H ((group.lieExp x)⁻¹):= q.shift (by rw [f,shade,inv_inv]; rfl); refine ⟨_,hs,?_,?_⟩
  · have h1 := g x j.1.2 0 (mem_of_mem_nhds t); have h2 := q 1; rw [shade_one,f] at h2; rw [picture_zero] at h1; have hw := c.dist_le_mul x j.1.1 0 (mem_of_mem_nhds r); -- hx chase
    rw [←inv_one (G:=E),chord.inv] -- tune
    rw [chord.mat_eq]; apply le_trans (div_le_div_of_nonneg_right (b:= (C:ℝ)*dist x 0) ?_ group.colorScale_pos.le)
    · apply le_trans (b:= A' * (2*K) * dist H magnet) ?_ (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) dist_nonneg); have he:=h1.trans (mul_le_mul_of_nonneg_left (dist_triangle (picture x) H magnet) a.le); rw [dist_comm H (picture x)] at h2; change _ ≤ (C:ℝ)/_ * _*_; simp only [div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ group.colorScale_pos.le; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left ?_ C.property; nlinarith only [he,h2,a]
    rw [dist_eq_norm,group.mat_lieExp_zero] at hw; exact hw
  intro k p; obtain ⟨y,i,F⟩:= entries k p; have he (i:E) (p:Chosen H i) (a) (f : shade i=picture a) : IsLocalMin (fun x=> dist (picture x) H) a:= Eventually.of_forall fun x=> by
    have h:=p (group.lieExp x)⁻¹; rw [f,shade,inv_inv] at h; change dist _ H ≤ dist _ H; rw [dist_comm _ H,dist_comm _ H]; exact h
  have g : x=y:= e H hx x j.2 y i.2 (he _ q x f) (he _ p y F); rw [F, ←g,shade,inv_inv]; rfl

/-- Tube translates, same grant over all H in that tube. -/
theorem lift_purchase : ∃ ε K : ℝ, 0<ε ∧ 0<K ∧
    (∀ H∈Mood ε, ∀ h k, Chosen H h→ Chosen H k→ ∃ i, k=center i*h) ∧
    ∀ H : Hue, dist H magnet ≤ ε → ∃ h, Chosen H h ∧ chord h 1≤ K*dist H magnet := by
 obtain ⟨a,b,x,y,H⟩:= near_magnet; refine ⟨a,b,x,y,?_,fun h p=> (H h p).imp fun _ v=>⟨v.1,v.2.1⟩⟩
 intro F l h k d t; obtain ⟨i,e⟩:= l; let Z:= spin i F; have hx : dist Z magnet ≤ a:= by unfold Z; rw [← show spin i (shade i)=magnet from (by rw [shade,paint,spin_seq,mul_inv_cancel,spin_one]),spin_dist]; exact e
 obtain ⟨p,_,_,g⟩:= H Z hx
 obtain ⟨j,r⟩:=(shade_rel _ _).mp ((g _ (d.gauge i)).symm.trans (g _ (t.gauge i)))
 exact ⟨j,mul_right_cancel (r.trans (mul_assoc ..).symm)⟩

lemma center_price : ∃ γ : ℝ, 0<γ ∧ Pairwise fun i j=> γ≤ chord (center i) (center j):= by
  let S:= Finset.univ.filter fun i:Fin 5 × Fin 5=> i.1≠i.2; have h: S.Nonempty:=⟨(0,1),by simp [S]⟩
  let f(i:Fin 5 × Fin 5) := chord (center i.1) (center i.2); refine ⟨S.inf' h f, (Finset.lt_inf'_iff ..).mpr fun i v=>lt_of_le_of_ne (chord.positive ..) (fun g=>?_ ),fun i j p=> Finset.inf'_le f (b:=(i,j)) (by simp [S,p])⟩
  exact (Finset.mem_filter.mp v).2 (center_injective (chord.eq_of_zero _ _ g.symm))

-- default measurable section; parameter 0 means base. Later adjusted locally near center.
lemma choice_section : ∃ f : Hue→ E, Measurable f ∧ ∀ x, Chosen x (f x) := by
  letI : TopologicalSpace.MetrizableSpace group.Mat := inferInstanceAs (TopologicalSpace.MetrizableSpace (Fin group.repDim → Fin group.repDim → ℂ))
  letI : TopologicalSpace.MetrizableSpace E := (group.continuous_mat.isClosedEmbedding group.mat_injective).isEmbedding.metrizableSpace
  exact closed_selector _ chosen_closed chosen_exists
end YM.CF.BPress.Mag
