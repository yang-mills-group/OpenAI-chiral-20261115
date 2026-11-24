import YM.SU5.Reconstruction.Chambers.Schedule
/-!
# Multipoint *full* projected readings in chambers

Temporal coherence with any permutation of slots spent. Recover all of each
j-axis's *spatial* projections in strict chambers, not just comparisons through
further orthogonal spaces. Analyticity & identification handled later. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.Chambers.Schedule
open Function Filter Set Metric NormedSpace MeasureTheory Analysis SelectionAnalysis OS Germ
open scoped Topology InnerProductSpace NNReal ENNReal Classical

variable {α : Type*} {H : Hilbert} {Γ : AddSubgroup ℝ}
variable {j : Axis}
local notation "Δ" j:max => {x:Axis // x≠ j}
local notation "R" => Axis→ℝ
local notation "M" => Axis→Γ
open Compose Fixture
-- Various shift flags for each gap, compare raw/unprojected exactly
variable (X : Sunbelt j Γ H) (S : OS.Semigroup H j) (hS : X.heat=S.E)
local notation "U" k:max=> ((X.track).crew k).play

def funded (B : α → List (Δ j)) (W : α→H.Op) (G : Fixture Γ α) (p : α → Axis → Γ) :
    (Axis→Γ) → List α → H.Op :=
  roll (fun i z=> (X.plane z).comp (X.track.stackS (B i))) W (G.beginAt j p) (G.depart j p)

def input (W : α→H.Op) (G : Fixture Γ α) (p : α → Axis → Γ) :
    (Axis→Γ) → List α → H.Op := roll (fun _ => X.plane) W (G.beginAt j p) (G.depart j p)

variable (G : Fixture Γ α) (B : α → List (Δ j)) (W : α→H.Op) (ω : H)
local notation "A" k:max t:max=> X.plane (G.beginAt j k t)
local notation "F" => funded X B W G
local notation "F₀" => input X W G

lemma empty_funds (t : List α) (h : ∀ i ∈ t,B i=[]) (p : α → Axis → Γ) (q : Axis→Γ) :
    F p q t=F₀ p q t := by
  induction t generalizing q with
  | nil=>rfl
  | cons i l ih=>
    unfold funded input; rw [roll_step,roll_step]; rw [h i (List.mem_cons_self ..)]; change ((X.plane _).comp _)=_
    rw [show roll _ W (G.beginAt j p) (G.depart j p) (G.depart j p i) l=input X W G p (G.depart j p i) l from ih (fun i a=>h i (List.Mem.tail _ a)) _]
    rfl

lemma vary_plane (p : Axis→Γ) (k : Δ j) (y : Γ) : X.plane (p+Pi.single k.val y)=(X.plane p).comp ((U k) y) := by
  let g := Function.update p k.val (p k.val+y)
  have h : (p+Pi.single k.val y)=g := by
    ext1 i; by_cases b : i=k.val; · simp [g,b]
    simp [g,b]
  rw [h,show X.plane p=X.plane (Function.update p k.val (p k.val)) by rw [Function.update_eq_self]]
  exact X.carries_spot p k (p k.val) (p k.val+y) y rfl

variable (p : α→Axis→Γ) (q r : Axis→Γ)

-- With stamp p,q and site s, vary entire tail list l. Recover previous projected
-- matrix expression on all valid mover positions. This variation of ONE gap lets us
-- keep the same price on the unaffected **data at all axes** thus use induction on flags.
-- decEq use classical fix (beware instance differences with user data and Compose vars).
def bend (p : α→Axis→Γ) (l : List α) (u : Axis→Γ) : α→Axis→Γ := fun i=> if i∈l then p i+u else p i

@[simp] lemma bend_zero (l:List α) : bend p l 0=p := by ext1 i; unfold bend; split <;> simp
@[simp] lemma bend_in {l : List α} {i} (h : i∈ l) : bend p l r i=p i+r := by simp only [bend,if_pos h]
@[simp] lemma bend_out {l : List α} {i} (h : i∉l) : bend p l r i=p i := by simp only [bend,if_neg h]

lemma alter_begin {x : α} {p z: α → Axis → Γ} (h : z x = p x+r) : G.beginAt j z x=G.beginAt j p x+r := by rw [beginAt,h]; unfold beginAt; abel
lemma alter_depart {x : α} {p z: α → Axis → Γ} (h : z x = p x+r) : G.depart j z x=G.depart j p x+r := by rw [depart, alter_begin G r h]; unfold depart; abel

lemma funds_alter (p' : α→Axis→Γ) (t : List α) (K : α → List (Δ j))
    (h : ∀ i∈ t, p' i=p i+r) (g : ∀ i∈ t,K i=B i) : funded X K W G p' (q+r) t=funded X B W G p q t := by
  induction t generalizing q with
  | nil=>rfl
  | cons i t ih=>
    have s := List.mem_cons_self (a:=i) (l:=t)
    have hh : G.beginAt j p' i-(q+r)=G.beginAt j p i - q := by rw [alter_begin G r (h i s)]; abel
    unfold funded; rw [roll_step,roll_step,hh, g i s,alter_depart G r (h i s)]
    specialize ih (G.depart j p i) (fun i e=> h i (List.Mem.tail _ e)) (fun i e=>g i (List.Mem.tail _ e))
    unfold funded at ih; rw [ih]

variable (v : α) (k : Δ j) (t l : List α)
-- matrix functional elementwise graph family for induction on prefix. use propagateCLM &
-- only insert the additional projection when confirmed.
-- need unaffected flags/trailing raw (same matrix W). Seta function classical.
def purchase (i : α) : α → List (Δ j) := fun v=> if v=i then k :: B i else B v
@[simp] lemma purchase_there : purchase B k v v=k :: B v := if_pos rfl -- binder order
@[simp] lemma purchase_miss {i} (p : i≠v) : purchase B k v i=B i := if_neg p

private def study (z : Γ) := bend p (v::l) (Pi.single k.val z)
local notation "p̂" z:max=> study p v k l z
-- dependent: U notation takes x then apply; Projection CLM via Players.pi_c.
local notation "Π" => ((X.track).crew k).pi_c
local notation "F'" => funded X (purchase B k v) W G
set_option maxHeartbeats 400000
lemma vary_tail (h : (t ++ v :: l).Nodup) :
    ∀ L : H.space →L[ℂ] ℂ, ∃ (E : H.space →L[ℂ] ℂ) (x : H),
      L (F' p q (t++v::l) ω) = E ( ((X.track).crew k).pi_c x) ∧
      ∀ z : Γ,L ((F (bend p (v::l) (Pi.single k.val z)) q (t++v::l)) ω) = E (((X.track).crew k).play z x) := by
  induction t generalizing q with
  | nil=>
    have h : v ∉ l := (List.nodup_cons.mp h).1
    intro L; let f := X.plane (G.beginAt j p v - q)
    let x: H := X.track.stackS (B v) (W v ((F p (G.depart j p v) l) ω))
    let A' := purchase B k v
    have hf : ∀ i∈ l,A' i=B i := by intro i z; exact (purchase_miss B v k (show i≠v from fun g=> h (g ▸ z)))
    refine ⟨L.comp f,x,?_,?_⟩
    · have he : F' p (G.depart j p v) l = F p (G.depart j p v) l := by
        simpa using funds_alter X G B W p (G.depart j p v) 0 p l (purchase B k v)
          (fun i _=>by simp) hf
      change L (funded X _ _ G p q (v::l) ω)=_
      unfold funded; rw [roll_step,purchase_there]; unfold funded at he; rw [he]; rfl
    intro z; let r':Axis→Γ:= Pi.single k.val z
    let p' := bend p (v::l) r'; have hp : p' v=p v+r' := bend_in p r' (List.Mem.head ..)
    have h' : G.beginAt j p' v - q= G.beginAt j p v-q+r' := by rw [alter_begin G r' hp]; abel
    have he: F p' (G.depart j p' v) l=F p (G.depart j p v) l := by
      rw [alter_depart G r' hp]; exact funds_alter X G B W p (G.depart j p v) r' p' l B
        (fun i e=> bend_in p r' (List.Mem.tail _ e)) (fun i _=>rfl)
    change L ( (F p' q (v::l)) ω ) =_
    unfold funded; rw [roll_step,h',vary_plane X (G.beginAt j p v - q) k z]; unfold funded at he; rw [he]; rfl
  | cons i t ih=>
    obtain ⟨g,h⟩ := List.nodup_cons.mp h
    have v' : i ≠ v := fun w=> g (List.mem_append_right _ (by exact w.symm ▸ List.Mem.head ..))
    have r : ∀ z : Γ, (bend p (v::l) (Pi.single k.val z)) i=p i := fun _=> bend_out p _ (fun hm=> g (List.mem_append_right _ hm))
    intro L; let u₁ := G.beginAt j p i; let u₂ := G.depart j p i
    let T := L.comp (( (X.plane (u₁-q)).comp (X.track.stackS (B i))).comp (W i))
    obtain ⟨Q,b,a,c⟩ := ih u₂ h T
    refine ⟨Q,b,?_,?_⟩
    · change L ((F' p q (i:: (t++v::l))) ω)=_
      unfold funded; rw [roll_step,purchase_miss B v k v']; exact a
    intro z; change L ((F (p̂ z) q (i:: (t++v::l))) ω)=_
    unfold funded; rw [roll_step,show G.beginAt j (p̂ z) i=u₁ by unfold u₁ beginAt study; rw [r],
      show G.depart j (p̂ z) i=u₂ by unfold u₂ depart beginAt study; rw [r]]
    exact c z

lemma actor_continuous {D E E₂ : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace D] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    (V : D → E →L[ℂ] E₂) (C : ℝ) (c : 0 < C) (β : ∀ z x,‖(V z) x‖≤C*‖x‖) (ty : ∀ x,Continuous (fun z => V z x))
    (W : D→E) (h : Continuous W) : Continuous fun z=> V z (W z) := by
  refine continuous_iff_continuousAt.mpr fun x=> ?_
  refine Metric.tendsto_nhds.mpr fun ε hv => ?_
  filter_upwards [Metric.tendsto_nhds.mp ((ty (W x)).tendsto x) _ (half_pos hv), Metric.tendsto_nhds.mp (h.tendsto x) ((ε/2)/C) (div_pos (half_pos hv) c)] with y b he
  apply lt_of_le_of_lt (dist_triangle _ (V y (W x)) _) ((add_lt_add ?_ b).trans_le (le_of_eq (add_halves ε)))
  rw [dist_eq_norm,←map_sub]; rw [dist_eq_norm] at he
  exact (β y _).trans_lt (by rw [mul_comm]; exact (lt_div_iff₀ c).mp he)

lemma enter_bend_cont (q : Axis) (l : List α) : Continuous (fun z:Γ=> enter (bend p l (Pi.single q z))) := by
  apply continuous_pi; intro i; apply continuous_pi; intro u
  by_cases h:i∈l
  · by_cases b:u=q
    · subst u; unfold enter paste; simp_rw [bend_in _ _ h,Pi.add_apply,Pi.single_eq_same]; fun_prop
    unfold enter paste; simp_rw [bend_in _ _ h,Pi.add_apply,Pi.single_eq_of_ne b,add_zero]; exact continuous_const
  unfold enter paste; simp_rw [bend_out _ _ h]; exact continuous_const

-- continuity in a temporal gap change (may affect MULTIPLE gaps in *that* chart due to order)
-- Need heat by hypothesis, enough. No continuity in the other coordinates used.
include S hS in
lemma varying_time_raw (l' : List α) {X' : Type*} [TopologicalSpace X']
    (d : X' → Axis → Γ) (y : X' → α → Axis → Γ) (u : X' → H)
    (j0 : ∀ z z' : X',∀ i : Δ j, d z i.val = d z' i.val ∧ ∀ a:α, y z a i.val=y z' a i.val)
    (a : Continuous (fun z => paste (d z))) (b : Continuous (fun z => enter (y z))) (h : Continuous u) :
    Continuous (fun z=> (input X W G (y z) (d z) l') (u z)) := by
  induction l' generalizing d with
  | nil=> exact h
  | cons i l ih=>
    by_cases hv : IsEmpty X'
    · exact continuous_iff_continuousAt.mpr (fun x => (hv.false x).elim)
    let z' := Classical.choice (not_isEmpty_iff.mp hv)
    let k(z:X') := fun i':Δ j=> (G.beginAt j (y z) i-d z) i'.val
    have hg(z) : k z=k z' := by
       ext1 a; change y z i a.val +_-_ = _; simp only [k,beginAt,Pi.add_apply,Pi.sub_apply,(j0 z z' a).1,(j0 z z' a).2 i]
    let A''(z:X') := (input X W G (y z) (G.depart j (y z) i) l) (u z)
    have he : Continuous A'' := by
       apply ih _ (fun z z' a=>⟨?_,(j0 z z' a).2⟩)
       · simp_rw [paste_depart]; exact (G.stop_cont j i).comp b
       simp only [depart,beginAt,Pi.add_apply,(j0 z z' a).2 i]
    let γt(z:X') := Real.toNNReal (((G.beginAt j (y z) i-d z) j:Γ):ℝ)
    have hx(z:X') : X.plane (G.beginAt j (y z) i-d z)=(S.E (γt z)).comp (X.track.raw X.list (k z')):= by unfold Sunbelt.plane; rw [hS,← hg z]
    unfold input; simp_rw [roll_step, ContinuousLinearMap.comp_apply, hx,ContinuousLinearMap.comp_apply]; -- parentheses
    apply actor_continuous (V:=fun z=> S.E (γt z)) 1 zero_lt_one
      (fun z u=> ((S.E _).le_opNorm _).trans (mul_le_mul_of_nonneg_right (S.shrinks _) (norm_nonneg _))) ?_
      (fun z=> (X.track.raw X.list (k z')) (W i (A'' z))) ?_
    · intro x; apply (S.continuousE x).comp
      apply continuous_real_toNNReal.comp; change Continuous fun z=>paste (G.beginAt j (y z) i-d z) j
      simp_rw [paste_sub,paste_begin]; exact (continuous_apply j).comp (((G.start_cont j i).comp b).sub a)
    exact (X.track.raw X.list (k z')).continuous.comp ((W i).continuous.comp he)

-- inspect universal comparison assumptions. can leave p external (weak derivatives budgets)
section token
variable (Y : Axis→Hilbert)
  (V : ∀ k:Axis, Sunbelt k Γ (Y k))
  (T : ∀ k:Axis, OS.Semigroup (Y k) k)
  (a : ∀ k:Axis,(V k).heat=(T k).E)
variable (β σ : (k:Axis)→ (Y k)) (C : (k:Axis) → α → (Y k).Op)
variable (O : Axis→List α) (q' : Axis→Axis→Γ)
local notation "K" i:max => input (V i) (C i) G
local notation "E₁" p:max i:max => inner ℂ (β i) ((K i) p (q' i) (O i) (σ i))

local notation "τ" x:max=> enter x ∈ G.ready q' O

variable (uCash : (α → Axis → Γ) → ℂ)
def agrees (B : α → List (Δ j)) : Prop :=
  ∀ p : α→Axis→Γ, enter p∈G.ready q' O → uCash p = inner ℂ (β j) ((funded (V j) B (C j) G p (q' j) (O j)) (σ j))

-- check v order & k implicit. Use the **open** strict scope to justify small bends even
-- when every positive bend of large size would violate order.
variable (o : (O j).Nodup) (hCash : ∀ p' : α→Axis→Γ, enter p' ∈ G.ready q' O → ∀ i : Axis,
  uCash p' = inner ℂ (β i) ((input (V i) (C i) G p' (q' i) (O i)) (σ i)))
local notation "onBud" => agrees G Y V β σ C O q' uCash
include hCash T a o
lemma transaction (k : Δ j) (v : α) (e : v∈ O j) (h : agrees G Y V β σ C O q' uCash B) :
    agrees G Y V β σ C O q' uCash (purchase B k v) := by
  obtain ⟨l,l',ε⟩ := List.append_of_mem e
  intro p b
  rw [h p b, ε]
  let u(z:Γ) := bend p (v::l') (Pi.single k.val z)
  obtain ⟨E,t,f,g⟩ := vary_tail (V j) G B (C j) (σ j) p (q' j) v k l l' (ε ▸ o) (innerSL ℂ (β j))
  let y:= k.val; let C'(z: Γ):= inner ℂ (β y) (((K y) (u z) (q' y) (O y)) (σ y))
  let c : Continuous (fun z=>enter (u z)) := enter_bend_cont p k.val (v::l')
  have h0:u 0=p:= by unfold u; rw [Pi.single_zero, bend_zero]
  have hv : ∀ᶠ z in 𝓝 0, enter (u z)∈G.ready q' O := c.continuousAt (G.ready_open q' O|>.mem_nhds (h0.symm ▸ b))
  let P := (V j).track.crew k
  have Hp : ContinuousAt (fun z=> E (P.play z t)) 0 := by
    have hk : Continuous C' := continuous_const.inner (varying_time_raw (V y) (T y) (a y) G (C y) (O y) (fun _=> q' y) u (fun _=> (σ y)) ?_ continuous_const c continuous_const)
    · refine hk.continuousAt.congr ?_
      filter_upwards [hv] with z w
      unfold C'; rw [← hCash (u z) w y,h (u z) w,ε]; exact g z
    intro i i' t; refine ⟨rfl,fun x=>?_⟩
    by_cases h:x∈ v::l'; simp only [u,bend,h,if_true,Pi.add_apply,Pi.single_eq_of_ne (show t.val≠ k.val from t.property),add_zero]
    simp only [u,bend,h,if_false]
  have h₀ := g 0; change inner ℂ (β j) _ = E (P.play 0 t) at h₀
  rw [P.play_zero] at h₀ -- at target tweak u hidden
  simp only [Pi.single_zero, bend_zero] at h₀; exact h₀.trans ((P.retain E t Hp).symm.trans f.symm)

lemma projected (p : α→Axis→Γ) (k : enter p ∈ G.ready q' O) :
    uCash p=inner ℂ (β j) (funded (V j) (fun _=> (V j).list) (C j) G p (q' j) (O j) (σ j)) := by
  -- or ANY stack schedule!
  suffices hg : ∀ t : List α,(∀ i∈t,i∈ O j)→ t.Nodup →
    ∀ (Z : α→ List (Δ j)), (∀ i ∉ t,Z i=[]) → agrees G Y V β σ C O q' uCash Z by
    let Z(i:α):= if i∈O j then (V j).list else []
    have hh := hg (O j) (fun i h=>h) o Z (fun i h=> if_neg h) p k
    have e := funds_alter (V j) G Z (C j) p (q' j) 0 p (O j) (fun _=> (V j).list)
       (fun i _=> by simp) (fun i t=> (if_pos t).symm)
    rw [add_zero] at e; rwa [e]
  intro l; induction l with
  | nil =>
     intro _ _ Z h p b; rw [hCash p b j,empty_funds (V j) G Z (C j) (O j) (fun i _=>h i List.not_mem_nil)]
  | cons i t ih=>
     intro p n Z h
     generalize zt: Z i=u
     induction u generalizing Z with
     | nil=>
        refine ih (fun i g=>p i (List.Mem.tail _ g)) (List.nodup_cons.mp n).2 _ (fun j b=> ?_)
        by_cases a:j=i; · exact a.symm ▸ zt
        exact h j (by simp [a,b])
     | cons x u h'=>
        let y(z:α):= if z=i then u else Z z
        have hp : agrees G Y V β σ C O q' uCash y := h' y (fun k t=>?_) (if_pos rfl)
        · have e : Z=purchase y x i := funext fun k => by by_cases h:k=i <;> simp [y,purchase,h,zt]
          rw [e]; exact transaction G y Y V T a β σ C O q' uCash o hCash x i (p _ (List.Mem.head ..)) hp
        have g : k≠ i:=fun e=> t (e.symm ▸ List.Mem.head ..); unfold y; rw [if_neg g,h k t]
end token
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.Chambers.Schedule
