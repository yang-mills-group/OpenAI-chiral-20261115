import YM.CF.Reflect.Merged
import YM.Wilson.Law

/-! Reflection allocation of bosonic factors. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Sample Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} (i : Axis) (x y z : Pack m B)
def massR (m B : Side) (x : Pack m B) := Phase.law m B x.1 x.2
def will (m B : Side) (x : Pack m B) := Wilson.energy (G:=SU.group) x.1
def top (m B : Side) (β : ℝ) (x : Pack m B) := Wilson.bare (G:=SU.group) β x.1
@[fun_prop] lemma will_cont (m B) : Continuous (will m B) := Wilson.energy_cont.comp continuous_fst
lemma econ : will m B (tiedK m B i x y z)+will m B (tiedK m B i x z y)=will m B (tiedK m B i x y y)+will m B (tiedK m B i x z z) := by
  unfold will Wilson.energy; rw [←sum_add_distrib,←sum_add_distrib]; refine sum_congr rfl ?_; rintro ⟨p,k⟩ _
  let V (x y' z') := (tiedK m B i x y' z').1; let l := square k.val.1 k.val.2; let E (y' z') := travel (V x y' z') p l
  change SU.group.price (E y z)+SU.group.price (E z y)=SU.group.price (E y y)+SU.group.price (E z z)
  rcases stays p k.property.ne i with h|h
  · have he a b : E a b=E a a := travel_local p l _ _ (fun e h₁ h₂=> (strum i x a b a).gaugeS e (h _ h₁) (h _ h₂))
    rw [he y z,he z y]
  have he a b : E a b=E b b := travel_local p l _ _ (fun e h₁ h₂=> barter i x a b b e (h _ h₁) (h _ h₂)); rw [he y z,he z y,add_comm]
lemma ridgeM : massR m B (tiedK m B i x y z) * massR m B (tiedK m B i x z y)= massR m B (tiedK m B i x y y)*massR m B (tiedK m B i x z z) := by
  unfold massR Phase.law; rw [←prod_mul_distrib, ←prod_mul_distrib]; apply prod_congr rfl; intro a _
  let f (a : Index m) (v : Pack m B) := water m B v.1 a v.2
  let t := tiedK m B i x
  change f a (t y z)* f a (t z y)= f a (t y y)*f a (t z z)
  have he a (p:a∈seaM m i) (v w) : f a (t v w)=f a (t v v) := water_limit _ _ a _ _ ((strum i x v w v).labels.less (level_keep i p)) (fun e g h=>(strum i x v w v).gaugeS _ (plane_room i p g) (plane_room i p h))
  rcases plane_all a i with g|g
  · rw [he a g y z,he a g z y]
  have hk v w : f a (t v w)= f (revI m i a) (t w v) := by nth_rw 1 [show t v w=Pbar m B i (t w v) from (sew ..).symm]; exact water_turn (slideM m i) (t w v).1 (t w v).2 a
  have hp v w : f a (t v w)=f a (t w w) := by rw [hk v w,hk w w,he _ ((plane_turn ..).mpr g) w v];
  rw [hp y z,hp z y,mul_comm]
lemma welfare (t : Pack m B) : massR m B (Pbar m B i t)=massR m B t ∧ will m B (Pbar m B i t)=will m B t := ⟨law_turn .., Wilson.energy_pull ..⟩
def net (m B : Side) (β : ℝ) (x:Pack m B) := massR m B x*top m B β x
lemma decks (k) : net m B k (tiedK m B i x y z)^2=net m B k (tiedK m B i x y y)*net m B k (tiedK m B i x z z) := by
  let A := tiedK m B i x y z
  have he := welfare i A; have hu := econ i x y z; have hm := ridgeM i x y z
  unfold A at he; rw [sew] at he; rw [he.1] at hm; rw [he.2] at hu
  have hT : top m B k (tiedK m B i x y z)*top m B k (tiedK m B i x y z)= top m B k (tiedK m B i x y y)*top m B k (tiedK m B i x z z) := by
    unfold top Wilson.bare; rw [←Real.exp_add,←Real.exp_add,←mul_add,←mul_add]; unfold will at hu; rw [hu]
  rw [net,pow_two,mul_mul_mul_comm,hm,hT,mul_mul_mul_comm]; rfl
lemma net_pos (u : Pack m B) k : 0≤net m B k u := mul_nonneg (law_positive ..) (Wilson.bare_pos ..).le
lemma net_turn (u : Pack m B) k : net m B k (Pbar m B i u)=net m B k u := congrArg₂ ((· * ·) : ℝ→ℝ→ℝ) (welfare i u).1 (Wilson.bare_pull ..)
@[fun_prop] lemma net_cont (m B) k : Continuous (net m B k) := (Phase.law_cont m B).mul (Wilson.bare_cont k |>.comp continuous_fst)
-- restricted finite measure

def TallyR (m B : Side) (e β : ℝ) := {t:Pack m B|Guard t.1 e ∧ net m B β t≠0}
lemma tallyP {z : Pack m B} {e β} (h : z∈TallyR m B e β) : z∈payer m B e := ⟨h.1, law_rich m B _ _ (left_ne_zero_of_mul (show net m B β z≠0 from h.2))⟩
lemma tally_meas (m B e β) : MeasurableSet (TallyR m B e β) := MeasurableSet.inter (((cover_closed _ _).preimage (continuous_fst (Y:=Cue m))).measurableSet) ((isOpen_ne_fun (net_cont m B β) continuous_const).measurableSet)
lemma apt (e β : ℝ) : tiedK m B i x y z∈TallyR m B e β ↔ tiedK m B i x y y∈TallyR m B e β ∧ tiedK m B i x z z∈TallyR m B e β := by
  let T := tiedK m B i x; let V := net m B β
  have he : V (T y z)≠0 ↔ V (T y y)≠0 ∧ V (T z z)≠0 := by
    rw [← pow_ne_zero_iff (n:=2) (by decide), ← mul_ne_zero_iff, show V (T y z)^2= _ from decks i x y z β] -- tune
  change (_ ∧ V (T y z)≠0)↔(Guard (T y y).1 _ ∧ V (T y y)≠0)∧(Guard (T z z).1 _ ∧ V (T z z)≠0)
  rw [he,cap_pair]; exact ⟨fun ⟨⟨p,t⟩,q,g⟩=>⟨⟨p,q⟩,⟨t,g⟩⟩,fun ⟨⟨p,q⟩,t,g⟩=>⟨⟨p,t⟩,q,g⟩⟩
-- phase allocate by grid anchor membership.

def bonus (a : Index m) (i : Axis) : ℝ := if a∈seaM m i then (if a∈seaP m i then 1/2 else 1) else 0
def inPort {c : Phase.Part m B} (W : Scroll m B c) (i) (p : Pack m B) := ∑ k:FaceTerm m B,bonus (faceT k) i • programK W k p
lemma bonusP (a : Index m) : bonus (revI m i a) i+bonus a i=1 := by
  unfold bonus; have he := plane_all a i; have hk : revI m i a∈seaP m i ↔ a∈seaM m i := by rw [←plane_turn (revI m i a),map_back]
  have hp := plane_turn a i
  split_ifs <;> first | tauto | norm_num -- tune
lemma portPair {c : Phase.Part m B} (W : Scroll m B c) (x : Pack m B) : cabin W x=inPort W i x+ star (inPort W i (Pbar m B i x)) := by
  unfold cabin inPort
  rw [←Equiv.sum_comp (pivotM (B:=B) (slideM m i)) (fun k=>bonus _ i • programK W k (Pbar m B i x))]; -- tune underscore
  rw [star_sum, ←sum_add_distrib]; apply sum_congr rfl; intro k _
  let q := slideM m i
  change _= _ + star (bonus (faceT (pivot q k)) i • programK W (pivot q k) (onPack _ q x))
  rw [drop_off,fieldHit]; unfold q; rw [slide_flips,slide_inv,star_smul,star_star, star_trivial,←add_smul,add_comm, show bonus (adv _ _) i+_=1 from bonusP i (faceT k),one_smul]
lemma port_side {c : Phase.Part m B} {W : Scroll m B c} {u v d e : ℝ} (h : ScaleK u v W) (k : Budget B e d) {x y:Pack m B} (g : NorthOf m B i x y) (L:x∈payer m B e) (A:y∈payer m B e) : inPort W i x=inPort W i y := by
  apply sum_congr rfl; intro j _
  by_cases p:faceT j∈seaM m i; rw [program_face h k j L A (g.labels.less (level_keep i p)) (fun e x y=>g.gaugeS e (plane_room i p x) (plane_room i p y))]
  simp [bonus,p]
lemma ports {c : Phase.Part m B} {W : Scroll m B c} {u v d e β : ℝ} (h : ScaleK u v W) (k : Budget B e d) (f:tiedK m B i x y z∈TallyR m B e β) : cabin W (tiedK m B i x y z)=inPort W i (tiedK m B i x y y)+star (inPort W i (tiedK m B i x z z)) := by
  have he := (apt ..).mp f
  have hg := tallyP f
  rw [portPair,sew i,port_side i h k (strum i x y z y) hg (tallyP he.1), port_side i h k (strum i x z y z) (by rw [←sew]; exact dominated _ _ hg) (tallyP he.2)]
end YM.CF.RP
