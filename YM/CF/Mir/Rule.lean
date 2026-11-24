import YM.CF.Mir.Action

/-! Law invariance and support geometry. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Mir.Trip
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Topology
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant MeasureTheory Phase Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} (b : Trip m)
lemma make_vote (z : Site (Domain m B)) (x : Index m) (t) : ballot m B (run B b z) (b.adv x) t ↔ ballot m B z x t := by
  have hk (x:Index m) (z:Site (Domain m B)) (i) : elect m B (z i) t (x i)↔ delta1 _ (z i) (address m B x i)≤radius m B (x i) t := by rw [address,high_here]; rfl
  unfold ballot; simp_rw [hk,addressAdv,b.level]; apply forall_congr'; intro i; by_cases h:OddAxis m (x i) <;> simp [radius,b.odd_rule,h]
lemma active_turn (z : Site (Domain m B)) (x : Index m) : b.adv x∈active m B (run B b z) ↔ x∈active m B z := by simp_rw [active_iff,make_vote]
abbrev shiftI (b : Trip m) (i : Spot m) : Spot m := (b.adv i.1,i.2)
def shiftE : Equiv.Perm (Spot m) := b.facesA.prodCongr (Equiv.refl _)
def riseF (s : ArrayF m) := s ∘ shiftI b
lemma shift_right (a:Spot m) : shiftI b (shiftI b⁻¹ a)=a := Prod.ext (adv_last ..) rfl
lemma market (B) (t : Sq) (a : Spot m) (x : Site (Domain m B)) : cash m B (run B b x) t (shiftI b a)=cash m B x t a := by
  simp only [cash,ticks,shiftI,b.make_vote]
lemma incentV (x y : Site (Domain m B)) (h : separation x y≤ B.val) : lift (run B b x-run B b y)=(glazed b.glare).act (lift (x-y)) := by
  rw [lift_eq_iff]; refine ⟨?_,?_⟩
  · rw [←wrap_signed,wrap_lift,Signed.act_sub,run,run,affine,affine,add_sub_add_right_eq_sub]

  intro i; rw [glaz]; have hu := (component_le (x-y) i).trans h; have hm := enough m B; have hB : 0<B.val := B.property; split <;> omega
lemma path_glow (x y : Site (Domain m B)) (h : separation y x ≤ B.val) (l : Lattice.Order) (U : Skin m B) :
    travel (through B b U) x (march x y l)=travel U (run B b x) (march (run B b x) (run B b y) l) := by
  let p := b.glare
  rw [through,travel_pull];
  have he (z:Cover) (a: List Axis) : (axisRoute 0 z a).map (fun i=>i.rotate (glazed p))=axisRoute 0 ((glazed p).act z) a := by
    induction a with
    | nil => simp [axisRoute]
    | cons i a ih =>
      rw [show axisRoute 0 z (i::a)=straight i (z i)++axisRoute 0 z a by simp [axisRoute],show axisRoute 0 _ (i::a)=straight i ((glazed p).act z i)++axisRoute 0 ((glazed p).act z) a by simp [axisRoute],List.map_append,ih,glaz]
      cases e:p i
      · simp [straight, Step.rotate,glazed,e]
      rcases lt_trichotomy (z i) 0 with hx|hx|hx
      · have hq : ¬-z i<0 := by omega
        simp [straight, Step.rotate, glazed,e,hx,hq,show ¬0<z i by omega]
      · simp [straight,hx]
      have hk : ¬ z i<0 := by omega
      simp [straight,hx,hk,Step.rotate,glazed,e]
  unfold march route; rw [incentV _ _ _ h]; exact congrArg _ (he _ _)
lemma fees_eq (s : ArrayF m) (q) (z : Site (Domain m B)) (U : Skin m B) : paintV m B (through B b U) (b.riseF s) q z=paintV m B U s q (run B b z) := by
  unfold paintV; apply congrArg ren; unfold paint
  rw [←Equiv.sum_comp b.shiftE (fun i=>cash m B (run B b z) q i • freight m B U (run B b z) i.1 (s i))]; refine sum_congr rfl ?_; intro i _
  change _=cash _ _ _ _ (shiftI b i) • _; rw [market]; by_cases e:i∈bandS m B z q
  · have hu := node_dist (spot_hit e)
    unfold freight; apply congrArg; apply congrArg; apply sum_congr rfl; intro l _
    change launch _ _ _ _ _ _ (s (shiftI b i))=launch m B U _ (adv b i.1) _ _; unfold launch tax
    rw [path_glow b _ _ ((separation_comm ..).trans_le hu.le), addressAdv]; rfl
  rw [outside e,zero_smul,zero_smul]

lemma tripsM (a c : Spot m) : Prev m (shiftI b a) (shiftI b c)↔Prev m a c := by
  unfold Prev; change Fits m (b.adv a.1) (b.adv c.1)∧a.2≤c.2∧(b.shiftE a≠b.shiftE c)↔_; rw [fits]; simp
abbrev appoint (r : Ramp m) : Ramp m := (shiftI b r.1,r.2)
lemma wind (l : List (Ramp m)) (a : Spot m) : Moves m (shiftI b a) (l.map b.appoint)↔ Moves m a l := by
  induction l generalizing a with
  | nil => exact Iff.rfl
  | cons x l ih => rw [List.map_cons,Moves]; change Prev m (shiftI b x.1) _∧ _ ↔ _; rw [tripsM]; exact and_congr_right (fun g=> ih x.1)
lemma wind_fit (l : List (Ramp m)) (a : Spot m) (r : Zone) : l.map b.appoint ∈ permits m (shiftI b a) r ↔ l∈permits m a r := by
  simp only [permits_iff,wind, InRows, List.forall_mem_map]
lemma winding (l : List (Ramp m)) : List.map b.appoint (l.map b⁻¹.appoint)=l := by
  rw [List.map_map,show b.appoint ∘ b⁻¹.appoint=id by funext x; exact Prod.ext (shift_right b x.1) rfl,List.map_id]
lemma train_turn (s : ArrayF m) {a : Spot m} (U : Skin m B) (l : List (Ramp m)) (p : Moves m a l) : train m B (through B b U) (b.riseF s) a.1 l=train m B U s (b.adv a.1) (l.map b.appoint) := by
  induction l generalizing a with
  | nil=> rfl
  | cons x l ih=>
    rcases x with ⟨x,c⟩
    have he : separation (address m B x.1) (address m B a.1) ≤ B.val := (separation_comm ..).trans_le (chain_near p.1.1 B)
    rw [List.map_cons,train,appoint,train, parcel,path_glow b _ _ he,parcel,ih p.2, addressAdv]
    change _=List.map (turn (travel U (run B b _) (march _ (address m B (adv b x.1)) c))) _; rw [addressAdv]; rfl
lemma paidR (r : Zone) (a : Spot m) (U : Skin m B) (s : ArrayF m) : Check m B margin (through B b U) (b.riseF s) r a ↔ Check m B margin U s r (shiftI b a) := by
  have he (g : Check m B margin (through B b U) (b.riseF s) r a) (l : List (Ramp m)) (h : l∈permits m (shiftI b a) r) : margin< ‖restrain margin (train m B U s (b.adv a.1) l) (s (shiftI b a)).val‖ := by
    have H : (l.map b⁻¹.appoint)∈permits m a r := (wind_fit b (l.map _) a r).mp (by rw [winding]; exact h)
    nth_rw 1 [←winding b l, ←train_turn b s (a:=a) U _ (permits_iff.mp H).1]; exact g _ H
  refine ⟨he,fun k l h=>?_⟩
  rw [train_turn b s (a:=a) _ l (permits_iff.mp h).1]; exact k _ ((wind_fit ..).mpr h)
lemma verified_turn (r : Zone) (U : Skin m B) (s : ArrayF m) : Verified m B margin (through B b U) (b.riseF s) r ↔ Verified m B margin U s r := by
  constructor
  · intro p a h; rw [←shift_right b a]; apply (paidR b r _ U s).mp; exact p _ h
  intro p a h; exact (paidR b r a U s).mpr (p _ h)
lemma twin_turn (x y) : twin m (oncue b x) (oncue b y)=b.riseF (twin m x y) := by funext i; cases i; unfold Phase.twin capRow oncue riseF; simp [shiftI,slot]
lemma term_turn (U : Skin m B) (x) : ZeroF m B (through B b U) (b.oncue x) ↔ ZeroF m B U x := verified_turn b {0} U (slot m x)
end YM.CF.Mir.Trip
