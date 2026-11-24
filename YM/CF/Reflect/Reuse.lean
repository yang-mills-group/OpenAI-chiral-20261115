import YM.CF.Reflect.View
import YM.Wilson.Symmetry

/-! Command and gauge equivariance, uses exactly the same allocated scalar and cuts. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.RP
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology BoundedContinuousFunction ComplexOrder
open Function Fock Filter NormedSpace SU Lat Lattice Branch Cube Tenant Phase Mir Mir.Trip MeasureTheory Finset Reflect
attribute [local instance] opCStarAlgebra
section basic
variable {N m B : Side}
lemma leaf_base (N) : filled (cutM (upperP N)) (Cfield (uniqueR N))=linearB N := by rw [filled,cutLine,cut_oneAct]; rfl
lemma turnsV (U : UNI (Model N)) (h : twist U (cutM (upperP N))=cutM (upperP N)) (g : congrC U (Cfield (uniqueR N))=Cfield (uniqueR N)) : acts (quantU U).val (linearB N)=linearB N := by rw [←leaf_base, ←filled_twist,h,g]
lemma fixedSign (p q : Site N) : acts (quantU (fringe p q)).val (linearB N)=linearB N := turnsV _ (by rw [plane_diag,view_fringe]) (grade_fringe p q _)
lemma fixedPerm (p : Equiv.Perm (Site N)) : acts (quantU (siteM p)).val (linearB N)=linearB N := turnsV _ (by rw [plane_diag,siteSpin]) (by rw [siteField]; rfl)
lemma newbill (b : Trip m) (β) (x : Pack m B) : net m B β (onPack B b x)= net m B β x := by
  unfold net massR top; dsimp only [onPack]; rw [law_turn]; exact congrArg _ (Wilson.bare_pull ..)
lemma val_trip (b : Trip m) : MeasurePreserving (onPack B b) (wheel m B) (wheel m B) := (Wilson.prior_pull (glazed b.glare) (n:=Domain m B) (torShift B b) (G:=SU.group)).prod b.rains_p
lemma use_trip {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] (b : Trip m) (v : Pack m B→Z) : (∫ x,v (onPack B b x) ∂wheel m B) = ∫ x,v x ∂wheel m B := by
  let f : Pack m B ≃ₜ Pack m B :=
    { toFun:=onPack B b
      invFun := onPack B b⁻¹
      left_inv := fun x=>by rw [trip_comp,mul_inv_cancel,pack_id]
      right_inv:= fun x=>by rw [trip_comp,inv_mul_cancel,pack_id]
      continuous_toFun := b.convey _
      continuous_invFun := b⁻¹.convey _ }
  exact (val_trip b).integral_comp f.measurableEmbedding _
lemma turn_ineq (a : Trip m) (t : Pack m B) {e β} : t∈ TallyR m B e β ↔ onPack B a t∈ TallyR m B e β := by
  have he a t (h:t∈TallyR m B e β) : onPack B a t∈TallyR m B e β := ⟨through_guard a h.1, fun g=> h.2 ((newbill a β t).symm.trans g)⟩
  refine ⟨he a t,fun h=>?_⟩; have hp:= he a⁻¹ _ h; rw [trip_comp,mul_inv_cancel,pack_id] at hp; exact hp
lemma bra (U : UNI (Model N)) (h : acts (quantU U).val (linearB N)=linearB N) (p : FC (Model N)) (v : Wave (Model N)) : inner ℂ (linearB N) (acts (twist (quantU U) p) (acts (quantU U).val v)) = inner ℂ (linearB N) (acts p v) := by rw [←swivel]; nth_rw 1 [← h]; exact act_unit_inner ..
lemma quant_flow (U : UNI (Model N)) (A : Op (Model N)) (t : ℝ) : twist (quantU U) (quant (grow A t))= quant (grow (twist U A) t) := by rw [←quant_twist,grow,breeze_exp,map_smul]; rfl
end basic

variable {m B : Side} {c : Phase.Part m B} {A D d e β : ℝ} {W : Scroll m B c}
variable (H : ScaleK A D W) (g : Budget B e d)
lemma from_to (p q:Foot m B) (t a:ℝ) (x : Pack m B) (f f' : Test m B) (h : twist (quantU (fringe p q)) (f x)=f' x) : ratioR W e β t a p f x=ratioR W e β t a q f' x := by
  unfold ratioR; by_cases k:x∈TallyR m B e β <;> try simp [k]
  unfold amplitude
  let U := fringe p q; let A := wiel m B p x.1; let P := quantU U; let C := pair m B x.1 x.2
  have he : twist U A=wiel m B q x.1 := swingFringe p q _
  apply congrArg; change _=inner ℂ _ (acts (f' x*quant _) (pairWave C)); rw [←h,←he,←quant_flow];
  have hy : acts P.val (pairWave C)=pairWave C := (pair_cov U.val C).trans (congrArg (pairWave (n:=Xmind m B)) (grade_fringe p q _))
  change inner ℂ _ (acts (f x*_ ) (pairWave C))=inner ℂ _ (acts (twist P _*twist P _) (pairWave C)); rw [←map_mul]; nth_rw 2 [←hy]; exact (bra U (fixedSign p q) _ _).symm
lemma bill_rot (v : Foot m B) (i : Trip m) (x : Pack m B) (b : ∀ j,i.glare j=false) (f f' : Test m B) (h : f' (onPack B i x)= twist (quantU (siteM (fperm m B i))) (f x)) (t a:ℝ) :
    ratioR W e β t a (far B i v) f' (onPack B i x)=ratioR W e β t a v f x := by
  unfold ratioR; by_cases k:x∈TallyR m B e β
  · rw [Set.indicator_of_mem k, Set.indicator_of_mem ((turn_ineq i x).mp k)]; unfold amplitude; rw [newbill,shakes,show ∀ z,i.flips z=z from fun z=>by simp [flips,b]]
    let q := onPack B i x; let U := siteM (fperm m B i); let P := quantU U; let S := pair m B x.1 x.2
    have hu : wiel m B (far B i v) q.1= twist U (wiel m B v x.1) := (careH i b _ v).symm
    have hh : pair m B q.1 q.2=congrC U S := by
      have he s t : bow m B (through B i x.1) (i.riseF s) t=congrC U (bow m B x.1 s t) := by rw [bow,played, ←siteField]; rfl
      exact he (slot m x.2) (stick 0)
    rw [hu,h, ←quant_flow,hh]; apply congrArg
    change inner ℂ _ (acts (twist P _*twist P _) (pairWave _))=_; rw [←map_mul]
    unfold congrC; rw [←pair_cov]; exact bra U (fixedPerm _) _ _
  rw [Set.indicator_of_notMem k, Set.indicator_of_notMem (fun l=>k ((turn_ineq i x).mpr l))]
-- displaced square in fixed canonical seam. f in translated coordinates at corresponding seam.
def northTrip (m : Side) (v : Site (More m)) : Trip m := ⟨fun _=>false,v⟩
def portal (m B : Side) (v : Site (More m)) (l : Foot m B) (i : Axis) := axisCut m B i (far B (northTrip m v) l)
-- where reflection plane lands via northTrip (magnitude). phase seam intertwine both. define test pulled into original coordinates.
def costarU (m B : Side) (v : Site (More m)) (l : Foot m B) (i : Axis) :=
    let t := northTrip m v; fringe (far B t l) (portal m B v l i)* siteM (fperm m B t)
def squareR (m B : Side) (v : Site (More m)) (l : Foot m B) (i : Axis) (f : Test m B) (b : Bool) : Test m B := fun x =>
    twist (star (quantU (costarU m B v l i))) (fiscal m B i f b (onPack B (northTrip m v) x))
include H g
lemma displacement (v : Site (More m)) (l : Foot m B) (i : Axis) (t a : ℝ) (k : 0≤t) (f b) (h : OfferedF m B i f b) :
    0 ≤ rawE W e β t a l (squareR m B v l i f b) := by
  let I := northTrip m v; let T := far B I l; let y := axisCut m B i T; let p := siteM (fperm m B I); let q := fringe T y
  let F := squareR m B v l i f b; let G := fiscal m B i f b
  let J := fun x => twist (star (quantU q)) (G x)
  have he x : ratioR W e β t a l F x=ratioR W e β t a y G (onPack B I x) := by
    let z := onPack B I x
    have hp (U : UNI (Finset (Model (CSide m B)))) (A : FC (Model (CSide m B))) : twist U (twist (star U) A)=A := by simpa only [star_star] using twist_inv (star U) A
    apply Eq.trans _ (from_to T y t a z J G (hp ..))
    apply (bill_rot l I x (fun _=>rfl) F J _ t a).symm
    let v := quantU p; let w := quantU q
    have ht : quantU (q*p) = w*v := Subtype.ext (quant_mul _ _)
    change twist (star w) _=twist v (twist (star (quantU (q*p))) _); rw [ht,star_mul,Fock.twin,hp]
  unfold rawE; change 0≤ ∫ x,ratioR W e β t a l F x ∂_; simp_rw [he]; rw [use_trip I (ratioR W e β t a y G)]; exact crossing_nonnegative β H g T t k a i f b h
end YM.CF.RP
