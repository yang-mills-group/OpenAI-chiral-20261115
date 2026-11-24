import YM.CF.Ave.Life

/-! The exponent for regulator terms. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Ave
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology
open Fock SU Lat Cube Phase Phase.Sample Mir RP MeasureTheory NormedSpace Branch Lattice Tenant Function Pastry Petal Manifest Filter Finset
attribute [local instance] opCStarAlgebra
variable {m B : Side} {c : Foot m B} {W : Scroll m B c} {a d e v q H k b τ : ℝ}
abbrev Capital (m B : Side) := Stamp m B ⊕ (FaceTerm m B ⊕ Stamp m B)
abbrev fupport (m B : Side) : Capital m B→ Stamp m B := Sum.elim id (Sum.elim driftK id)
def vacantT {c : Foot m B} (W : Scroll m B c) (v b : ℝ) (w : Stamp m B→ℝ) : Capital m B→ℝ := Sum.elim (fun S=>‖1-b‖*W.mint S) (Sum.elim (fun S=> ‖b‖*coinK W v S) w)
def fenced {c : Foot m B} (W : Scroll m B c) (b : ℝ) (F : Stamp m B→ Train m B e → Ewe m B) : Capital m B→Train m B e→ Ewe m B := Sum.elim (fun S x=>hollow ((1-b) • W.value S none (release x))) (Sum.elim (fun S x=>hollow (b • seedK W S (release x))) F)
def hover (m B : Side) (k u : ℝ) := Real.exp (k*21^4) * (16*(7*(B.val:ℝ)+1)^4*(u+(way B:ℝ)*u))
lemma notch (g : RunsB m B c W a d v e (k+2) (1/32)) (p : 1≤ H) {C : Stamp m B→ℝ} {F} (L : Construct m B H p e τ c (k+2) (1/16) F C) (ht : ‖b‖≤1) (hb : ‖1-b‖*hover m B (k+2) d ≤ 1/32) (U : (k+2)*21^4≤ a*(B.val:ℝ)) (Z : 0≤d) (K : 0<k) : Team (welter m B e H p) (terr _) (travel m B e H p) (pavilion m B ∘ fupport m B) (chairs m B ∘ fupport m B) (vacantT W v b C) (fenced W b F) univ k := by
  have E S:= subsidy g.budget g.scaleK S (1-b); have J S:= shake g.budget g.scaleK S b
  refine ⟨K,fun i _ h=>?_,fun i _=>?_,fun x=>?_⟩
  · rcases i with i|(i|i); exact pad_grove (m:=m) (B:=B) ((E i).2.2.2.2.1 h); exact pad_grove (m:=m) (B:=B) ((J i).2.2.2.2.1 h); exact pad_grove (m:=m) (B:=B) (L.bought i h)
  · rcases i with i|(i|i); exact curried p (E i); exact curried p (J i); exact L.serve i
  unfold hose; rw [sum_filter,Fintype.sum_sum_type,Fintype.sum_sum_type] -- tune
  let n := k+2; let V := pavilion m B
  let Q (S:Stamp m B) (w:ℝ) := if x∈V S then rent n (V S)*w else 0
  have Hq (S:Stamp m B) (w b:ℝ) : Q S (b*w)=b*Q S w := by unfold Q; split <;> first | exact mul_left_comm ..| rw [mul_zero]
  have hu (P:Stamp m B→ℝ) : ∑ i,Q i (P i)=cellHit m B n P x := by unfold cellHit spotHit; rw [sum_filter]
  change (∑ i:Stamp m B,Q i (‖1-b‖*W.mint i)) + ((∑ i:FaceTerm m B, Q (driftK i) (‖b‖*coinK W v i)) + ∑ i:Stamp m B, Q i (C i)) ≤ _
  simp_rw [Hq]; rw [←mul_sum, ←mul_sum,hu,hu]
  have he := (mul_le_mul_of_nonneg_left (motorFee (v:=0) g.budget g.scaleK Z U (by linarith) x) (norm_nonneg (1-b))).trans hb
  have hx : ‖b‖ * ∑ i:FaceTerm m B,Q (driftK i) (coinK W v i) ≤ 1/32 := by
    change _*markHit W v n x ≤ _; exact (mul_le_mul_of_nonneg_left (g.costs x) (norm_nonneg _)).trans (mul_le_of_le_one_left (by norm_num) ht)
  exact (add_le_add he (add_le_add hx (L.spends x))).trans (by norm_num)
lemma hollow_add (s t:ℂ) : hollow (n:=Hearth m B) s+hollow t=hollow (s+t) := Subtype.ext (by change s•1+t•(1:FC (Hearth m B))=(s+t) • 1; rw [add_smul])
lemma hollow_sum {I : Type*} (A : Finset I) (x : I→ℂ) : ∑ i∈A,hollow (n:=Hearth m B) (x i)=hollow (∑ i∈A,x i) := by
  classical
  induction A using Finset.induction_on with
  | empty=> rw [sum_empty,sum_empty]; apply Subtype.ext; change (0:FC (Hearth m B))= (0:ℂ) • 1; rw [zero_smul]
  | insert i A u ih=> rw [sum_insert u,sum_insert u,ih]; exact hollow_add ..
def chargeS {c : Foot m B} (W : Scroll m B c) (b : ℝ) (x : Pack m B) := fund m B c x.1 x.2-b • cabin W x
def carry (m B : Side) (x : Ewe m B) (z:ℂ) := hollow z+x
def chili {c : Foot m B} (W : Scroll m B c) (b τ : ℝ) (v : Train m B e) := carry m B (retire m B c τ v) (chargeS W b (release v))
lemma ripeX {p : 1≤H} (L : ScaleK a d W) (V : Budget B e q) {r : ℝ} {F K} (A : Construct m B H p e τ c k r F K) {x : Train m B e} (g : x∈Breath m B e) (b:ℝ) : ∑ i, fenced W b F i x=chili W b τ x := by
  rw [Fintype.sum_sum_type,Fintype.sum_sum_type]; let T := release x
  change ∑ S:Stamp m B, hollow (n:=Hearth m B) ((1-b) • W.value S none T) + ((∑ S:FaceTerm m B,hollow (n:=Hearth m B) (b • seedK W S T))+∑ i:Stamp m B, F i x)=_
  have ht : T∈payer _ _ _:= pays g
  rw [hollow_sum,hollow_sum,A.inventory x g, ←add_assoc,hollow_add, ←smul_sum,←smul_sum,taxed L V.1 ht,←net_sum L V ht]; unfold chili carry
  rw [show (1-b) • fund m B c T.1 T.2+b • (fund m B c T.1 T.2 - cabin W T)=chargeS W b T by unfold chargeS; rw [sub_smul,one_smul,smul_sub]; abel]
-- intensive weights in the identical finite family
structure FormR (W : Scroll m B c) (H : ℝ) (p : 1 ≤ H) (e v : ℝ) (K : Seal (Index m)→ Briar m B e→Ewe m B) (w : Seal (Index m)→ℝ) (t b : ℝ) : Prop where
  fine : Charge (welter m B e H p) (terr _) (v/2) (bulk v 16*(1/3)) K w
  paid (x : Briar m B e) : (motor (travel m B e H p) (fun y:Train m B e=>exp (chili W b t y)) x)=exp (∑ S:Seal (Index m),K S x)
lemma accordR (g : RunsB m B c W a d v e (k+2) (1/32)) (p : 1≤ H) {C : Stamp m B→ℝ} {F} (L : Construct m B H p e τ c (k+2) (1/16) F C) (ht : ‖b‖≤1) (hb : ‖1-b‖*hover m B (k+2) d ≤ 1/32) (U : (k+2)*21^4≤ a*(B.val:ℝ)) (Z : 0≤d) (K : 0<k) : ∃ G w, FormR W H p e k G w τ b := by
  have he := notch g p L ht hb U Z K
  obtain ⟨G,w,p,q⟩:= hospital he (C:=16) (by norm_num) (fun x=>reach x) -- reach name
  refine ⟨G,w,p,fun x=>?_⟩; rw [← q]
  unfold motor; apply integral_congr_ae; apply Eventually.of_forall; intro i
  unfold bet
  by_cases k : (x,i)∈ Breath m B e
  · simp only [ripeX g.scaleK g.budget L k b] -- tune
  change ¬ law m B x.val i≠0 at k; have ht := not_not.mp k
  change law m B x.val i • _ = law m B x.val i • _; rw [ht,zero_smul,zero_smul]
end YM.CF.Ave
