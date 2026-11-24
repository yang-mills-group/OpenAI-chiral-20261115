import ForceSatin.Truncate
import ForceSatin.CommutingPrice

/-! Length/degree budgets at the Tilt filter. Give a local walk of CAR queries, then
     buy its tilted reading once, in *any* gauge argument on which the hypotheses hold.
     No vacuum identification across torus sizes. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.Papyrus.Franc.SatinForce
open Function Filter NormedSpace Fock Finset Matrix Thera Verses
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
variable {I : Type}[LinearOrder I][Fintype I][Nonempty I]
variable {P : Op I}{A K : Shaft I} {J : Type*}{B C D W : ℝ} {m:ℕ}

def highLeg (A : Shaft I) (i : Bool × I) : Ket I :=
  acts (if i.1 then star A.buy else A.sell) (basisKet i.2)

omit [Nonempty I] in
theorem highLeg_norm (A : Shaft I)(p:fiber A B)(i): ‖highLeg A i‖≤B:=by unfold highLeg; split; exact p.snd _; exact p.fst _

def monomial (L:List (Bool×I)) : FC I := rollC (fun i=> creed i.1 (basisKet i.2)) L

omit [Nonempty I] in
theorem monomial_shaped (T:Shaft I)(L:List (Bool×I)) : T.glow (monomial L)=rollC (fun i=>creed i.1 (highLeg T i)) L := by
  induction L with
  | nil=> simp [monomial,rollC,T.glow_nil]
  | cons i L ih=> change T.glow (_* monomial L)=_ * rollC _ L; rw [T.glow_mult,ih]; congr 1; unfold highLeg creed; dsimp only; split_ifs; exact T.glow_down _; exact T.glow_up _

def wordFee (c : Bool×I)(A:Shaft I)(P:Op I)(x:Wave I) : ℝ :=
  ‖acts (create (acts P (highLeg A c))) x‖^2 +
  ‖acts (Fock.remove (acts (1-P) (highLeg A c))) x‖^2

def food (S: Finset I)(A:Shaft I)(P:Op I)(x:Wave I) : ℝ := Real.sqrt (∑ i∈ S,(wordFee (true,i) A P x + wordFee (false,i) A P x))

omit [Nonempty I] in
theorem budgeted_leg (S:Finset I)(c:Bool×I)(hc:c.2∈S)(A:Shaft I)(P:Op I)(x:Wave I):
    shield P x (highLeg A c) (food S A P x):=by
  let F(i:I):= (wordFee (true,i) A P x + wordFee (false,i) A P x)
  let f:=∑ i∈S,F i
  have h(i:Bool×I):0≤wordFee i A P x:=add_nonneg (sq_nonneg _) (sq_nonneg _)
  have he:F c.2≤f:= single_le_sum (fun i _=>add_nonneg (h (true,i)) (h (false,i))) hc
  have hw: wordFee c A P x ≤ F c.2 := by
    obtain ⟨i,j⟩:=c; cases i; exact le_add_of_nonneg_left (h _); exact le_add_of_nonneg_right (h _)
  exact ⟨Real.le_sqrt_of_sq_le (le_trans (le_add_of_nonneg_right (sq_nonneg _)) (hw.trans he)),
         Real.le_sqrt_of_sq_le (le_trans (le_add_of_nonneg_left (sq_nonneg _)) (hw.trans he))⟩

lemma food_product (K:Shaft I)(P:Op I)(p:IsStarProjection P)(x:Wave I)(W:ℝ)(h:‖K.sell‖≤W)(t:‖K.buy‖≤W) (L:Finset J) (S:J→ Finset I) (a: Set.PairwiseDisjoint (L:Set J) S) :
    (∑ j∈L, food (S j) K P x)^2 ≤ L.card * (4*W^2 * active P x) := by
  classical
  let F(i:I):= (wordFee (true,i) K P x+wordFee (false,i) K P x)
  have hx(i):0≤F i := add_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (add_nonneg (sq_nonneg _) (sq_nonneg _))
  let v:=W^2 * active P x
  have hv(i:Bool)(X:Op I)(t:∀ j:I,highLeg K (i,j)=acts X (basisKet j))(h:‖X‖≤W): ∑ j:I,wordFee (i,j) K P x ≤ v+v :=by
    unfold wordFee; simp_rw [t]; rw [sum_add_distrib]; exact add_le_add (bessel_hole p h x) (bessel_particle p h x)
  have hs:∑ j∈L, food (S j) K P x ^2 ≤ 4*W^2*active P x:=by
    let u:= L.biUnion S
    have he(j):food (S j) K P x ^2= ∑ i∈S j,F i:=Real.sq_sqrt (sum_nonneg fun i _=> hx i)
    simp_rw [he]; rw [←sum_biUnion a]; apply le_trans (b:=∑ i:I,F i) (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=> hx i)); unfold F; rw [sum_add_distrib]
    exact (add_le_add (hv true (star K.buy) (fun _=>rfl) ((norm_star _).le.trans t)) (hv false K.sell (fun _=>rfl) h)).trans_eq (by unfold v; ring)
  have he(j:J)(_:j∈L) : 0≤food (S j) K P x := Real.sqrt_nonneg _
  apply le_trans _ (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _))
  simpa using (sum_mul_sq_le_sq_mul_sq L (fun _=> (1:ℝ)) (fun j=>food (S j) K P x))

theorem monomial_budget (A:Shaft I)(L:List (Bool×I))(h:L.length ≤ m)(p:fiber A B)(u:1≤B) : ‖A.glow (monomial L)‖ ≤ B^m := by
 rw [monomial_shaped]
 exact (Loaves.normC _ _ (zero_lt_one.trans_le u) _ (fun i _=> (Flare.cost_pe ..).trans (highLeg_norm A p i))).trans (pow_le_pow_right₀ u h)

lemma feed_one (q x:Wave I)(S:Finset I)(L:List (Bool×I))(v:∀ i∈L,i.2∈ S)(h:L.length  ≤ m)
    (hp:IsStarProjection P) (hb: Sea P q)(p:fiber A B)(u:1 ≤ B)(e:fiber K B)
    (s0:0≤D)(d:∀ i, ‖highLeg A i-highLeg K i‖≤D) :
    ‖resid q x (A.glow (monomial L))‖ ≤ normalCost B m * food S K P x *‖x‖ + (2*m*D*B^m)*‖x‖^2:=by
  rw [monomial_shaped]; let W (A:Shaft I):=rollC (fun i:Bool × I=>creed i.1 (highLeg A i)) L
  let X:=resid q x; let v':=food S K P x
  change ‖X (W A)‖≤ normalCost B m*v'*_ + _
  have hh(X:Shaft I)(p:fiber X B)(i:Bool×I): ‖creed i.1 (highLeg X i)‖≤ B:= (Flare.cost_pe ..).trans (highLeg_norm X p _)
  have hk:‖X (W K)‖ ≤ normalCost B m*v'*‖x‖:= length_price (q:=q) (highLeg K) Prod.fst P hp hb u (show 0≤v' from Real.sqrt_nonneg _) m L h (fun i y=>⟨highLeg_norm K e _,budgeted_leg S i (v _ y) K P x⟩)
  have he: ‖W A-W K‖  ≤ m*D*B^m:=by
    have hm := Loaves.normsDiff (fun i:Bool×I=>creed i.1 (highLeg A i)) (fun i:Bool×I=>creed i.1 (highLeg K i)) B u D s0 L (fun i _=>hh A p i) (fun i _=>hh K e i) (fun i _=>(Loaves.scone i.1 _ _).trans (d i))
    apply hm.trans; gcongr
  have hg:= resid_price q x hb.2 (W A-W K)
  rw [show W A=W K+(W A-W K) from (add_sub_cancel ..).symm,map_add]
  apply (norm_add_le ..).trans; apply add_le_add hk; apply hg.trans; nlinarith only [mul_le_mul_of_nonneg_right he (sq_nonneg ‖x‖)]

/- Polynomial of raw letters with explicit membership. Later realized at
   the legal Mark signatures. Using inductive definition makes it easy to assemble
   sum of polynomials and products (don't interpolate on a different vacuum). -/
inductive Credential (S:Finset I) (m:ℕ) : ℝ → FC I→ Prop
| coeff (u:ℂ)(L:List (Bool×I))(h:L.length ≤ m)(v:∀ i∈L,i.2∈S) : Credential S m ‖u‖ (u • monomial L)
| add {a b:ℝ} {X Y:FC I} : Credential S m a X → Credential S m b Y → Credential S m (a+b) (X+Y)
| enlarge {a b X} : a ≤ b → Credential S m a X → Credential S m b X

namespace Credential
variable {S:Finset I}{X Y:FC I}{a b d:ℝ}

omit [Nonempty I] in
theorem nonneg (p:Credential S m a X) : 0≤a:=by induction p with|coeff => exact norm_nonneg _|add p q h g=> exact add_nonneg h g|enlarge h _ ih=> exact ih.trans h
lemma glow (p:Credential S m a X) (h:fiber A B)(u:1≤B) : ‖A.glow X‖ ≤ a*B^m:=by
  have v:0≤B^m:=by have e:=zero_lt_one.trans_le u; positivity
  induction p with
  | coeff c L t _=> rw [A.glow_free,norm_smul]; exact mul_le_mul_of_nonneg_left (monomial_budget A L t h u) (norm_nonneg _)
  | add _ _ g h=> rw [A.glow_sum, add_mul]; exact (norm_add_le ..).trans (add_le_add g h)
  | enlarge l _ ih=> exact ih.trans (mul_le_mul_of_nonneg_right l v)

def feedBill (m:ℕ)(B d ε:ℝ)(x:Wave I) := normalCost B m * ε*‖x‖+(2*m*d*B^m)*‖x‖^2
omit [Nonempty I] [LinearOrder I] in
lemma feedBill_nonneg (h:1≤B)(u:0≤ d)(e:0≤a)(x:Wave I) (m : ℕ):0≤feedBill m B d a x:=by
  apply add_nonneg; exact mul_nonneg (mul_nonneg (normal_non h m) e) (norm_nonneg _); have hb:=zero_lt_one.trans_le h; positivity
lemma feed (q x:Wave I)(p:Credential S m a X)(h:IsStarProjection P)(v:Sea P q)
    (u:fiber A B)(k:fiber K B)(g:1≤B)(p':0≤d)(s:∀ i, ‖highLeg A i-highLeg K i‖≤d) :
    ‖resid q x (A.glow X)‖ ≤ a* feedBill m B d (food S K P x) x:=by
  induction p with
  | coeff c L ht V=> rw [A.glow_free,map_smul,norm_smul]; exact mul_le_mul_of_nonneg_left (feed_one q x S L V ht h v u g k p' s) (norm_nonneg _)
  | add _ _ ih ig=> rw [A.glow_sum,map_add,add_mul]; exact (norm_add_le ..).trans (add_le_add ih ig)
  | enlarge H _ ih=> exact ih.trans (mul_le_mul_of_nonneg_right H (feedBill_nonneg g p' (Real.sqrt_nonneg _) x _))
end Credential

section
open Lattice Laurent Bloch Lat Cube Rush SU Fir Nacre Ember Scroll Tulip Tenant BPress.Spin.Blank Dial Cascade
-- summarize high-mode use
variable {N:Side}
lemma commuted_neumann (j:ℕ)(h:1≤j) :
  ∃ c:ℝ,0<c∧∀ (N:Side)(M:Tulip.Male)(k:ℕ),0<k→let Q:=FlatPaneP j M N; ∀ p:IsStarProjection Q,
  ∀ (t:ℝ), |t|≤1 →
    let S:= (tilt Q t); let A:= S.foldC (exactShear j M N h p); let K:= S.foldC (Saber (B:=tickA N) p k)
    (‖K.sell‖ ≤ tiltCost*(1+k) ∧ ‖K.buy‖ ≤ tiltCost*(1+k)) ∧
    ∀ i:Bool×Single N, ‖highLeg A i-highLeg K i‖ ≤ tiltCost*Real.sqrt (c*(Real.sqrt (k:ℝ))⁻¹):=by
  obtain ⟨c,hc,v⟩:= neumann_truncation j h; refine ⟨c,hc,?_⟩
  intro N M k hk Q p t b S A K
  let U:=exactShear j M N h p;let V:= Saber (B:=tickA N) p k; let z:= tiltCost; have hz:0≤z:= (Real.exp_pos _).le
  have ha:‖S.sell‖≤z:= tilt_norm p b
  have hb:‖S.buy‖≤z:= tilt_norm (t:= -t) p (by rwa [abs_neg])
  let W:= c*(Real.sqrt (k:ℝ))⁻¹
  have he:=saber_op p (plus_P N) k
  refine ⟨⟨(norm_mul_le ..).trans (mul_le_mul ha he.1 (norm_nonneg _) hz), (norm_mul_le ..).trans ((mul_le_mul_of_nonneg_left hb (norm_nonneg _)).trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left he.2 hz))⟩,?_⟩
  rintro ⟨a,i⟩; let X:=flatComb j M N h p; let Y:= Comb (tickA N) Q k
  let I:=basisKet i; obtain ⟨s,l⟩:= v k hk N M p i
  cases a
  · change ‖acts (S.sell*U.sell) I-acts (S.sell*V.sell) I‖ ≤ z*Real.sqrt W; rw [←act_sub, ←mul_sub, act_mul,show U.sell-V.sell=star (X-Y) from by change 1+star X-(1+star Y)=_; rw [star_sub]; abel]
    exact (Flare.opy ..).trans (mul_le_mul ha (Real.le_sqrt_of_sq_le l) (norm_nonneg _) hz)
  change ‖acts (star (U.buy*S.buy)) I - acts (star (V.buy*S.buy)) I‖ ≤ z*Real.sqrt W
  rw [star_mul, star_mul, ←act_sub, ←mul_sub, act_mul, show star U.buy-star V.buy= -(X-Y) from ?_, act_neg]
  · apply (Flare.opy ..).trans; rw [norm_neg, norm_star]; exact mul_le_mul hb (Real.le_sqrt_of_sq_le s) (norm_nonneg _) hz
  unfold U V exactShear Saber X Y Q; simp only [star_sub, star_star, star_one]; abel

end
end YM.CF.Papyrus.Franc.SatinForce
