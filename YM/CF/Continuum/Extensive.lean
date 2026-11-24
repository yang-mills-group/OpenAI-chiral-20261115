import YM.CF.Graph.Slay
import YM.CF.Continuum.Salary

/-!
# Absolute price at the active stopping lattice

Sharpen `Graph.stout`/`Graph.cents`. The price after `rec` (scalar `v`
removed) is exponentially bounded *per-site*, on ALL volumes of admissible
`Pull_P`s, even on the complement of the no-flags event. Record both the
absolute and the precise relative bills used in the local expectations. Uses
the very same budgets and positive constants; no change of representation or
truncating the amplitude. Some proofs below rework `Graph/*.lean` proofs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic Graph
open Nacre Font Pec
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 4096
variable {n:Side}{v h b a:ℝ}{p:BudgetPoint}

variable {m : ℕ} {C : ℝ}

private def toyBill (U : Toy m n) (a : ℝ) (x y : Single n) :=
  ∑ i, nick a (notx m x y i) * ‖U x y i‖

-- column endpoint of the walk multiplies a color matrix. Do NOT use the
-- old `Ctil` (worst-case entry) estimate inside another sum over the volume.
lemma toy_entry (U:Pane n)(T:Toy m n)(t: HelpP U v a)(e:0≤a)(w:0≤v)(s:Signed)(i j:Single n): let V:=Yg (incX s) U; ‖cavil T V i j‖ ≤ v^m * ∑ c:SU.Slot,toyBill T a i (j.1,c):=by
 intro V; let f(k:Trip m n):=fun x: Fin m=> silt (terse i.1) (k x) V; let z(q:SU.Slot): Single n:=(j.1,q)
 have ht(k q):∏ x: Fin m,‖f k x‖ ≤ v^m * nick a (notx m i (z q) k):=by
    let W(x):= t.fee s (place_x i) (k (x: Fin m)); refine (prod_le_prod (fun x _=> norm_nonneg (f k x)) (fun x _=>W x)).trans ?_; rw [prod_mul_distrib, prod_const,card_univ,Fintype.card_fin,← Real.exp_sum, ←mul_sum]; refine mul_le_mul_of_nonneg_left (le_trans (b:=Real.exp (a*notx m i (z q) k)) ?_ ?_) (pow_nonneg w _)
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (show 0≤gear _ _ by unfold gear; positivity)) e)
    exact le_mul_of_one_le_left (Real.exp_pos _).le (le_add_of_nonneg_right (notx_zero ..))

 unfold cavil; rw [Matrix.of_apply,Matrix.sum_apply]; apply (norm_sum_le ..).trans
 let F(k:Trip m n)(q:SU.Slot):=‖T i (z q) k‖*(v^m *nick a (notx m i (z q) k)); have he(k:Trip m n): ‖mold T i.1 j.1 k V i.2 j.2‖ ≤ ∑ q: SU.Slot,F k q:=by
    unfold mold; rw [Matrix.mul_apply]; refine (norm_sum_le ..).trans (sum_le_sum fun q _=> ?_); rw [norm_mul]; have hx: ‖walkB i.1 j.1 V q j.2‖ ≤ 1:= (norm_entry (walkB _ _ V) _ _).trans (le_of_eq (CStarRing.norm_of_mem_unitary (matter _).property)); apply (mul_le_of_le_one_right (norm_nonneg _) hx).trans; change ‖T i (z q) k (f k)‖ ≤ F k q; exact ((T i (z q) k).le_opNorm _).trans (mul_le_mul_of_nonneg_left (ht k q) (norm_nonneg _))

 apply (sum_le_sum (g:=fun i=>∑ q,F i q) fun i _=>he i).trans; rw [sum_comm,mul_sum]
 refine le_of_eq (sum_congr rfl fun c _=>?_)
 unfold toyBill; rw [mul_sum]; refine sum_congr rfl fun b _=>?_ ; unfold F z; ring

lemma absolute_rows (U : Pane n) (T : Toy m n) (p : CardK n m T C a)
    (t : HelpP U v a) (e : 0≤a) (w : 0≤v) (s : Signed) (i : Single n) :
    ∑ j, ‖cavil T (Yg (incX s) U) i j‖ ≤ 45 * v^m * C := by
  let A:= cavil T (Yg (incX s) U); let F(j : Single n):=toyBill T a i j
  calc
    _ ≤ ∑ j:Single n, v^m * ∑ c:SU.Slot, F (j.1,c) := Finset.sum_le_sum (s:=univ) (f:=fun j=> ‖A i j‖) (fun j _=> toy_entry U T t e w s i j)
    _ = 45*v^m * (∑ j:Single n, F j) := by
      rw [←mul_sum]; unfold Single; simp_rw [Fintype.sum_prod_type]; simp only [Finset.sum_const,card_univ,nsmul_eq_mul,Fintype.card_fin, show Fintype.card SU.Sheet=15 from by decide,Nat.cast_ofNat]; simp_rw [←mul_sum]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (p.2.2 i) (by positivity)

lemma absolute_toy (U : Pane n) (T : Toy m n) (p : CardK n m T C a)
    (t : HelpP U v a) (e : 0≤a) (w : 0≤v) (s : Signed) :
    entryBudget (cavil T (Yg (incX s) U)) ≤ (Fintype.card (Single n):ℝ)*45*v^m*C := by
  refine (sum_le_sum (fun i _=> absolute_rows U T p t e w s i)).trans_eq ?_
  rw [sum_const, card_univ, nsmul_eq_mul]; ring

private lemma foilBound (U : Pane n) (T : Toy m n) (p : CardK n m T C a)
    (t : HelpP U v a) (e : 0≤a) (w : 0≤v) (s : Signed) (A B : Op (Single n))
    (h : ‖A‖ ≤ 1) (g : ‖B‖ ≤ 1) :
    ‖dg (A*(foil s (cavil T) U)*B)‖ ≤ (Fintype.card (Single n):ℝ)*45*v^m*C := by
  apply le_trans _ (absolute_toy U T p t e w s⁻¹)
  unfold foil; rw [zone_c]; let F:=cavil T (Yg (incX s⁻¹) U)
  let V:=prepU (incX s) (spinX s) inert n
  change ‖dg (A*Thera.jazz (detX s) (twist V F)*B)‖ ≤ entryBudget F
  unfold Thera.jazz; split; · rw [mul_neg,neg_mul,dg_neg,norm_neg,←map_star]; exact (rotatedBound _ _ _ _ h g).trans_eq (entryBudget_adjoint _)
  exact rotatedBound _ _ _ _ h g

lemma thermalCap (P : GramM n) (W : Loom n) (Z : Graph.Ledger h v b a C P)
    (t : Orbit n) (e : 0≤a) (k : ℕ) (p : IsStarProjection (spar k P.J.M (W t))) {d : ℝ}
    (hd : 0≤d) (g : HelpP (W t) d a) :
    ‖dg (actF k P W t)‖ ≤ doorF n d C := by
  let U:= spar k P.J.M (W t)
  have he {u : ℕ} (F : Toy u n) (h : CardK n u F C a) :
      ‖dg ((1-U)*colorX F (W t)*U)‖ ≤ (Fintype.card (Single n):ℝ)*45*d^u*C := by
    unfold colorX sumU
    rw [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Finset.mul_sum, Finset.sum_mul,dg_scale,generator_sum]
    exact Graph.sealV _ fun s=> foilBound (W t) F h g e hd s _ _ (p.one_sub.norm_le _) (p.norm_le _)
  obtain ⟨A,B⟩:= Z.field.1; unfold actF Kennel.capT Aim.den
  rw [Pi.add_apply,mul_add,add_mul,dg_add]; refine (norm_add_le ..).trans ((add_le_add (he _ A) (he _ B)).trans_eq ?_)
  unfold doorF lark; rw [Pic.units_t]; ring

def flagBill (n : Side) (v η C : ℝ) :=
  pittance n 2 C + (((v+v+η)*(More n).val^4)+doorF n 2 C)

theorem extensive_mile {j : ℕ} {X : Loom n} {P : GramM n} (W : Graph.Ledger h v b a C P)
    (t : Orbit n) (e : 0≤a) (g : 1 ≤ h) (_hc : 0 ≤ C) (p : IsStarProjection (spar j P.J.M (X t))) :
    ‖mile j P X t‖ ≤ Real.exp (flagBill n v b C) := by
  have hp := rear P W.reg W.slip W.force g t _ p
  let Q:=Pec.pigment P.J.I (X t); have he : ‖-Q‖≤pittance n 2 C := by rw [norm_neg]; exact aurP _ _ W.field.2 (railT _ _ e) (by positivity)
  have ht := thermalCap _ X W t e j p (by norm_num : (0:ℝ)≤2) (railT _ _ e)
  have hu := (bootC _).trans (Real.exp_le_exp.mpr ht); rw [flagBill,Real.exp_add,Real.exp_add (x:=(v+v+b)*_),mile,norm_smul]
  exact mul_le_mul ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr he)) ((norm_mul_le ..).trans (mul_le_mul hp hu (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le
end YM.CF.Window
