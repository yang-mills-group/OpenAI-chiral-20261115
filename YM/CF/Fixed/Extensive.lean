import YM.CF.Graph.Core

/-!
Sharper volume audit, including OFF-LACE charge.
This new estimate applies all the way to and through the fixed-x cutoff and
volume horizons. Follow d8's definitions: no change to which couplings,
stamps, positivity, etc. replaced. Use an **extensive** bound as opposed to
`flagT ~ vol^3`, at same arguments. `Extensive.chargeE` is O(vol), needed for
the larger period window. It uses the actual CardK row budget AND the CAR
norm while contracting the projected kets & bras **at fixed colors**, paying
for total size only rather than replacing with the bound from every entry. No
change to any integrands which might affect the state.

Some markup `unitV` Constants depend on the Teller. Off-Lace this keeps the
`pastWeight` in the estimate, which can be important; then one may weaken.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Fixed.Extensive
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial Nacre Font Laic Graph Skye
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
variable {ν:Type*}[Fintype ν][LinearOrder ν]
-- a basis choice is fixed in the total cardinal estimates. Don't commute Jazz with l1 sum.
def absEntries(X:Op ν):ℝ:=∑ i, ∑ j, ‖X i j‖
omit [LinearOrder ν] in
lemma entries_star(X:Op ν):absEntries (star X)=absEntries X:=by
  unfold absEntries; rw [sum_comm]; simp [Matrix.star_apply]
lemma dgN(C P Q:Op ν) (p:‖P‖≤1)(q:‖Q‖≤1): ‖dg (P*C*Q)‖ ≤ absEntries C := by
  let c:=basisKet (n:=ν)
  have ht(A:Op ν)(p:‖A‖≤1)(i): ‖acts A (c i)‖≤1:=(ContinuousLinearMap.le_opNorm ..).trans (by unfold acts; rw [Matrix.l2_opNorm_toEuclideanCLM,show ‖c i‖=(1:ℝ) by simp [c,basisKet],mul_one]; exact p)
  have he:= dyad_prong C P (cc (star Q)) put takeF; simp_rw [ccT,star_star] at he; change ‖dyad _ _ _‖ ≤_; rw [← he]; unfold absEntries dyad
  apply (norm_sum_le ..).trans; apply sum_le_sum; intro i hi; apply (norm_sum_le ..).trans; apply sum_le_sum; intro j hj; rw [norm_smul,prong_p,prong_t]
  apply mul_le_of_le_one_right (norm_nonneg _)
  have hp: ‖create (acts P (c i))‖≤1:= (Flare.cost_pe false (acts P (c i))).trans (ht P p i)
  have hq: ‖remove (acts (star Q) (c j))‖≤1:= (Flare.cost_pe true _).trans (ht (star Q) (by rwa [norm_star]) j)
  exact (norm_mul_le ..).trans ((mul_le_mul hp hq (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
lemma dgTwist (U:UNI ν)(C P Q:Op ν)(p:‖P‖≤1)(q:‖Q‖≤1): ‖dg (P*(twist U C)*Q)‖ ≤ absEntries C := by
  rw [twist_formula]; simp only [←mul_assoc]; rw [mul_assoc _ (star _) Q]; apply dgN
  · exact (CStarRing.norm_mul_coe_unitary _ U).trans_le p
  exact (CStarRing.norm_coe_unitary_mul (star U) _).trans_le q
lemma dgJazz (U:UNI ν)(b:Bool)(C P Q:Op ν)(p:‖P‖≤1)(q:‖Q‖≤1): ‖dg (P*Thera.jazz b (twist U C)*Q)‖ ≤ absEntries C := by
  unfold Thera.jazz; split; swap; · exact dgTwist U C P Q p q
  rw [mul_neg,neg_mul,←map_star (twist U),dg_neg,norm_neg]
  exact le_trans (dgTwist U (star C) P Q p q) (entries_star C).le

-- Card bound is already over all Jones color columns. Maintain it before
-- the norm computations, and pay at worst 45 for matrix entries through the
-- holonomy. Port Gauge rows; holds for any reflection and charge.
variable {N:Side}{m:ℕ}{C v a:ℝ}
lemma cavilRow (T:Toy m N)(p:CardK N m T C a)(A:Pane N)(t: HelpP A v a)(e:0≤a)(w:0≤v)(s:Signed)(i:Single N) :
    ∑ j:Single N, ‖cavil T (Yg (Nacre.incX s) A) i j‖ ≤ 45*(v^m*C):=by
  let V:=Yg (Nacre.incX s) A; let f(k: Trip m N) (x: Fin m):= silt (terse i.1) (k x) V
  have ht(k j):∏ x:Fin m,‖f k x‖ ≤ v^m*nick a (notx m i j k):=by
    let W(x):=t.fee s (place_x i) (k (x: Fin m)); refine (prod_le_prod (fun x _=>norm_nonneg (f k x)) (fun x _=>W x)).trans ?_
    rw [prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,←Real.exp_sum,←mul_sum]; refine mul_le_mul_of_nonneg_left (le_trans (b:=Real.exp (a*notx m i j k)) ?_ ?_) (pow_nonneg w _)
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (show 0≤gear _ _ by unfold gear; positivity)) e)
    exact le_mul_of_one_le_left (Real.exp_pos _).le (le_add_of_nonneg_right (notx_zero ..))
  let F(k:Trip m N)(j:Single N):=nick a (notx m i j k)*‖T i j k‖
  let G(q:HopK N)(z:Slot)(k:Trip m N):=F k (q,z)
  have hp(k: Trip m N)(j:Single N): ‖mold T i.1 j.1 k V i.2 j.2‖ ≤ ∑ q:Slot, (v^m* F k (j.1,q)) := by -- tune j binder
    unfold mold; rw [Matrix.mul_apply]; apply (norm_sum_le ..).trans; apply sum_le_sum; intro q _; rw [norm_mul]; have hx: ‖walkB i.1 j.1 V q j.2‖ ≤ 1:= (norm_entry (walkB _ _ V) _ _).trans (le_of_eq (CStarRing.norm_of_mem_unitary (matter _).property)); apply (mul_le_of_le_one_right (norm_nonneg _) hx).trans; change ‖T i _ k (f k)‖ ≤ v^m * F k _; refine ((T i (j.1,q) k).le_opNorm (f k)).trans ((mul_le_mul_of_nonneg_left (ht k (j.1,q)) (norm_nonneg _)).trans_eq ?_); unfold F; ring
  have he (x): ‖cavil T V i x‖ ≤ v^m*(∑ q:Slot,∑ k,G x.1 q k):=by
    unfold cavil; rw [Matrix.of_apply,Matrix.sum_apply]; apply (norm_sum_le ..).trans; rw [mul_sum]; simp_rw [mul_sum]; rw [sum_comm (f:=fun q k=> v^m*G _ q k)]; exact sum_le_sum fun k _=> hp k x
  let V'(k : HopK N):=v^m*(∑ q:Slot,∑ i,G k q i)
  apply (sum_le_sum (g:=fun q:Single N=>V' q.1) (fun q _=>he q)).trans
  have ht: balance a T i= ∑ q:HopK N,∑ k:Slot,∑ i,G q k i :=by rw [balance,Fintype.sum_prod_type]
  rw [Fintype.sum_prod_type]; simp only [sum_const,card_univ,SU.slots,nsmul_eq_mul,Nat.cast_ofNat]
  rw [←mul_sum]; apply mul_le_mul_of_nonneg_left _ (by positivity); unfold V'; rw [←mul_sum,←ht]; exact mul_le_mul_of_nonneg_left (p.2.2 i) (pow_nonneg w _)

lemma extensive_dgT (T:Toy m N)(p:CardK N m T C a)(A:Pane N)(t: HelpP A v a)(e:0≤a)(w:0≤v)
    (P:Op (Single N))(Hp:IsStarProjection P): ‖dg (Kennel.capT P (colorX T A))‖ ≤ lark N *(45*(v^m*C)):=by
  let Q:=1-P; let K : Op (Single N) →ₗ[ℝ] FC (Single N):=
    { toFun F:=dg (Q*F*P)
      map_add' i j:=by rw [mul_add,add_mul,dg_add]
      map_smul' c F:=by rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,dg_scale]; rfl }
  let D(s):= Nacre.foil s (cavil T) A
  change ‖K (_ • ∑ s:Signed,D s)‖ ≤ _
  rw [map_smul,map_sum]; apply sealV; intro s; let L:= cavil T (Yg (incX s⁻¹) A)
  change ‖dg (Q* Nacre.foil s (cavil T) A*P)‖ ≤ lark N *_; rw [Nacre.foil,Nacre.zone_c]; refine (dgJazz _ _ L Q P (Hp.one_sub.norm_le _) (Hp.norm_le _)).trans ?_
  refine (sum_le_sum (g:=fun i=>45*(v^m*C)) (fun i _=> cavilRow T p A t e w s⁻¹ i)).trans_eq ?_; simp only [sum_const,card_univ,nsmul_eq_mul,Pic.units_t]
variable {v η t vA r u h:ℝ}{R: GramM N}{X:Loom N}
lemma extensive_dg (W:Ledger h u η r C R)(t:Orbit N)(g:HelpP (X t) vA r)(e:0≤vA)(a:0≤r){j:ℕ}(p:IsStarProjection (spar j R.J.M (X t))): ‖dg (actF j R X t)‖ ≤ doorF N vA C:=by
  unfold actF Aim.den; rw [Pi.add_apply]; obtain ⟨A,B⟩:= W.field.1
  rw [show ∀ (x y z:Op (Single N)),Kennel.capT x (y+z)=Kennel.capT x y+Kennel.capT x z from fun _ _ _=>by unfold Kennel.capT; rw [mul_add,add_mul],dg_add]; refine (norm_add_le ..).trans ((add_le_add (extensive_dgT _ A _ g a e _ p) (extensive_dgT _ B _ g a e _ p)).trans_eq ?_); unfold doorF; ring

def chargeE(n:Side)(v η C:ℝ):= pittance n 2 C+ (((v+v+η)*(More n).val^4)+doorF n 2 C)
lemma flag_charge(W:Ledger h u η r C R)(t:Orbit N)(a:0≤r)(hP:1≤h){j:ℕ}(p:IsStarProjection (spar j R.J.M (X t))): ‖mile j R X t‖ ≤Real.exp (chargeE N u η C):=by
  have hp:= rear R W.reg W.slip W.force hP t _ p; let F:= actF j R X t; let E:=pittance N 2 C; let Q:=Pec.pigment R.J.I (X t); have he:‖-Q‖≤E:= by rw [norm_neg]; exact aurP _ _ W.field.2 (railT (X t) r a) (by positivity)
  have ht:‖dg F‖ ≤ doorF N 2 C:=extensive_dg W t (railT _ _ a) (by positivity) a p
  have hu:= (bootC _).trans (Real.exp_le_exp.mpr ht); rw [chargeE,Real.exp_add,Real.exp_add (x:=(u+u+η)*_),mile,norm_smul]; exact mul_le_mul ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr he)) ((norm_mul_le ..).trans (mul_le_mul hp hu (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le

end YM.CF.Fixed.Extensive
