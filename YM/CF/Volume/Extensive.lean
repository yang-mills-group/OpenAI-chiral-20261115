import YM.CF.Ups.Gul
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Nacre Font Pec
variable {n:Side}{v h b a z:ℝ}{p:BudgetPoint}
variable {m:ℕ}{C:ℝ}
set_option maxHeartbeats 1000000

/- Extensivity of dg exponent: row budget aggregation on cavil
   doesn't spend the number of columns on each row. -/
lemma cavilRowExt (U:Pane n)(T:Toy m n)(p:CardK n m T C a)(t: HelpP U v a)(e:0≤a)(w:0≤v)(s:Signed)(i:Single n): let V:=Yg (incX s) U; ∑ j: Single n, ‖cavil T V i j‖ ≤ Fintype.card SU.Slot * (v^m *C):=by
 intro V
 -- reuse the stencil price from Graph/Zing. Keep weights with the corresponding output index.
 let f(k:Trip m n):=fun x: Fin m=> silt (terse i.1) (k x) V
 let F(j:Single n)(k:Trip m n):=nick a (notx m i j k) * ‖T i j k‖
 have ht(k:Trip m n)(j):∏ x: Fin m,‖f k x‖ ≤ v^m * nick a (notx m i j k):=by
    let W(x):= t.fee s (place_x i) (k (x: Fin m)); refine (prod_le_prod (fun x _=> norm_nonneg (f k x)) (fun x _=>W x)).trans ?_; rw [prod_mul_distrib, prod_const,card_univ,Fintype.card_fin,← Real.exp_sum, ←mul_sum]; refine mul_le_mul_of_nonneg_left (le_trans (b:=Real.exp (a*notx m i j k)) ?_ ?_) (pow_nonneg w _)
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (show 0≤gear _ _ by unfold gear; positivity)) e)
    exact le_mul_of_one_le_left (Real.exp_pos _).le (le_add_of_nonneg_right (notx_zero ..))
 have hx(j: Single n): ‖cavil T V i j‖ ≤ ∑ q: SU.Slot, ∑ k:Trip m n, v^m * F (j.1,q) k:=by
    unfold cavil
    rw [Matrix.of_apply,Matrix.sum_apply,sum_comm]
    refine (norm_sum_le ..).trans (sum_le_sum fun k _=> ?_)
    unfold mold
    rw [Matrix.mul_apply]
    refine (norm_sum_le ..).trans (sum_le_sum fun q _=> ?_)
    rw [norm_mul]
    have hq: ‖walkB i.1 j.1 V q j.2‖ ≤ 1:= (norm_entry (walkB _ _ V) _ _).trans (le_of_eq (CStarRing.norm_of_mem_unitary (matter _).property))
    apply (mul_le_of_le_one_right (norm_nonneg _) hq).trans
    change ‖T i (j.1,q) k (f k)‖ ≤ v^m * F (j.1,q) k
    apply le_trans (((T i (j.1,q) k).le_opNorm _).trans (mul_le_mul_of_nonneg_left (ht _ _) (norm_nonneg _)))
    unfold F; apply le_of_eq; ring
 have hsum : ∑ (i:Single n), ∑ k, F i k ≤ C:=p.2.2 i
 apply le_trans (sum_le_sum (s:=univ) fun j _=>hx j)
 change ∑ j:HopK n × SU.Slot, ∑ q: SU.Slot, ∑ k:Trip m n, v^m * F (j.1,q) k ≤ _
 rw [Fintype.sum_prod_type, sum_comm]
 apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (pow_nonneg w _)) (show 0 ≤ (Fintype.card SU.Slot :ℝ) by positivity)).trans'
 have he: ∑ j:Single n,∑ k:Trip m n,F j k=∑ j:HopK n, ∑ q:SU.Slot,∑ k:Trip m n,F (j,q) k:= Fintype.sum_prod_type _
 change ∑ _: SU.Slot,∑ x:HopK n, ∑ q:SU.Slot,∑ k:Trip m n,v^m * F (x,q) k ≤ _
 rw [he,sum_const,card_univ,nsmul_eq_mul]; simp_rw [←mul_sum]; apply le_rfl

open Cascade
section compress
variable {X:Type*}[LinearOrder X][Fintype X]
/- contraction on each side then dg. -/
lemma dgPriceExt [Nonempty X] (P A B:Op X)(pa: ‖A‖≤1)(bp: ‖B‖≤1): ‖dg (A*P*star B)‖ ≤ ∑ i,∑ j,‖P i j‖:=by
 have hx: dg (A*P*star B)=dyad P (prong put A) (prong takeF (cc B)):=by rw [dyad_prong, ccT]; rfl
 have hp(W:Op X)(hw:‖W‖≤1)(b:Bool)(i:X): ‖creed b (acts W (basisKet i))‖≤ 1 :=by
    apply (Flare.cost_pe ..).trans; exact (Flare.opy ..).trans (by rw [show ‖basisKet i‖=1 by simp,mul_one]; exact hw)
 rw [hx,dyad]
 apply (norm_sum_le ..).trans; apply sum_le_sum; intro i _; apply (norm_sum_le ..).trans; apply sum_le_sum; intro j _
 rw [norm_smul]
 apply mul_le_of_le_one_right (norm_nonneg _)
 rw [prong_t,prong_p]
 exact (norm_mul_le ..).trans ((mul_le_mul (hp A pa false i) (hp B bp true j) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
lemma dgTwistExt [Nonempty X] (P A B:Op X)(pa: ‖A‖≤1)(bp: ‖B‖≤1)(U:UNI X)(u:Bool): ‖dg (A* Thera.jazz u (twist U P) *star B)‖ ≤ ∑ i,∑ j,‖P i j‖:=by
 let W(Q:Op X):= Q*U.val
 have hp(Q:Op X)(h:‖Q‖≤1): ‖W Q‖≤1:=by
    unfold W; exact (norm_mul_le ..).trans (by rw [wedge_on, mul_one]; exact h)
 have hv(Q R T:Op X): Q*twist U R*star T= W Q*R*star (W T):=by rw [twist_formula]; unfold W; simp only [star_mul,mul_assoc]
 unfold Thera.jazz
 split
 · rw [mul_neg, neg_mul,dg_neg,norm_neg,← map_star,hv]
   apply (dgPriceExt _ _ _ (hp A pa) (hp B bp)).trans
   simp_rw [Matrix.star_apply,norm_star] -- inspect
   rw [sum_comm]
 · rw [hv]; exact dgPriceExt _ _ _ (hp A pa) (hp B bp)
end compress

lemma forgeExtensive (U:Pane n)(T:Toy m n)(p:CardK n m T C a)(t: HelpP U v a)(e:0≤a)(w:0≤v)(A:Op (Single n))(h:IsStarProjection A): ‖dg (Kennel.capT A (colorX T U))‖ ≤ Fintype.card (Single n)* (45*(v^m*C)):=by
 let Q: Op (Single n) →ₗ[ℝ] FC (Single n):=
   { toFun P:=dg (Kennel.capT A P)
     map_add' x y:=by rw [Kennel.capT,mul_add,add_mul,dg_add]; rfl
     map_smul' c x:=by change dg ((1-A)*(c•x)*A)= c • dg ((1-A)*x*A); rw [Matrix.mul_smul, Matrix.smul_mul, dg_scale] }
 change ‖Q ((↑(Fintype.card Signed):ℝ)⁻¹ • ∑ a:Signed, Nacre.foil a (cavil T) U)‖ ≤ _
 rw [map_smul, map_sum]
 apply sealV
 intro s
 have hp': star A = A:=h.isSelfAdjoint
 suffices ht: ‖Q (Nacre.foil s (cavil T) U)‖≤ ∑ i,∑ j,‖cavil T (Yg (incX s⁻¹) U) i j‖ by
    apply ht.trans
    have hs:=sum_le_sum (s:=univ) (fun i _=> cavilRowExt U T p t e w s⁻¹ i)
    rw [slots] at hs; simp only [sum_const,card_univ, nsmul_eq_mul, Nat.cast_ofNat] at hs; exact hs
 rw [Nacre.foil,zone_c,ape]
 change ‖dg ((1-A) * Thera.jazz _ (twist _ (cavil T (Yg (incX s⁻¹) U))) * A)‖ ≤ _
 nth_rw 2 [← hp']
 apply dgTwistExt _ (1-A) A (h.one_sub.norm_le _) (h.norm_le _)

lemma dgActExtensive {j:ℕ}{vA r η:ℝ}{R:GramM n}{X:Loom n}(W:Ledger h v η r C R)(t:Orbit n)(g:HelpP (X t) vA r)(he:0≤vA)(a:0≤r)(p:IsStarProjection (spar j R.J.M (X t))): ‖dg (actF j R X t)‖ ≤ doorF n vA C:=by
 unfold actF Aim.den; simp only [Pi.add_apply,Kennel.capT,mul_add,add_mul,dg_add]
 have hK:=W.field.1; obtain ⟨i,j'⟩:= hK; exact (norm_add_le ..).trans ((add_le_add (forgeExtensive _ _ i g a he _ p) (forgeExtensive _ _ j' g a he _ p)).trans_eq (by rw [Pic.units_t (N:=n)]; unfold doorF lark; ring))
/-- norm price linear in volume in the exponent -/
def exPrice (n:Side)(v η C:ℝ):= pittance n 2 C+ (((v+v+η)*(More n).val^4)+doorF n 2 C)
lemma stoutExtensive {j:ℕ}{r η:ℝ}{R:GramM n}{X:Loom n}(W:Ledger h v η r C R)(t:Orbit n)(a:0≤r)(hP:1≤h)(p:IsStarProjection (spar j R.J.M (X t))): ‖mile j R X t‖ ≤Real.exp (exPrice n v η C):=by
 have hp:= rear R W.reg W.slip W.force hP t _ p; let F:= actF j R X t; let E:=pittance n 2 C; let Q:=Pec.pigment R.J.I (X t); have he:‖-Q‖≤E:= by rw [norm_neg]; exact aurP _ _ W.field.2 (railT (X t) r a) (by positivity)
 have ht:=dgActExtensive W t (railT _ _ a) (by positivity) a p
 have hu:= (bootC _).trans (Real.exp_le_exp.mpr ht); rw [exPrice,Real.exp_add,Real.exp_add (x:=(v+v+η)*_),mile,norm_smul]; exact mul_le_mul ((Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr he)) ((norm_mul_le ..).trans (mul_le_mul hp hu (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
open MeasureTheory Cascade Vale CF.Paige Vault Nova
open Emu Flare
variable {m B L:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e u η r R C μ D L':ℝ}
lemma recPoint (V:GramM (mid m B))(S:Loom (mid m B))(H:Roof _ u e n S)(s:Grasp Y B e)(hp:s.roundZ ≤ (mid m B).val)(K':Ledger R v η r C V)(ht:0 ≤ r)(t:1 ≤ R)(y: Orbit (mid m B)): ‖recX s V S y‖≤ past V y.1 * Real.exp (exPrice (mid m B) v η C):=by
 have hh:= (s.broadness _ hp V.J.M).projection (S y) (H.paid y)
 let A:=cab V s S y; let w:= past V y.1; have he:0 ≤ w:= (Real.exp_pos _).le; have hp':‖A‖=1:= (sea_g hp (S y) (H.paid y) V.J.M).2; have hu:‖beam V s S y‖ ≤ Real.exp (exPrice (mid m B) v η C):=(spentS _ _ A).trans (by rw [hp',mul_one]; exact stoutExtensive K' _ ht t hh)
 rw [porch, norm_smul, Real.norm_of_nonneg he]; exact mul_le_mul_of_nonneg_left hu he
lemma recPointTax (V:GramM (mid m B))(S:Loom (mid m B))(H:Roof _ u e n S)(s:Grasp Y B e)(hp:s.roundZ ≤ (mid m B).val)(K':Ledger R v η r C V)(hx:V.path.Bounds V.funds μ D L')(ht:0 ≤ r)(t:1 ≤ R)(hb:0≤V.beta)(y: Orbit (mid m B)): ‖recX s V S y‖≤ Real.exp (taxY (More (mid m B)) V.beta V.p.threshold D L'+exPrice (mid m B) v η C):=by
 rw [Real.exp_add]
 exact (recPoint V S H s hp K' ht t y).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le.mp (principal_min V.p V.path _ hx hb y.1))) (Real.exp_pos _).le)
end YM.CF.Graph
#print axioms YM.CF.Graph.recPointTax
