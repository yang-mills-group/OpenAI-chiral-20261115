import YM.CF.Spark.Thrive
import YM.CF.Graph.Coif
import YM.CF.Paige.Kit
set_option autoImplicit false
noncomputable section
namespace YM.CF.Spark
open Function Filter Metric Finset NormedSpace Lattice Laurent Lat Tulip Rush Cube Tenant Mir Mir.Trip Phase Phase.Sample Branch MeasureTheory RG Wilson WilsonStartup RP Nova Kea Ave Fock SU CF.Jet Broc Petal Spire Scroll Peaks Pastry Pic Sods Paige Vault Brace Graph Dial
open scoped Topology BigOperators Matrix MatrixOrder ContDiff InnerProductSpace Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L B m N: Side}{e H a b c d v σ h Y:ℝ}{i j k n:ℕ}{O:Odd L.val}{T:Pricing j L O (Thread j)}{P:Grasp T B e}
local notation "n'"=>Domain m B
local notation "U'"=>Briar m B e
local notation "E'"=>Elf m B
local notation "M'"=>CSide m B
section
variable {I J: Type*}[LinearOrder I][Fintype I][LinearOrder J][Fintype J]
variable (E:I≃J)
lemma leap : Surjective (cartsL E):=by
 have ht: Module.finrank ℂ (Wave I)=Module.finrank ℂ (Wave J):=by simp [Wave,Ket, Fintype.card_congr E]
 exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ht (f:=(Fock.hoist E.toEmbedding ∅).toLinearMap)).mp (carts_inj _)
def crossL (A:FC J):FC I:= (Matrix.toEuclideanCLM (n:=Finset I) (𝕜:=ℂ)).symm ((pailL E.toEmbedding ∅).comp ((acts A).comp (Fock.hoist E.toEmbedding ∅)))
lemma crossed (A: FC J) (p:Wave I): cartsL E (acts (crossL E A) p)=acts A (cartsL E p):=by
 let f:=acts A (cartsL E p); obtain ⟨y,h⟩:= leap E (acts A (cartsL E p)); unfold acts crossL; rw [StarAlgEquiv.apply_symm_apply]; change cartsL E (pailL _ ∅ (acts A (cartsL E p)))=_; change _=acts _ _; rw [←h]; rw [show pailL _ _ (cartsL E y)= _ from (pourL E.toEmbedding ∅ (shelfG E) y)]
lemma cx_eq (A:FC J)(B:FC I)(s:∀ x,cartsL E (acts B x)=acts A (cartsL E x)) :crossL E A=B:=by apply Matrix.toEuclideanCLM.injective; apply ContinuousLinearMap.ext; intro x; apply carts_inj E; change cartsL E (acts _ _)=cartsL E (acts _ _); rw [crossed,s]
lemma cxC:Continuous (crossL E):= by
 let F:FC J→ₗ[ℂ] FC I:=
    { toFun:=crossL E
      map_add' a b:=cx_eq _ _ _ fun x=>by rw [act_add,act_add, ←crossed, ←crossed]; exact map_add (Fock.hoist E.toEmbedding ∅) _ _
      map_smul' c y:=cx_eq E (c • y) (c • crossL E y) fun x=> by rw [act_smul,act_smul,carts_s,crossed] }
 exact F.continuous_of_finiteDimensional
lemma cx_m(A B:FC J):crossL E (A*B)=crossL E A * crossL E B:=cx_eq E _ _ fun x=>by rw [act_mul,act_mul,crossed,crossed]
lemma cx_p(i:I):crossL E (put (E i))=put i ∧ crossL E (takeF (E i))=takeF i:=⟨cx_eq _ _ _ (fun _=>hoist_put E.toEmbedding ..),cx_eq _ _ _ (fun x=>hoist_t _ _ (shelfG E) i x)⟩
lemma cCash(x y:Wave I)(P:FC J): inner ℂ x (acts (crossL E P) y)=inner ℂ (cartsL E x) (acts P (cartsL E y)):=by rw [←crossed]; exact (sigh _ _ (shelfG ..) ..).symm
lemma boostP(A:FC I): ‖exp A-1‖ ≤ Real.exp ‖A‖-1:=by
 let s (n:ℕ):FC I:= ((n.factorial:ℝ)⁻¹) • A^n; let t(n:ℕ):ℝ:= ((n.factorial:ℝ)⁻¹) • ‖A‖^n
 have he: Summable (fun i:ℕ=>‖s i‖):= norm_expSeries_summable' (𝕂:=ℝ) A
 have hf: Summable t:= expSeries_summable' (𝕂:=ℝ) ‖A‖
 have hx: exp A-1=∑' i:ℕ,s (i+1):=by rw [congrFun (exp_eq_tsum ℝ), ← Summable.sum_add_tsum_nat_add 1 he.of_norm]; simp [s]
 rw [hx, Real.exp_eq_exp_ℝ, congrFun (exp_eq_tsum ℝ), ←Summable.sum_add_tsum_nat_add 1 hf]; change _ ≤ ∑ i∈range 1,t i+_ -1; rw [Finset.sum_range_one,show t 0=1 by simp [t],add_sub_cancel_left]
 have he':Summable (fun i:ℕ=> ‖s (i+1)‖):= he.comp_injective (add_left_injective 1)
 refine (norm_tsum_le_tsum_norm he').trans (he'.tsum_mono (hf.comp_injective (add_left_injective 1)) (fun i=>?_))
 unfold s t; dsimp only; rw [norm_smul,Real.norm_of_nonneg (by positivity), smul_eq_mul]; exact mul_le_mul_of_nonneg_left (norm_pow_le ..) (by positivity)
end
abbrev wallU(x:Briar m B e)(q:Room B e)(f:Foot m B)(K:Acres m→ Briar m B e→ Ewe m B):= (zeroOf x f q).cook (cloudD K x)
lemma plankCost(K:Briar m B e)(p:Room B e)(t:Foot m B)(Q:Acres m→ Briar m B e→Ewe m B)(Z:Acres m→ℝ) (s:1≤H)(u:Charge (welter m B e H s) (terr _) a c (fun S x=> cloudless (Q S x)) Z)(g:0≤a): ‖wallU K p t Q‖ ≤ Fintype.card (Index m)*c:=by
 unfold wallU zeroOf; rw [←Scree.tank_eq]; refine (Graph.billP _ _ (lensP t p K.property) s).trans ?_; -- tune shelf
 let G(i):= cloudless (Q i K); let b:=welter m B e H s
 refine (show b.fare (∑ i:Acres m,G i)≤_ from le_trans (b.pile ..) ((sum_le_sum (fun i _=>?_)).trans (cum Z u.rankV (fun i=>(u.pledge i).price) (fun i e=>gspan ((u.pledge i).shape e)))))
 exact ((u.pledge i).owns K).trans (le_mul_of_one_le_left (u.pledge i).price (rent_one g i))
-- actual leaf in test state and ℂ factors.
def chantV(P:Grasp T B e)(t:Foot m B)(K:Acres m→Briar m B e→ Ewe m B)(x:Briar m B e):= Complex.exp (-candle m B (P.cost m firstM) x.val) • cartsL (helix _).symm (leafR K x t P.baseY)
def seekV(m B:Side)(f: Skin m B → FC (Single (CSide m B))):Readers m B:= fun x=>crossL (helix (CSide m B)).symm (f x)
section
variable {s:1≤H}(R:Reg 0 e B)(Z: Vial P R a Y h c d) (q:P.roundZ ≤ (CSide m B).val)(K:Acres m→Briar m B e→ Ewe m B){y:Acres m→ℝ}
include Z q
lemma fired(x:Briar m B e)(f:Skin m B→FC (Single M'))(p:Effect s m B e 0 R k h d K y P.baseY): ∫ z, ratioR (R.W m) e 0 (R.time k) R.knob (R.c m) (fun x=> seekV m B f x.1) (x.val,z) ∂rains m= Complex.exp (amen R K P k x)*inner ℂ (mateK M') (acts (f x.val) (chantV P (R.c m) K x)):=by
 rw [p.atFiber]; unfold Ave.stroll; rw [p.scalarExp]; unfold chantV amen; rw [map_smul,inner_smul_right, Complex.exp_add, Complex.exp_add,Complex.exp_neg]; let N:=M'; let V:=leafR K x (R.c m) P.baseY; rw [seekV,cCash]; simp only [Wilson.bare,neg_zero,zero_mul,Real.exp_zero,Complex.ofReal_one,one_mul, Dial.mateK]; field_simp
abbrev skiff(m:Side)(h σ:ℝ)(k:ℕ):ℝ:= Fintype.card (Index m)*(σ^k*(Petal.bulk h 16*(1/3)))
set_option maxHeartbeats 300000 in
lemma worn(x:Briar m B e)(p:Effect s m B e 0 R k h d K y P.baseY)(g:0≤h): ‖chantV P (R.c m) K x-changeM P x.val firstM‖ ≤ Real.exp (skiff m h d k)-1:=by
 have he:= Z.synchronized m q x; unfold chantV changeM; rw [show chant _ _ _ _ _ _= _ from he,←smul_sub,norm_smul,negC,one_mul]
 let e:=helix M'; let V:=leafR K x (R.c m) P.baseY; let U:=sound m B (R.c m) x.val; let L:= wallU x P.baseY (R.c m) K; change ‖cartsL e.symm V - cartsL e.symm U‖≤_; rw [show cartsL e.symm V-cartsL e.symm U =cartsL e.symm (V-U) from (show _-cartsL e.symm U=_ from (map_sub (Fock.hoist e.symm.toEmbedding ∅) V U).symm),carts_n]; have hp: V-U=acts (exp L-1) U:=by rw [act_sub,act_one]; rfl
 rw [hp] -- orientation wrong
 have hx: ‖U‖=1:=(Z.valid.bond.val m x).2
 have hf: ‖acts (exp L-1) U‖ ≤ ‖exp L-1‖ * ‖U‖:= by apply ((acts (exp L-1)).le_opNorm U).trans_eq; exact congrArg (·*‖U‖) (Matrix.l2_opNorm_toEuclideanCLM (exp L-1)) -- tune
 rw [hx,mul_one] at hf; exact hf.trans ((boostP (I:=Elf m B) L).trans (sub_le_sub_right (Real.exp_le_exp.mpr (plankCost x P.baseY (R.c m) K (fun S=>d^k*y S) s p.occurrence (by positivity))) _))
end
end YM.CF.Spark
