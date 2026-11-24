import YM.CF.BProof.Oasis.Hearth
/-! mark families weights on slot P-pivot. -/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Oasis
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Crystal MeasureTheory Dew
open Lattice Tenant Lat Cube Tulip Scree Skye Spin Branch Stint Hearth Tape Palot RG Push.AbsoluteSums
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical Hearth ENNReal
attribute [local instance] opCStarAlgebra
variable {N:Side}{D:GramM N} {v h H α k:ℝ}
lemma inheritCost {N:Side}{A:Type}[Fintype A](W:A→Type)[∀ i,Fintype (W i)] (f:Sigma W→ℝ)(u:∀ i,0≤f i) (w:A→ℝ)(v:∀ i,∑ j:W i,f ⟨i,j⟩≤w i)(y:A→Support N)(z:Moment.Toll y w α H): Moment.Toll (y ∘ Sigma.fst) f α H:=by
 apply (tollPrice _ u _ _).mpr; intro i; apply le_trans (b:=Gas.bill_X y w α i) _ ((tollPrice _ z.nonneg _ _|>.mp z) i); unfold Gas.bill_X; rw [sum_filter,sum_filter,Fintype.sum_sigma]; apply sum_le_sum; intro j _; by_cases b:i∈y j; swap; · simp only [Function.comp_apply,b,ite_false,sum_const_zero]; rfl
 simp only [Function.comp_apply,b,ite_true]; rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (v j) (rent_pos ..).le
lemma alphaLot(a r:ℝ)(g:a*r≤1/2): a*r≤1/2:=g -- tune remove
namespace Cargo
variable (q:Cargo D h v)(p:1≤ h)(u:1≤ H)(t:H≤h)(e:D.p.supportExponent=1)(a:α*coverC D.p.B≤1/2)(r:0 ≤α)
def runR(q:Cargo D h v)(i:OptionR N):ℝ:=q.annual i.1 i.2.val
def runF(q:Cargo D h v)(i:OptionF N):ℝ:=q.far i.1 i.2.val
def roomAge(B:ℕ)(v:ℝ):ℝ:=payV (coverC B) v
include p e r a
lemma boughtR: Moment.Toll (fun i:Stem N=> lot D.p i.2) q.vouchR α (roomAge D.p.B (v+v)):=by
 apply forward (N:=N) (f:=OriginR) (u:=fun i=>coverNumber D.p.B i.2.val.2) (fun i=> by rw [mul_comm]; apply lot_price) (fun i _=>lot_ok ..) (fun i _=>seeT _ i.2 i.2.property) (q.vp p) _ r a; intro i; unfold heroes; rw [sum_filter]; have hx(b): (∑ j:Hub N,(if i=j.val.1 then q.vouchR (b,j)*Real.exp (coverNumber D.p.B j.val.2) else 0))≤v:=by have ht:= q.coastR i b; simpa only [BudgetPoint.mass,e,one_mul,mul_comm _ (q.vouchR _)] using ht
 rw [Fintype.sum_prod_type,Fintype.sum_bool]; exact add_le_add (hx true) (hx false)
lemma boughtF : Moment.Toll (fun i:Force N=> lot D.p i.val.1) q.vouchF α (roomAge D.p.B v):=by
 apply forward (r:=coverC D.p.B) (N:=N) (f:=fun i:Force N=> i.val.1.val.1) (u:=fun i=>coverNumber D.p.B i.val.1.val.2) (fun i=> by rw [mul_comm]; apply lot_price) (fun i _=>lot_ok D.p i.val.1) (fun i _=>seeT D.p i.val.1 i.val.1.property) (q.vF p) _ r a; intro i; unfold heroes; rw [sum_filter]; apply le_trans _ (q.coastF i); apply sum_le_sum; intro j _; unfold BudgetPoint.mass; by_cases g:i=j.val.1.val.1; · simp only [g,ite_true,j.val.1.property,e,one_mul]; rw [mul_comm]
 rw [if_neg g]; split; exact mul_nonneg (Real.exp_pos _).le (q.vF p _); rfl
include t u
lemma paidR: Moment.Toll (fun i:OptionR N=> lot D.p i.1.2) (Civic.costW (lineR N) q.runR H) α (roomAge D.p.B (v+v)):=by
 refine inheritCost StarR (Civic.costW (lineR N) q.runR H) ?_ q.vouchR ?_ _ (q.boughtR p e a r); · intro i; exact mul_nonneg (q.annual_pos ..) (pow_nonneg (zero_le_one.trans u) _)
 intro i; let b:= (Starry (Dwell N) (Scree.camp i.2.val.2)); apply le_trans _ (q.ann_sum i); apply le_trans (b:=∑ j∈b,Scree.tariff D.p i.2.val.1 h j * q.annual i j); swap; · exact sum_le_sum_of_subset_of_nonneg (subset_univ b) (fun j _ _=> mul_nonneg (tote p ..) (q.annual_pos ..))
 rw [← Finset.sum_attach b]; apply sum_le_sum; intro j _; unfold Civic.costW; change q.annual i j.val* H^(bkiln j.val).length ≤ _; rw [bkiln_size,mul_comm]; exact mul_le_mul_of_nonneg_right (tariffE _ _ (zero_le_one.trans p) (zero_le_one.trans u) t _) (q.annual_pos ..)
lemma paidF: Moment.Toll (fun i:OptionF N=> lot D.p i.1.val.1) (Civic.costW (lineF N) q.runF H) α (roomAge D.p.B v):=by
 refine inheritCost PartyF (Civic.costW (lineF N) q.runF H) ?_ q.vouchF ?_ _ (q.boughtF p e a r); · intro i; exact mul_nonneg (q.fend ..) (pow_nonneg (zero_le_one.trans u) _)
 intro i; let b:= (Wheat (Scree.camp i.val.1.val.2)); apply le_trans _ (q.f_sum i); apply le_trans (b:=∑ j∈b,Scree.tariff D.p i.val.1.val.1 h j * q.far i j); swap; · exact sum_le_sum_of_subset_of_nonneg (subset_univ b) (fun j _ _=> mul_nonneg (tote p ..) (q.fend ..))
 rw [← Finset.sum_attach b]; apply sum_le_sum; intro j _; unfold Civic.costW; change q.far i j.val* H^(bkiln j.val).length ≤ _; rw [bkiln_size,mul_comm]; exact mul_le_mul_of_nonneg_right (tariffE _ _ (zero_le_one.trans p) (zero_le_one.trans u) t _) (q.fend ..)
-- J locations; use uniform pre-H lower, sparse price estimate before confinement, uniform Reader valuations
end Cargo

def runJ(κ:ℝ)(v:OptionJ N) : ℝ:=κ* sitePrice
def amountJ(B:ℝ):ℝ:=2^(slotsu)* sitePrice*B^(slotsu)
lemma pJ{H:ℝ}(g:0≤H):0≤amountJ H:=by have ht:=zero_le_one.trans sitePrice_p; unfold amountJ; positivity
lemma paidJ(κ:ℝ)(k:0≤κ)(u:1≤H) (e:α≤1): Moment.Toll (fun i:OptionJ N=> {node i.1}) (Civic.costW (ArcJ N) (runJ κ) H) α (κ* amountJ H * Real.exp 1):=by
 have hH:=zero_le_one.trans u; have hS:0≤κ*sitePrice:=mul_nonneg k (zero_le_one.trans sitePrice_p); have hf:=pJ hH; let w:=κ*amountJ H; refine inheritCost (A:=Site N) (N:=More N) (fun i => ↥(JPick i)) (Civic.costW (ArcJ N) (runJ (N:=N) κ) H) ?_ (fun _=> w) ?_ (fun x:Site N=> {node x}) ?_
 · intro i; exact mul_nonneg hS (pow_nonneg hH _)
 · intro j; apply le_trans (sum_le_sum (g:=fun _=> κ*sitePrice*H^slotsu) _); swap; · intro i _; apply mul_le_mul_of_nonneg_left _ hS; apply pow_le_pow_right₀ u; show List.length _≤ _; rw [show (ArcJ N).line ⟨j,i⟩= (bkiln i.val).reverse from rfl,List.length_reverse,bkiln_size]; rw [←stake_count j]; exact card_le_card (mem_alloy ..|>.mp i.property).1
   rw [sum_const,card_univ,nsmul_eq_mul]; have hx:Fintype.card (JPick j)≤ 2^slotsu:=by rw [JPick,Fintype.card_coe,← stake_count j,←card_powerset]; exact card_le_card (filter_subset ..)
   apply le_trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hx) (mul_nonneg hS (pow_nonneg hH _))); unfold w amountJ; push_cast; apply le_of_eq; ring
 apply (tollPrice _ (fun _=> mul_nonneg k hf) _ _).mpr; intro i; unfold Gas.bill_X; rw [sum_filter]; by_cases v:∃ j:Site N, i=node j
 · obtain ⟨j,f⟩:=v; rw [sum_eq_single_of_mem _ (mem_univ j)]; rw [if_pos (mem_singleton.mpr f)]; dsimp only; unfold rent; rw [card_singleton,Nat.cast_one,mul_one]; exact mul_le_mul_of_nonneg_left (Real.exp_monotone e) (mul_nonneg k hf)
   exact fun i' _ u=>if_neg (fun g=>u (Tenant.needle ((mem_singleton.mp g).symm.trans f)))
 rw [sum_eq_zero]; · exact mul_nonneg (mul_nonneg k hf) (Real.exp_pos _).le
 exact fun j _=>if_neg (fun t=> v ⟨j,mem_singleton.mp t⟩)
end YM.CF.BProof.Oasis
