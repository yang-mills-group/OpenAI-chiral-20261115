import YM.CF.BProof.Oasis.Table
import YM.CF.BProof.Weights.Supply
/-! The NPL log price. B_j upper tracked by M parameters; don't consume y here.
Even pure-budget logs paid at same rates. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Oasis
open Function Filter Fock Finset NormedSpace Garden Align Wick Double Pastry Crystal MeasureTheory Dew
open Lattice Tenant Lat Cube Tulip Scree Skye Spin Branch Stint Hearth Tape Palot RG Push.AbsoluteSums Civic
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical Hearth ENNReal
attribute [local instance] opCStarAlgebra
variable {N:Side} {v h C H α κ:ℝ}{D: GramM N}
def Cargo.runs (q:Cargo D h v)(κ:ℝ)(i:Options N):ℝ:= Sum.elim (runJ κ) (Sum.elim q.runR q.runF) i
def mainW(B:ℕ)(H κ v:ℝ):ℝ:= κ*amountJ H*Real.exp 1+(Cargo.roomAge B (v+v)+Cargo.roomAge B v)
lemma pays (q:Cargo D h v)(p:1≤h)(u:1≤ H)(t:H≤h)(e:D.p.supportExponent=1)(a:α*coverC D.p.B≤1/2)(r:0≤α)(hr:α≤1)(d:0≤κ): Moment.Toll (fun i=>(streets D.p i).val) (Civic.costW (Ark N) (q.runs κ) H) α (mainW D.p.B H κ v):=by
 have f:= q.paidR p u t e a r; have i:= q.paidF p u t e a r; have U:=paidJ (N:=N) κ d u hr
 have v:=Moment.Toll.sum _ _ U _ _ (Moment.Toll.sum _ _ f _ _ i); let Z(v₁ v₂:Type):=Unit; convert! v using 1; · funext i; rcases i with i|(i|i)<;> rfl
 funext i; rcases i with i|(i|i) <;> apply congrArg₂ (· * ·) rfl <;> exact congrArg (fun r:ℕ=> H^r) (List.length_map _)
variable {j:ℕ}{a b l r δ c ν η:ℝ}{P:Spin.Ready j a b l r}{F: Core j a b l r N}
abbrev Marks (G:Honor P F δ)(y:Pay)(c ν η:ℝ):= TariffE (Tape.kiln G.1 c ν η|>.mark) y paymentE
structure Tube (D:GramM N)(y:Pay)(h κ v α C:ℝ):Prop where
 cost : coins y ≤ h
 blur : α ≤ y.rate/2
 spill : puffPrice (y.rate/2)* mainW D.p.B (coins y) κ v ≤ C
 height : 0≤ κ
 norm : 0< α
 shelf : α ≤ 1
 chew : α*coverC D.p.B ≤ 1/2
 knot : D.p.supportExponent=1
 safeB : 0<C
 small : Roots.mild α C
variable {y:Pay}{G: Honor P F δ} (U:Marks G y c ν η)(q:Cargo D h v)
theorem Tube.known (T:Tube D y h κ v α C): Able (plaza D.p N) y.rate C (coins y) α (mainW D.p.B (coins y) κ v) U.award (q.runs κ):=by
 let d:=coins y; have he:=coin_ge y; have h:=T.height; refine ⟨T.norm,T.safeB,T.small,grant G D.p U,T.blur,pays q (he.trans T.cost) he T.cost T.knot T.chew T.norm.le T.shelf h,fun i _=>plazaHeat ..,?_,T.spill⟩; rintro (i|(i|i)); exact mul_nonneg h (zero_le_one.trans sitePrice_p); exact q.annual_pos ..; exact q.fend ..
lemma cKnown(x:Loft F δ c ν η){W:Options N→ℂ}(g:∀ i,‖W i‖≤ q.runs κ i): Known (U.eye x) W U.award (q.runs κ):= ⟨fun i j S _=> (U.expo i j S).bounded x,g⟩
-- strength payment pre-y, options.
abbrev spanT (x:ℝ) := MeasureTheory.Measure.dirac x -- remove
lemma Dec_cost(p:1≤h)(i:Stem N){u:ℝ}(f:‖u‖≤1)(x:Pane N):‖DecR D u x i‖ ≤ q.vouchR i:=by
 have he : q.annual i ∅ ≤ q.vouchR i:=by
    have he:= single_le_sum (f:= fun j:Finset (Dwell N)=> Scree.tariff D.p i.2.val.1 h j*q.annual i j) (fun j _=>mul_nonneg (Cargo.tote p ..) (q.annual_pos ..)) (mem_univ ∅)|>.trans (q.ann_sum i); refine le_trans ?_ he; apply le_mul_of_one_le_left (q.annual_pos ..); simpa only [card_empty,pow_zero] using (tariffE _ _ (zero_le_one.trans p) zero_le_one p (∅:Finset (Dwell N)))
 rw [DecR,norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) f).trans ((q.annualCost i ∅ x).trans he)
lemma f_cost(f:Pollen (Site (More N)))(x:Orbit N)(i:OptionF N):‖RateF D f x i‖ ≤ q.runF i:=by rw [RateF,norm_mul,style_one,one_mul]; apply q.farCost -- tune runF
lemma r_cost{vT:ℝ}(p:‖vT‖≤1)(x:Pane N)(i:OptionR N):‖FeeR D vT x i‖≤ q.runR i:=by rw [FeeR,norm_smul]; exact (mul_le_of_le_one_left (norm_nonneg _) p).trans (q.annualCost ..)
lemma j_cost{Y:Plant N}{ε:ℂ}(h:‖ε‖ ≤κ)(p: ∀ i, ‖Y.leaf i‖≤ sitePrice)(S:Support N)(x:Loft F δ c ν η)(w:Pollen (Site N)) (i:OptionJ N): ‖tokenJ S w ε Y (coreB x) i‖≤ runJ κ i:=by
 unfold tokenJ; split; · rw [norm_mul,norm_mul,glow_p,mul_one]; apply mul_le_mul h _ (norm_nonneg _) ((norm_nonneg _).trans h); have hr:Ride ..:= x.property; apply (coeffJ_bound (A:=Y.leaf i.1) (s:=chef i.1) (C:=coreB x) (hr.pores 1 Wick.walk1).2 (chefCom ..) (hr.pores 1 Wick.walk1).3 i.2.val ((mem_alloy ..|>.mp i.2.property).1)).trans; apply (actuary ..).trans; rw [show ‖Fock.vacuum (Single N)‖=1 by simp [Fock.vacuum,basisKet],mul_one]; exact p _
 rw [norm_zero]; exact mul_nonneg ((norm_nonneg _).trans h) (zero_le_one.trans sitePrice_p)
end YM.CF.BProof.Oasis
