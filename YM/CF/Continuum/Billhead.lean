import YM.CF.Graph.Core
import YM.CF.Continuum.Extensive

/-!
# Exponential-in-volume absolute-price estimate

Left side is the **relative** density of the actual history with scalar "v"
removed. Rework pieces of `Graph` proofs with row budgets to the very end (see
`Extensive.lean`) rather than a bound involving the square/cube of the
volume. We retain the old estimate on the no-flags event (including `pittance`
requirement). Cost of stepping away from a whole-box no-flags calculation, for
a normalized expectation, is still a blocking estimate at fixed x (measure
large family; see next file).
-/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Sods Wilson PathData Precision Tree Work.F03
variable {N:Side}{t:ℝ}
open MeasureTheory Cascade Vale CF.Paige Vault Nova
open Emu Flare
variable {α:Type*}{m B L:Side}{j n:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e v b c a l r K u η vA k s r' D L' C μ y R w z:ℝ}{P:Grasp Y B e}{hP:Pearl P}
lemma energy_low {G:Gauge}{a b c L:ℝ}(P:BudgetPoint)(X:PathData G)(Q:Clip)(hx:X.Bounds Q a c L)(hp:0≤b)(V:Config G N): -taxY N b P.threshold c L ≤ X.inChannels Q P b V:=by
 have he(s:Signed): -taxY N b P.threshold c L ≤ X.principal Q P b (pull s 0 V):=by
    let U:=pull s 0 V; obtain ⟨A,B⟩:= oath hx P U; unfold PathData.principal; have h(i:Face (Per N)):0 ≤ X.baseTerm Q P U i:=by
       unfold baseTerm; apply add_nonneg
       · unfold clipped; split; exact div_nonneg (mul_nonneg Q.quadratic_pos.le (sq_nonneg _)) (by positivity); exact mul_nonneg (mul_nonneg Q.tail_pos.le P.threshold_pos.le) (G.chord_nonneg _)
       split <;> positivity
    refine le_trans ?_ (add_le_add (mul_le_mul_of_nonneg_left (add_le_add (sum_nonneg (fun i _=>h i)) (neg_le_of_abs_le A)) hp) (neg_le_of_abs_le B)); exact le_of_eq (by unfold taxY; ring)
 apply ((mul_le_mul_of_nonneg_left (sum_le_sum (s:=univ) (fun i _=> he i)) (show 0≤ (Fintype.card Signed:ℝ)⁻¹ by positivity))).trans'; simp
lemma extensive_price (V:GramM (mid m B))(S:Loom (mid m B))(H:Roof _ u e n S)(s:Grasp Y B e)(hp:s.roundZ ≤ (mid m B).val)(K':Ledger R v η r C V)(hx:V.path.Bounds V.funds μ D L')(ht:0 ≤ r)(t:1 ≤ R)(hC:0 ≤ C)(hb:0≤V.beta)(y: Orbit (mid m B)): ‖recX s V S y‖≤ Real.exp (taxY (More (mid m B)) V.beta V.p.threshold D L')*Real.exp (flagBill (mid m B) v η C):=by
 have hh:= (s.broadness _ hp V.J.M).projection (S y) (H.paid y)
 let A:=cab V s S y; let w:= past V y.1; have he:0 ≤ w:= (Real.exp_pos _).le; have hp':‖A‖=1:= (sea_g hp (S y) (H.paid y) V.J.M).2; have hu:‖beam V s S y‖ ≤ Real.exp (flagBill (mid m B) v η C):=(spentS _ _ A).trans (by rw [hp',mul_one]; exact extensive_mile K' _ ht t hC hh)
 rw [porch,norm_smul]; exact mul_le_mul ((Real.norm_of_nonneg he).trans_le (Real.exp_le_exp.mpr (neg_le.mp (energy_low V.p V.path _ hx hb y.1)))) hu (norm_nonneg _) (Real.exp_pos _).le -- neg?
variable (V:GramM (mid m B))(S:Loom (mid m B))
variable (Q: Pic.Span hP K b v c l r' n)(H:SkinT V S e)
include H Q
lemma outside_price (T:Orbit (mid m B))(O:Opt (α:=α) (mid m B))(h:n ≤ (mid m B).val)(hYA:T∉ Lace V)(B':Ledger R u η r C V)(a:0≤r)(hP:1≤R)(hC:0≤C)(hp:‖Emu.gain O.R‖ ≤ (mid m B).val^2)(g: V.path.Bounds V.funds μ D L')(hv:0≤V.beta)(hw:0≤w)(vL:w≤V.funds.linear): let N:=mid m B
    ‖recW O P V S T-baseW O P V S T‖ ≤ lite O *Real.exp (flagBill N u η C-kinetic (More N) V.p D L' V.beta w) :=by
 intro N; obtain ⟨v,k,F⟩:=H.wave; have hh:= (P.broadness _ (Q.plan m h).1 V.J.M).projection (S T) (F.paid T); let A:=past V T.1; let X:= lite O; let f:= flagBill N u η C; have ht:0 ≤ X:=by unfold X lite; positivity; -- tune
 have he:0≤A:=(Real.exp_pos _).le; let P':= cab V P S T; have hg:‖P'‖=1:=(sea_g (Q.plan m h).1 (S T) (F.paid T) V.J.M).2; have hu:‖beam V P S T‖ ≤ Real.exp f:= (spentS _ _ P').trans (by rw [hg,mul_one]; exact extensive_mile B' _ a hP hC hh)
 let x:= kinetic (More N) V.p D L' V.beta w; have hs:A≤Real.exp (-x):= Real.exp_le_exp.mpr (neg_le_neg (fullH g V.p T.1 hw vL hv hYA)); unfold baseW recW; rw [dim,Set.indicator_of_notMem hYA,zero_smul,sub_zero,porch,(feel_r O _ _ P' _).1,norm_smul]; change ‖A‖*_ ≤ X*Real.exp (f-x); rw [Real.norm_of_nonneg he]; exact (mul_le_mul hs ((earn O _ _ hp).trans (mul_le_mul_of_nonneg_left hu ht)) (norm_nonneg _) (he.trans hs)).trans_eq (by rw [sub_eq_add_neg,Real.exp_add]; ring)
lemma together_ledger(W:Ledger R u η r C V)(a:0<r)(t:0≤vA)(k':0≤k)(h:1≤R)(g:V.path.Bounds V.funds μ D L')(hv:0≤V.beta)(w':0≤w)(vL:w≤V.funds.linear)(l:n ≤ (mid m B).val)(hC:0≤C)(hy:0≤y)(f:∀ T∈Lace V, Gall.Yep k (mateK (mid m B)) (changeM (m:=m) P T.1 V.J.M) (y*Kea.angel m P V.J.M))(f':∀ T∈Lace V,∀ i:LeanV (Single (mid m B)),Pays k (drawT (spar j V.J.M T.1) i) R)(b:∀ T∈Lace V,HelpP T.1 vA r)(l':pittance (mid m B) vA C≤1)(O:Opt (α:=α) (mid m B))(hp:‖gain O.R‖ ≤ (mid m B).val^2): let z:= baton (mid m B) u vA C k
     phM V O P S ≤ drip V P*(z*y*feeP O k)+ lite O *Real.exp (flagBill (mid m B) u η C-kinetic (More (mid m B)) V.p D L' V.beta w):=by
 intro z; let N:=mid m B; let A:=Kea.angel m P V.J.M; let Y:=lite O * Real.exp (flagBill N u η C-kinetic (More N) V.p D L' V.beta w); have he:0≤Y:=by unfold Y lite; positivity
 -- dim on flag complement zero
 let F(x):= recW O P V S x-baseW O P V S x; let K:=z*(y*A)*feeP O k
 have hh (x): ‖F x‖ ≤ dim V x*K + Y:=by by_cases ht:x∈ Lace V; exact le_trans (pall_b V S Q H x O l ht W (b _ ht) t a.le (zero_le_one.trans h) k' hC hp (f _ ht) hy (f' _ ht) l') (le_add_of_nonneg_right he); rw [dim, Set.indicator_of_notMem ht,zero_mul,zero_add]; exact outside_price V S Q H x O l ht W a.le h hC hp g hv w' vL
 have ht:= bonB W g; obtain ⟨p,q⟩:= integrable_s V S Q H ht O l; let μ:=city N; have hA:= ((worth ht).integrable μ).mul_const K; apply le_trans (integral_mono (p.sub q|>.norm) (hA.add (integrable_const _)) hh); apply le_of_eq; change (∫ x, dim V x*K + Y ∂μ)=drip V P*(z*y*feeP O k)+ Y; change Integrable (fun x=>dim V x*K) (city _) at hA; unfold μ N; rw [integral_add hA (integrable_const _), integral_mul_const,integral_const,probReal_univ,one_smul]; unfold drip K angle Y A; ring -- tune
end YM.CF.Window
