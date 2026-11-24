import YM.CF.BPress.Mount.Deep
/- issue eq:B-Ms actual Mark counterweight. Also weak regular-only.Cost per slot. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Mount
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf Primary
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Shot Till Store Skye Girt Scree Voice Noon Phase Extensor Stamps Grid Hazel Net Locale Push.AbsoluteSums --
variable {s m B N:Side} {D:BandWidth} {T: Sheet.Atlas}{X Y Z W:Pledge}{a:ℕ}{c d L y u v μ q ε:ℝ}{R:Driver (mid m B)}{P: Edition R}{G:Brace.Duet m B}{U:GramM (mid m B)}{p:Wish R X Y Z}
variable {K:Type}{g:K→R.Pose} (A:Bands (More (mid m B)) D)(F:Net (More (mid m B)) T L y c d a) (h:Tiling (More (mid m B))) (C:Calyx P g)
local notation "A0"=> Theatre (mid m B)
abbrev toolsF(N:Side):= Micro (More N) × Duo (More N)
variable (r:ℕ)(i:A.Index)(z:toolsF (mid m B))
abbrev ledgerTerm (T:Plain (mid m B)):= (∑ t: Tenor (More (mid m B)) with abyss A i r (scaffold t), C.body t T)+(∑ t: Support (More (mid m B)) with abyss A i r t,C.hull t T)
def CO := ledgerTerm A C r i (readingX A F h i z)
def candid : A0:= fun x=> Complex.exp (-CO A F h C r i x) • Chalk.pairTest A i F h x
namespace Silhouette
local notation "Λ"=> (mid m B)
variable (t: Passports R U G p P W q ε u μ v)
lemma reads(x y:Plain Λ)(q:Along (deep A i r) x y): ledgerTerm A C r i x=ledgerTerm A C r i y:=by
 unfold ledgerTerm; refine congrArg₂ (·+·) (sum_congr rfl (fun k b=> (C.pay k).local0 _ _ (q.drop ((mem_filter.mp b).2.2)))) (sum_congr rfl (fun k b=>(C.phaseRec k).local0 _ _ (q.drop ((mem_filter.mp b).2.2)))) -- tune
lemma CO_m : Measurable (CO A F h C r i):= by
 unfold CO ledgerTerm; refine Measurable.add (Finset.measurable_fun_sum _ (fun i _=> ((C.pay i).pay.meas.comp (reading_m A F h _)))) (Finset.measurable_fun_sum _ (fun i _=> ((C.phaseRec i).pay.meas.comp (reading_m A F h _))))
lemma invariant (X:Plain Λ)(M:Mach (More Λ)): ledgerTerm A C r i (τ X M)=ledgerTerm A C r i X:=by unfold ledgerTerm; simp_rw [(C.pay _).gauge,(C.phaseRec _).gauge] -- tune `_` simp
-- parameters intentionally separate Angle y and Clock budget ySpin `$` originally same g(x)? actually `y` = coupling hat, BOOK.g` is `BPress.g y`. change latter g parameter.
abbrev tax(q: ℝ) := Real.exp (((A.band i).card:ℝ)*(W.price+q))
abbrev yolk := Chalk.cost_site^(card (Chalk.withinX (A.band i)))
abbrev heightP(q:ℝ):= tax (W:=W) A i q*(yolk A i)
variable (Q:0≤μ)
include t Q
lemma tariff : ‖CO A F h C r i z‖ ≤ ((A.band i).card:ℝ)*(W.price+v):=by
 unfold CO ledgerTerm; rw [mul_add]; refine (norm_add_le ..).trans (add_le_add ((norm_sum_le ..).trans ?_) ((norm_sum_le ..).trans ?_))
 · exact (sum_le_sum (fun i _=>(C.pay i).pay.cost _)).trans (Abyss.budgetS A i r scaffold t.cruise W.pos.le)
 exact (sum_le_sum (fun i _=> (C.phaseRec i).pay.cost _)).trans (Abyss.budgetS A i r id t.grow Q)
lemma candid_p : YM.CF.BPress.Extends F A i (candid A F h C r i) (heightP (W:=W) A i v):=by
 let g'(x):= Complex.exp (-CO A F h C r i x); have he:=Chalk.guards A i F h; have hm:Measurable g':=(Complex.continuous_exp.measurable.comp (CO_m A F h C r i).neg); refine ⟨fun j=> IsMark.factor (c:=fun v=>g' (v,j)) (he.mark j) (fun U V u=>?_) (hm.comp (measurable_id.prodMk measurable_const)) (fun U=>?_ ), hm.smul he.meas,?_ ⟩
 · have hx:= (reading_local A F h i (U,j) (V,j) rfl u).drop (deep_sub A i r); apply congrArg (fun x:ℂ=>Complex.exp (-x)) (reads A C r i _ _ hx)
 · unfold g'; rw [Complex.norm_exp]; exact Real.exp_monotone ((le_abs_self _).trans ((Complex.abs_re_le_norm _).trans ((norm_neg ..).le.trans (tariff A F h C r i (U,j) t Q))))
 intro v' U p i' L A'; change g' _ • ( Chalk.pairTest A i F h _) = twist _ (_ • Chalk.pairTest A i F h _); rw [he.moves v' _ _ i' L, twist_scalar]; apply congrArg (· • (twist _ _)); unfold g' CO; rw [reads A C r i _ (τ (readingX A F h i (U,p)) A') ((reading_gauge A F h i (U,p) A' v').drop (deep_sub A i r)),invariant]
end Silhouette
end YM.CF.BPress.Mount
#print axioms YM.CF.BPress.Mount.Silhouette.candid_p
