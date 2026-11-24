import YM.CF.BProof.Temple.Wear
set_option autoImplicit false
set_option maxHeartbeats 290000
noncomputable section
namespace YM.CF.BProof.Bide
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory Cube SU Fock Lat Spire Scroll Pressure Tree RG
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
set_option synthInstance.maxSize 26000
open Skye Law
open Arbor
open Wager Frost Half Leg Rush Tulip Peaks TripD Scree Tap Haro ArborW RillW
namespace Gale
attribute [local instance] Wager.measureVal Wager.billVal
open Push.SectorMeasure Phase Brace Girt Vault Paige Drapes
variable {N P M C H L:Side}{R:Patch}{r l k j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e t:ℝ}
variable {U:Grasp Y H e}
local notation "Λ" => mid M H
local notation "Λ₁"=> mid C H
variable {F:Scree.Loom (mid M H)}{F₁:Scree.Loom (mid C H)}(i:Axis)(X:ClockD R r l k){α n:ℕ}{c z:ℝ}
variable {q:Chi}{G:Ratio (mid M H) (mid C H)} {T:StepData (Domain M H) (Domain C H)} {R':GramM (mid C H)}(E: Girt.BaseL U G R' F F₁ q z)
local notation "νβ"=> R'.beta
local notation "Pβ"=>R'.J.M
variable (L0:Roof (mid M H) c e l F) (Q:Vogue.Quartz (mid M H) α c l F) (p:T.patch.Branches T.kernel SU.group)(A: SpaceM) (h:T.ratio=ratio G) (hr:T.patch=R) (hu:G.count=R.L)
local notation "λS"=> integrated U F R' F₁ G T q z A.val
local notation "D_"=> stove U F R' F₁ G T q z A.val
variable {B:Body (mid M H)} (b:Soul i X B) (V:Rider (shade (mid M H) i true X.uF) (Leg.reach G (shade (mid M H) i true X.uF) k) i G j R'.J.M A)
namespace Soul
local notation "Λv"=>poleM i X G b V
local notation "Ωv"=> Travel i Λv * Λv
local notation "Ψ"=>wince G q z Ωv
local notation "ΛX"=>wince G q z Λv
local notation "βΓ"=> fuel T νβ F
local notation "κc"=> sqR i B
local notation "f_" x:max => (denZ R' U F₁ x)
-- wear in two parts. no assumption positivity.
variable (x:Orbit (mid M H))(y:Orbit (mid C H))
local notation "XT"=>poke F x
local notation "YT"=>F₁ y
-- change order of integration using Step budget, not bound on f(X). offset uniform cost not requested here. Spatial read fully Furn.
section ilk
variable {N P L:Side} {X₀ E₁ D' E':Type*}[MeasurableSpace X₀][MeasurableSpace E₁][NormedAddCommGroup D'][NormedSpace ℝ D'][CompleteSpace D']
private lemma trade(μ:Measure X₀)(ν:Measure E₁)[IsFiniteMeasure μ][IsFiniteMeasure ν] (V:X₀→ E₁→ D')(F:X₀→ D'→L[ℝ]ℂ)(p:∀ x,Integrable (V x) ν)(v:Integrable (fun x:X₀×E₁=> F x.1 (V x.1 x.2)) (μ.prod ν)) : (∫ x,F x (∫ y,V x y∂ν)∂ μ)= ∫ y,∫ x,F x (V x y)∂μ ∂ν:=by
 symm; simp_rw [← ContinuousLinearMap.integral_comp_comm (F _) (p _)]; exact (integral_integral_swap v).symm -- orientation tune
end ilk
variable [hG:Nonempty (Forest (ratio G))]
include L0 h p V hG E
private lemma val_b : Envelope (Function.uncurry Ωv):=by
 let g:= per_prec i X G b V; exact (Wager.engine (turnP i X G g).envy g.envy) -- tune engine p
lemma forwards : cup D_ F (sqR i B)=cup (denZ R' U F₁) F₁ (βΓ Ψ):=by
 let f(x):Orbit Λ₁→ Phys Λ:= λS x; let g(x:Orbit Λ):= (κc (poke F x)); let H(x:Orbit Λ)(y:Orbit Λ₁):= pass (g x) (f x y); have hp:Envelope (Function.uncurry f):= buoy E T h p A.val; have he: Envelope g:=Law.pull (q:=Frost.poke F) b.sq_price (measurable_fst.prodMk L0.bill); have h': Integrable (Function.uncurry H) ((city Λ).prod (city Λ₁)):= Law.pay (priceA hp (Law.pull (q:=Prod.fst) he measurable_fst)) -- tune args
 calc
    _ = ∫ y, ∫ x, H x y∂city Λ ∂city Λ₁:=trade _ _ f (fun x=>cupL (g x)) (fun x=>Law.pay (Law.pull (q:=Prod.mk x) hp measurable_prodMk_left)) h'
    _ = _:=by
       let v(y:Orbit Λ₁):= denZ R' U F₁ y; apply integral_congr_ae; apply Eventually.of_forall; intro y; let a:= v y; change (∫ x,H x y∂city Λ)= pass _ a; have ht(x:Orbit Λ): H x y= T.density νβ y.1 x.1 • pass (Ψ (poke F x) (F₁ y)) a:= point_r i X E A b V x y
       simp_rw [ht]; exact portal L0 p νβ Ψ (winceC G q z E.legal.1 E.legal.2 (val_b i X E L0 p A h b V)) (y.1,F₁ y) a -- tune
include Q hu
lemma together : cup D_ F κc=cup (denZ R' U F₁) F₁ (sqR i (βΓ ΛX)) :=by
 rw [forwards i X E L0 p A h b V,rustic i X G q z h hu E.legal.1 E.legal.2 L0 Q p νβ _ (per_prec i X G b V)] -- tune
end Soul
end Gale
end YM.CF.BProof.Bide
