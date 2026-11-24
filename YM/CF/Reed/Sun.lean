import YM.CF.Reed.Amp
import YM.CF.Taxi.Sun
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup Vow
variable {p:Clip}(R: PathData SU.group)(o:Site (More n))(U:Pane n)
local notation "Gp"=> SU.group
variable (b: AnalyticBridge.VerifiedReset.Low) (Γ:ℝ)
local notation "B_"=> Low.home R b P o
local notation "kP"=> P.threshold
private lemma pKw {u:Pane n→ℂ}(hx:LocalOn D u)(v:Measurable u)(w:GaugeInvariant u): ThemeR D (fun i: Orbit n=>Pastry.hollow (u i.1)):=by
 refine ⟨fun i j t l=> congrArg _ (hx _ _ t),fun _=> Flour.grainE.smul _,?_,fun i j=>?_⟩; swap
 · change Pastry.hollow (u _) = _; rw [w]; exact Subtype.ext (Eq.symm ((twist_scalar _ _ _).trans (by rw [map_one]; rfl)))
 let K:ℂ→Cipher n:=Pastry.hollow; exact ((show Continuous K from Continuous.subtype_mk (continuous_id.smul continuous_const) _).measurable.comp (v.comp measurable_fst))
private lemma stints{f:Pane n→ℂ}(p: ThemeR X (fun i: Orbit n=>Pastry.hollow (f i.1)))(u: ∀ V: Pane n,pingS P.threshold (X\Y) V→∀ D:Support (More n),Y⊆D→ Allows P.order (f ∘ pressQ P D V) 0 c)(hc:0 ≤ c) : Medal P X Y (oV fun i=> hollow (f i)) h ((P.order+1:ℝ)*c):=by
 let K:ℝ:= (P.order+1:ℝ)*c; refine ⟨p,Pi.single ∅ K, fun i=>?_,fun i v Z s=> ?_,?_⟩
 · rw [Pi.single_apply]; split_ifs; exact mul_nonneg (by positivity) hc; exact le_rfl
 · let x:=u i.1 v Z s; let g:= Woody.chit (∅:Finset (Dwell n)) (Rue.bare_p _ _ x); refine g.germ ?_; apply Eventually.of_forall; intro i; change _ • Pastry.poke ∅ = _ • (1:FC (Dwell n)); rw [poke,Poly.tag_void]; rfl
 simp [joinV,Pi.single_apply,mul_ite,stake,K] -- syntax missing f
private lemma stamp_f (p:Clip) (a:0≤Γ) :0≤ stamp_KB R p P b Γ:=by
 unfold stamp_KB; refine mul_nonneg (abs_nonneg _) (add_nonneg (add_nonneg ?_ (mint_p _ _ (mul_nonneg a (mul_nonneg (faceCost_nonneg ..) (sq_nonneg _))))) (mint_p _ _ (mul_nonneg a (mul_nonneg (row_nonneg ..) (sq_nonneg _)))))
 exact mul_nonneg (by norm_num) P.threshold_pos.le
variable (p_:DayT P.order Γ)(ht:0≤Γ)(v:Decent p P)
include p_ ht v
lemma peakB : Medal P B_ Y (warmK R p P o b Y) h ((P.order+1:ℝ)*stamp_KB R p P b Γ):=by
 let U:= Low.live R p b P o; let V:=Complex.ofRealCLM; apply stints (f:=V ∘ U) (pKw (fun i j g=> congrArg V (b.live_local R p v o i j g)) (V.continuous.measurable.comp (b.live_meas ..)) (fun i j=>congrArg V (b.live_gauge _ _ _ i j))) ?_ (stamp_f R b Γ p ht)
 intro i z D g; exact pulse_cB R o i b Γ g v p_ ht z
private def chin(p:BudgetPoint)(a:ℝ):ℝ:= liteV p (a*((2:ℝ)⁻¹*(pairBill SU.group p *p.threshold^2)))
def paidV (p:Clip)(Γ:ℝ)(P:BudgetPoint):ℝ:= (P.order+1:ℝ)*(stamp_KB R p P b Γ + |b.mark R p| *chin P Γ)
lemma means_X : Medal P B_ Y (loanW R p P o b Y) h (paidV R b p Γ P):=by
 have ht':0 ≤ chin P Γ:=mint_p _ _ (mul_nonneg ht (mul_nonneg (by norm_num) (mul_nonneg (pair_nonneg ..) (sq_nonneg _))))
 let X:=b.home R P o; let T:=warmK R p P o b Y; let t:= b.mark R p; let k:= b.proxy R o; let L:Pane n→ℂ:= fun V=> Complex.ofRealCLM (t * k V); have he:= peakB R o b Γ (Y:=Y) p_ ht v (h:=h); unfold loanW; by_cases h:o∈Y
 · simp only [h,↓reduceIte,sub_zero]; refine Medal.big (F:=T) he ?_ -- tune simplify before
   unfold paidV; gcongr; exact le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) ht')
 let U':Copy n:= oV fun i=> hollow (L i); rw [show (fun V:Orbit n => _)= T - U' from ?_] -- tune expected vague
 swap; · funext i; rw [if_neg h]; rfl
 unfold paidV; rw [mul_add,sub_eq_add_neg]; apply Medal.plus he; refine Medal.negT (stints (pKw (u:=L) ?_ ?_ ?_) ?_ (mul_nonneg (abs_nonneg _) ht')) -- pKw u binder
 · intro i j g; unfold L; rw [show k i=k j from b.proxy_local R o i j (agrees_mono g (Finset.coe_subset.mpr (b.clover_home R v.radius o)))]
 · exact Complex.ofRealCLM.continuous.measurable.comp (measurable_const.mul (b.proxy_cont ..).measurable)
 · intro i j; unfold L; rw [show k _=k j from b.proxy_gauge R o i j]
 intro W l D q
 let a:=AnalyticBridge.VerifiedReset.Bill.mul_left t (b.proxy_bill R o P); have hu:Signs P o (_ ∘ RG.increment W) (Γ*(|t| * ((2:ℝ)⁻¹*(pairBill SU.group P*P.threshold^2)))) := p_ _ _ _ _ _ _ a rfl W (ping_le (grow_b (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨b.small_home R P o,h⟩)) l))
 have hv:=mintK (D:=D) W _ _ hu; rw [mul_left_comm Γ |t|,scaleV] at hv; exact hv
omit p_ v ht
def fee1K (Γ:ℝ)(P:BudgetPoint):ℝ:=(P.order+1:ℝ)*liteV P (Γ)
lemma cash_f (a:ℝ)(P:BudgetPoint)(h:0 ≤ a):  0 ≤ fee1K a P:=by
 exact mul_nonneg (by positivity : (0:ℝ)≤P.order+1) (mint_p _ _ h)
lemma rise_y(p:Clip)(Γ:ℝ)(P:BudgetPoint): paidV R b p Γ P=|b.mark R p| * (price0 Γ P+ fee1K Γ P * rowCost SU.group P (b.length R)*(P.threshold*Real.exp ((b.length R)/p.relaxation))^2) :=by
 unfold paidV stamp_KB price0 fee1K liteV Jet.composeCost; ring_nf <;> rfl
end YM.CF.Taxi
