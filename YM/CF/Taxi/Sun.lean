import YM.CF.Taxi.Amp
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
abbrev xca (X:Skye.Seat n):Vow.Aura n:= ⟨{X},singleton_nonempty X⟩
abbrev warmK (R:PathData SU.group)(p:Clip)(P:BudgetPoint)(o:Skye.Seat n)(b:AnalyticBridge.VerifiedReset.Low)(Y:Support (More n))(V: Orbit n): Cipher n:= Pastry.hollow (↑(b.live R p P o V.1)) -- no Y. not actual pay if no marks.L.
abbrev loanW (p:Clip)(P:BudgetPoint)(o:Skye.Seat n)(b:AnalyticBridge.VerifiedReset.Low)(Y:Support (More n))(V:Orbit n): Cipher n:= warmK R p P o b Y V - (if o∈Y then 0 else hollow (↑(b.mark R p * b.proxy R o V.1)))
private lemma pKw {u:Pane n→ℂ}(hx:LocalOn D u)(v:Measurable u)(w:GaugeInvariant u): ThemeR D (fun i: Orbit n=>Pastry.hollow (u i.1)):=by
 refine ⟨fun i j t l=> congrArg _ (hx _ _ t),fun _=> Flour.grainE.smul _,?_,fun i j=>?_⟩; swap
 · change Pastry.hollow (u _) = _; rw [w]; exact Subtype.ext (Eq.symm ((twist_scalar _ _ _).trans (by rw [map_one]; rfl)))
 let K:ℂ→Cipher n:=Pastry.hollow; exact ((show Continuous K from Continuous.subtype_mk (continuous_id.smul continuous_const) _).measurable.comp (v.comp measurable_fst))
private lemma stints{f:Pane n→ℂ}(p: ThemeR X (fun i: Orbit n=>Pastry.hollow (f i.1)))(u: ∀ V: Pane n,pingS P.threshold (X\Y) V→∀ D:Support (More n),Y⊆D→ Allows P.order (f ∘ pressQ P D V) 0 c)(hc:0 ≤ c) : Medal P X Y (oV fun i=> hollow (f i)) h ((P.order+1:ℝ)*c):=by
 let K:ℝ:= (P.order+1:ℝ)*c; refine ⟨p,Pi.single ∅ K, fun i=>?_,fun i v Z s=> ?_,?_⟩
 · rw [Pi.single_apply]; split_ifs; exact mul_nonneg (by positivity) hc; exact le_rfl
 · let x:=u i.1 v Z s; let g:= Woody.chit (∅:Finset (Dwell n)) (Rue.bare_p _ _ x); refine g.germ ?_; apply Eventually.of_forall; intro i; change _ • Pastry.poke ∅ = _ • (1:FC (Dwell n)); rw [poke,Poly.tag_void]; rfl
 simp [joinV,Pi.single_apply,mul_ite,stake,K] -- syntax missing f
private lemma stamp_f (p:Clip) (a:0≤Γ) :0≤ stampV R p P b Γ:=by
 unfold stampV; refine mul_nonneg (abs_nonneg _) (add_nonneg (add_nonneg ?_ (mint_p _ _ (mul_nonneg a (mul_nonneg (faceCost_nonneg ..) (sq_nonneg _))))) (mint_p _ _ (mul_nonneg a (mul_nonneg (by norm_num) (row_nonneg ..)))))
 exact mul_nonneg (by norm_num) P.threshold_pos.le
variable (p_:DayT P.order Γ)(ht:0≤Γ)(v:Decent p P)
include p_ ht v
lemma peakV : Medal P B_ Y (warmK R p P o b Y) h ((P.order+1:ℝ)*stampV R p P b Γ):=by
 let U:= Low.live R p b P o; let V:=Complex.ofRealCLM; apply stints (f:=V ∘ U) (pKw (fun i j g=> congrArg V (b.live_local R p v o i j g)) (V.continuous.measurable.comp (b.live_meas ..)) (fun i j=>congrArg V (b.live_gauge _ _ _ i j))) ?_ (stamp_f R b Γ p ht)
 intro i z D g; exact pulse_k R o i b Γ g v p_ ht z
private def chin(p:BudgetPoint)(a:ℝ):ℝ:= liteV p (a*((2:ℝ)⁻¹*(pairBill SU.group p *p.threshold^2)))
def glory_v (p:Clip)(Γ:ℝ)(P:BudgetPoint):ℝ:= (P.order+1:ℝ)*(stampV R p P b Γ + |b.mark R p| *chin P Γ)
lemma meansB : Medal P B_ Y (loanW R p P o b Y) h (glory_v R b p Γ P):=by
 have ht':0 ≤ chin P Γ:=mint_p _ _ (mul_nonneg ht (mul_nonneg (by norm_num) (mul_nonneg (pair_nonneg ..) (sq_nonneg _))))
 let X:=b.home R P o; let T:=warmK R p P o b Y; let t:= b.mark R p; let k:= b.proxy R o; let L:Pane n→ℂ:= fun V=> Complex.ofRealCLM (t * k V); have he:= peakV R o b Γ (Y:=Y) p_ ht v (h:=h); unfold loanW; by_cases h:o∈Y
 · simp only [h,↓reduceIte,sub_zero]; refine Medal.big (F:=T) he ?_ -- tune simplify before
   unfold glory_v; gcongr; exact le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) ht')
 let U':Copy n:= oV fun i=> hollow (L i); rw [show (fun V:Orbit n => _)= T - U' from ?_] -- tune expected vague
 swap; · funext i; rw [if_neg h]; rfl
 unfold glory_v; rw [mul_add,sub_eq_add_neg]; apply Medal.plus he; refine Medal.negT (stints (pKw (u:=L) ?_ ?_ ?_) ?_ (mul_nonneg (abs_nonneg _) ht')) -- pKw u binder
 · intro i j g; unfold L; rw [show k i=k j from b.proxy_local R o i j (agrees_mono g (Finset.coe_subset.mpr (b.clover_home R v.radius o)))]
 · exact Complex.ofRealCLM.continuous.measurable.comp (measurable_const.mul (b.proxy_cont ..).measurable)
 · intro i j; unfold L; rw [show k _=k j from b.proxy_gauge R o i j]
 intro W l D q
 let a:=AnalyticBridge.VerifiedReset.Bill.mul_left t (b.proxy_bill R o P); have hu:Signs P o (_ ∘ RG.increment W) (Γ*(|t| * ((2:ℝ)⁻¹*(pairBill SU.group P*P.threshold^2)))) := p_ _ _ _ _ _ _ a rfl W (ping_le (grow_b (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨b.small_home R P o,h⟩)) l))
 have hv:=mintK (D:=D) W _ _ hu; rw [mul_left_comm Γ |t|,scaleV] at hv; exact hv
-- exact loan recovery any Δ
lemma pulp_w (d:ℝ)(hq:Y=flags P.threshold U∩B_)(m:Y.Nonempty)(S:Ids n): d • (loanW R p P o b Y (U,S))= Pastry.hollow (↑(Low.loan R p b o P 0 d U)):=by
 -- Needs Fleet only for § E? baseline Loan nonstrict signs chosen on flagged branch.Strict(o). Since Ω from >, Healthy iff. 
 have ht:¬ Healthy P.threshold B_ U:=by obtain ⟨i,v⟩:= m; rw [hq] at v; exact fun u=> Finset.disjoint_left.mp u (mem_inter.mp v).2 (mem_inter.mp v).1
 have he:o∈Y ↔ ¬ Healthy P.threshold {o} U:=by rw [hq,mem_inter,and_iff_left (b.small_home R P o)]; unfold Healthy; simp
 unfold loanW warmK Low.loan; rw [if_neg ht, zero_add]; by_cases v:o∈Y
 · rw [if_pos v,if_neg (he.mp v),sub_zero,sub_zero]; apply Subtype.ext; change d • ((_ :ℂ) • (1:FC (Dwell n)))= _ • 1; rw [←smul_assoc]; congr 1; apply Complex.ext <;> simp -- tune
 rw [if_neg v, if_pos (not_not.mp (mt he.mpr v))]; apply Subtype.ext; change d • ((_ :ℂ) • (1:FC (Dwell n))-(_ :ℂ) • 1) = _ • 1; rw [←sub_smul,←smul_assoc]; congr 1; apply Complex.ext <;> simp <;> ring
omit p_ v ht
def price0 (Γ:ℝ)(P:BudgetPoint):ℝ:= (P.order+1:ℝ) * (2*P.threshold + liteV P (Γ*(faceCost SU.group P *P.threshold^2)) + chin P Γ)
def price1 (Γ:ℝ)(P:BudgetPoint):ℝ:=(P.order+1:ℝ)*liteV P (4*Γ)
lemma dotsP (a:ℝ)(P:BudgetPoint)(h:0 ≤ a): 0 ≤ price0 a P ∧ 0 ≤ price1 a P:=by
 have hp:=P.threshold_pos; exact ⟨mul_nonneg (by positivity : (0:ℝ)≤P.order+1) (add_nonneg (add_nonneg (mul_nonneg (by positivity) hp.le) (mint_p _ _ (mul_nonneg h (mul_nonneg (faceCost_nonneg ..) (sq_nonneg _))))) (mint_p _ _ (mul_nonneg h (mul_nonneg (by positivity) (mul_nonneg (pair_nonneg ..) (sq_nonneg _)))))),mul_nonneg (by positivity : (0:ℝ)≤P.order+1) (mint_p _ _ (mul_nonneg (by positivity) h))⟩
lemma oar_F(p:Clip)(Γ:ℝ)(P:BudgetPoint): glory_v R b p Γ P=|b.mark R p| * (price0 Γ P+ price1 Γ P * rowCost SU.group P (b.length R)) :=by
 unfold glory_v stampV price0 price1 liteV Jet.composeCost; ring
end YM.CF.Taxi
