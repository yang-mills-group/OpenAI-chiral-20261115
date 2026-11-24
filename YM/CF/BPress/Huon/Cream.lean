import YM.CF.BPress.Huon.Slate
/- meas.L(i). -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BPress.Huon
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Pf Primary Hazel Mount Stamps Skye Port Locale Cube Precision Next.SectorChange RG Sugar Honey
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace ContDiff Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Net Grid Driver Letter Letters Hazel Chrono Spin.Hole Actor House LocalH Sugar.Stage Wealth Weave Pressure Mount.Silhouette Awards Push.SectorMeasure Env Scree Vesper Shot Crew Honey Honey.Recipe Peel Peel.Spine Ledger Push.AbsoluteSums Mosaic Lilac Born Lilac.Stripe Peel.Along Rates
variable {m s N:Side}{B:BandWidth}{A: Bands (More (mid m s)) B}{R:Hangar (More (mid m s))}
local notation "Λ"=> mid m s
local notation "η"=> More Λ
variable {H: Sugar.Crew A}{T:GramM (mid m s)}{X: Sugar.Stage (mid m s)}{Y:Driver (mid m s)}{k r r':ℕ} {c q d t v ε e d' C D ζ δ τ u b C':ℝ}{p0 p1 p2 p3:Pledge}{h: Wish Y p0 p1 p2}{G: Brace.Duet m s}
namespace Pilot
open Push.AbsoluteSums
variable {B0: Born A R X Y} {P: Edition Y}{F:Rented R H X Y.d e k c}{Q:Stamp A R X Y}{W: Recipe (A:=A) T}
local notation "Ξ"=> Visit A R H
-- planting $Sa Truth.$
variable (l: Passports Y T G h P p3 q d ε t v) (p: Budgeting H W τ u D ζ δ C) (tH:Seer H R X k) (p':ShortP X H R r)(a':Mangrove R H W.M) (z: Fast H.y)
private lemma sumM {I Y:Type}[MeasurableSpace I][DecidableEq I][MeasurableSingletonClass I][Fintype I][MeasurableSpace Y]{L:Type}[MeasurableSpace L][AddCommMonoid L][MeasurableAdd₂ L]{S:Y→Finset I}(v:Measurable S)(f:I→Y→L)(p:∀ i,Measurable (f i)):Measurable fun y:Y=>∑ i∈S y,f i y:= askM S v (fun S y=>∑ i∈S,f i y) (fun _=>Finset.measurable_fun_sum _ (fun i _=> p i)) -- tune
include p z l
lemma dusk_m (o:SlotT A R){r:ℕ} : Measurable (duskWeight (ε:=ε) B0 P F Q W r o):=by
 have hc: Measurable (fun x:Ξ=>House.read A R x.val):= (recipe A R z).measurable.comp measurable_subtype_coe; have hp:= (vista_m H o).comp (measurable_subtype_coe (p:=Peel.points A R H)); let x0:Choir A R→Π i:SiteX A R, Realm B Λ R:=id; have he: Measurable fun x=> Huon.storm W (H:=H) x o:= sumM ((ice_m A R o).comp measurable_subtype_coe) _ (fun i=>(p.cold_m i).comp hc)
 have hu : Measurable fun x:Ξ=>leftP B0 P F Q r x o:= by
    refine sumM (v:=bucketM _ _ _ measurable_const hp) _ (fun j=>?_ ); unfold ζLeft; split; exact ((l.measure j).comp ((Γ_m F Q).comp (party_meas z))).sub measurable_const; exact measurable_const
 have hf : Measurable fun x:Ξ=>rightP B0 P r x o:= sumM ((upper_m H o).comp measurable_subtype_coe) _ (fun i=>(measurable_of_countable (fun z:Fin 5=>chast B0 P r i z)).comp ((chip_m _).comp measurable_subtype_coe))
 have hm : Measurable (fun x:Ξ=> shapeM x o X ε):=by
    let M(x:Ξ):=segZZ x o; let D(x:Ξ):= segYY (X:=X) x o; have A':Measurable M:= bucketM (plan A R) _ _ (H.flag_m.comp hc) hp; have B':Measurable D:=bucketM _ _ _ ((H.areaC_m ..).comp hc) hp; refine Measurable.mul (askM M A' (fun i x=> (Wheel.ζ i (κZ x))⁻¹) (fun i=> ((Wheel.ζ_C i).measurable.comp ((Crew.lock_m).comp hc)).inv)) (askM D B' (fun i x=>bill_phase (ε:ℂ) (κY x) i) (fun i=>(((Wheel.ζ_C i).measurable.comp ((Crew.can_m).comp hc)).inv.mul measurable_const))) -- tune askM g implicit
 exact hm.mul (Complex.continuous_exp.measurable.comp (((Complex.continuous_ofReal.measurable.comp he).add hu).add hf))
include tH p' a'
lemma payments (tX: SlotT A R)(K:Rates)(v:Banner B0 r' C')(ha:r'≤ mcap X H r)(t₁:(B.D+2*mcap X H r+1:ℕ)*blur r p3≤ C'/16) (g:Even R.L.val)(sB:K.pay ≤ (C'/16)*(R.L.val:ℝ)^3)(s₁: Pilot.costη R p3 B (mcap X H r)+chargeP (B:=B) (X:=X) R ε ≤ K.bad) (s₂:K.severe≤ Port.reward B.D H.κ H.y T.funds) (a:0<ε) : ∃ f, PaidQ tX K H (duskWeight (ε:=ε) B0 P F Q W r tX) f:=by
 refine cores tX K (duskWeight (ε:=ε) B0 P F Q W r tX) (dusk_m l p z tX) z tH.charter.port (fun x h=> (?_)) (fun x y v h u=> sharing l p tH p' a' x y tX v h u); -- tune `dusk_m l p z _`. maybe sharing binder order.
 refine ⟨ brilliant (F:=F) l p p' tX x h K v ha t₁ g sB s₁ s₂ a, fun i l=>?_⟩; obtain ⟨z,b⟩:= Finset.mem_sdiff.mp (show i∈tX \ vicinity H x.val from upper_l h ▸ l); exact ⟨_, (grade_t F x b).1 (pay_p x.val h z),funext fun i=> ins F x b i⟩ -- tune θ
end Pilot
end YM.CF.BPress.Huon
