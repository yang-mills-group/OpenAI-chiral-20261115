import YM.CF.Fixed.Voltage.OfferF
/-!
Masked kinetic safety. The kinetic here is derivative of ACTUAL clipped
scalar in these RG models, not continuum local! Need keep full flag symmetry.
Adapts Beau/CF proofs (genuine monetary path); no pressure bound post-root yet.
-/
set_option autoImplicit false
set_option maxHeartbeats 720000
noncomputable section
namespace YM.CF.Fixed.Voltage
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
variable{n:Side} {x h:ℝ}
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup Collection
open Trees Salt Beau Push.BetaTransport Reef
variable(P:BudgetPoint)(R:PathData SU.group){q:Clip}{σ C Λ:ℝ}(p:R.Bounds q σ C Λ)(A Γ:ℝ)(D': DayT P.order Γ)(DA: OriK P.order A)(hc:0≤Γ)(ha:0≤ A)(hw:Decent q P)(hp:Geo.Width P q σ)(hn:60 <(More n).val)
local notation "Rd"=> (P.supportExponent+1+1)
variable (T:Ids n)(hv:1 ≤ h)(hL:(P.supportExponent+1+1)/(P.B:ℝ)≤σ/8)(r: Rare R)
-- heads literal valuations
local notation "GK"=>SU.group
local notation "M"=> More n
variable (D:Support (More n))(o:Site (More n))
private def petF(i:Site (More n))(V:Pane n):ℝ:= (∑ a:PlaqAxes,inner ℝ (AnalyticBridge.VerifiedReset.petals V i a) (AnalyticBridge.VerifiedReset.petals V i a))/2
private abbrev cope (i:Site (More n)) := oV (moldV n ∘ petF i)
abbrev headCharge(P:BudgetPoint):ℝ:= (2:ℝ)⁻¹*(∑ _i:PlaqAxes, pairBill SU.group P * P.threshold^2)
private lemma spoke (o:Site M): AnalyticBridge.VerifiedReset.Bill P o (Healthy P.threshold {o}) (headCharge P) (petF o):=by
    unfold petF headCharge; simp_rw [div_eq_inv_mul]; convert Bill.mul_left (2:ℝ)⁻¹ (Bill.sum univ (fun i _=>pair_paid (G:=GK) P o i i)) using 1; norm_num
private lemma pet_gauge(g:Site M→ SU.group.El)(V:Pane n) : petF o (Lattice.gauge g V)=petF o V:=by unfold petF; simp_rw [AnalyticBridge.VerifiedReset.petals_gauge,StressFlux.inner_adjoint] -- maybe lemma direction
private lemma pet_theme : ThemeR univ (cope o) :=by
    let F:= cope o; refine ⟨fun U V p _=> congrArg (fun V=> moldV n (petF o V)) (completeV (n:=n) _ _ p),fun i=>?_,?_,fun V g=>?_⟩ -- target binder
    · change Flour _ (moldV n (petF o i.1)).val; rw [mon_v]; exact Flour.grainE.smul _
    · exact ((moldV n).continuous.comp (show Continuous (petF o) from (by unfold petF; fun_prop))).measurable.comp measurable_fst
    simp only [cope,oV,Function.comp_apply]; rw [pet_gauge]; change _= paintR false false _ ((petF o V.1) • 1); rw [map_smul,map_one]; rfl
abbrev spineBudget (P:BudgetPoint)(Γ:ℝ):ℝ:= (P.order+1:ℝ)*liteV P (Γ*headCharge P)
private abbrev meterC (P:BudgetPoint)(o:Site (More n)):Copy n:=oV (moldV n ∘ AnalyticBridge.VerifiedReset.heads P o)
include hc D'
private lemma surplusM (t:o∉D): Medal P univ D (cope o) h (spineBudget P Γ):=by
 let i:=o; let V':=spineBudget P Γ; have hp:= spoke P i; have hb:0≤V':= mul_nonneg (by positivity) (mint_p _ _ (mul_nonneg hc hp.nonneg)); refine ⟨pet_theme _, Pi.single ∅ V',fun i=>by rw [Pi.single_apply]; split_ifs; exact hb; exact le_rfl ,fun i' p Y m=>?_,?_⟩
 · have he : Healthy P.threshold {i} i'.1:= ping_le (grow_b (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨mem_univ i,t⟩)) p); let V:=i'.1; let U:= ((Complex.ofRealCLM ∘ petF i) ∘ pressQ P Y V); have hw:Allows P.order U 0 (liteV P (Γ*headCharge P)):= mintK _ _ _ (D' _ _ _ _ _ _ hp rfl V he); have hk:= Rue.bare_p _ _ hw; refine (Woody.chit (∅:Finset (Dwell n)) hk).germ ?_; filter_upwards with x; change _= (moldV n (petF i (pressQ _ _ _ x))).val; rw [mon_v]; unfold Pastry.poke; rw [Pastry.Poly.tag_void]; rfl
 simp [joinV,Pi.single_apply,mul_ite,stake,V']
private lemma rootPay : Metered P D (meterC P o) h (spineBudget P Γ):=by
  by_cases t:o∈D; swap
  · refine (Metered.of_cast (surplusM P Γ D' hc D o t)).related ?_; intro i v; unfold meterC AnalyticBridge.VerifiedReset.heads oV; change moldV n (petF o i.1)=moldV n (masked _ _ _ i.1); have he:Healthy P.threshold {o} i.1:= (by unfold Healthy; rw [show flags _ _=D from v.2]; simpa using t); rw [masked_eq _ _ _ _ he]; congr 1; unfold petF; simp_rw [real_inner_self_eq_norm_sq]
  have ht:0≤ spineBudget P Γ:= mul_nonneg (by positivity) (mint_p _ _ (mul_nonneg hc (spoke P o).nonneg)); refine (Metered.mono Metered.vacant ht).related ?_; intro i v; change 0= moldV n _; unfold AnalyticBridge.VerifiedReset.heads; rw [masked_ne, map_zero]; intro he; rw [Healthy,show flags P.threshold i.1=D from v.2] at he; exact Finset.disjoint_left.mp he (mem_singleton_self _) t -- tune view
include p D' DA hL hn hv hw hp hc ha
lemma toeV : ∃ C':ℝ,0≤ C'∧∀ D:Support M,Metered P D (oV (moldV n ∘ kinetic R q P)) h C':=by
  obtain ⟨h1,h11,h12,y1⟩:= thirst P R p A 1 DA ha hw hp hn hv 0; obtain ⟨h2,h21,h22,y2⟩:= crown_V P R p A 1 DA ha hw hp hn hv 0; obtain ⟨Z,u,i1,k1,o1⟩:=Λro P R p Γ 1 D' hc hw hp (Classical.arbitrary (Ids n)) hv hL
  let T:=Classical.arbitrary (Ids n); obtain ⟨c1,v1⟩:= budget_E P _ h1 hv; obtain ⟨c2,v2⟩:= budget_E P _ h2 hv
  have hN(D:Support M):∃ C',Metered P D (oV (moldV n ∘ kinetic R q P)) h C':=by
    let K(D':Support (More n))(a:ℝ):= Metered P D' (oV (moldV n ∘ kinetic R q P)) h a
    let H:= Metered.pile univ (meterC P) (fun _i=>spineBudget P Γ) (fun i _=> rootPay P Γ D' hc D i (h:=h));
    let L:= (H.link (project_thr P D (Beau.ΘK T P R q 1) Z u)).diff ((v1 D).link (v2 D)); refine ⟨_,L.related fun i v=> ?_⟩; rw [Pi.sub_apply,Pi.add_apply,Finset.sum_apply,Pi.add_apply]; let U:=i.1; have hU:Rue.FleetS P.threshold U:=v.1
    have H₁ : HasSum (fun x:Lane n=> Vow.march P (χx P R x) (oV (ham x P q R 1)) i) (moldV n (layer (fade R q P 1) U)):=by
        simp_rw [psips P R i hw _ 1 hU]; apply (moldV n).hasSum; have he:= fade_sum (n:=M) p P 1; rw [layer_total _ U he]; exact (stack_series _ _ he).hasSum
    have H₂: HasSum (fun x:Reign n=> Vow.march P (ωx P R x) (oV (gustH x P q R 1)) i) (moldV n (layer (upperFade R P 0 1) U)):=by
        simp_rw [pTime P R p i hw _ 1 hU]; apply (moldV n).hasSum; let he:= high_fade_sum (n:=More n) p P 0 1; rw [layer_total _ U he]; exact (stack_series _ _ he).hasSum
    rw [show fuelV P (Beau.ΘK T P R q 1) _= _ from (o1 i hU).unique (Taxi.toast P R p i T hc D' hw hp 1),show oV (exponentL P (lite_b n P R q 1)) i= _ from (y1 i).unique H₁,show oV (exponentL P (lit_P n P R q 1)) i= _ from (y2 i).unique H₂,show (∑ j,meterC P j i)= _ from (map_sum (moldV n) (fun j=>AnalyticBridge.VerifiedReset.heads P j U) _).symm,←map_add,←map_add,←map_sub]; apply congrArg (moldV n); have hr:= path_split p hp hw 0 1 U; rw [zero_add,one_mul,one_mul,zero_mul,zero_add] at hr; linarith only [hr]
  choose Cg hg using hN; let t':= ∑ i:Support (More n),Cg i; have hs(i):0 ≤ Cg i:= (hg i).holds (zero_le_one.trans hv); exact ⟨t',sum_nonneg (fun i _=>hs i),fun D=>(hg D).mono (single_le_sum (fun i _=>hs i) (mem_univ _))⟩
end YM.CF.Fixed.Voltage
