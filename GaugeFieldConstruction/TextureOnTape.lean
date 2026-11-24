import GaugeFieldConstruction.EqualTrialAssembly
/-! # Determining-theory valuations (postselection) on the β schedules of P1 (even and column paths). -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 7500
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
open Lamour.Bridge.Celeste
open Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn
open Regis.Head Regis.Head.Brecht
namespace Spine
open Aria Casting Six
open CF.Velvet CF.Pannier.Chancel Pitching.Focus
open YM.CF.Oath.BellPrice CF.Fief
open Oath
open Papal AUbard
open Papal FrameP Yoke.Promena WorldJ Frugal CF.Scroll MirrorCost
open Py Yoke.Promena
open CF.Neon CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart
open CF.TableF CF.TableF.Lenten CF.XGarden CF.XGarden.Shield
open WorldJ
open scoped YM.CF.Mew
open Pitching.Focus.CoeffArc TableF TableF.Lenten TableF.Lenten.Layout TableF.Lenten.Layout.Fren
open Ing Ing.Ivey CF.XGarden.MastTin
open CF.Pastry CF.Hive
open CF.Scroll
open RosterJ BoonsθJ SignetS Patrons ChSigFe
open CF.XGarden.MastTin.ArtCart
open SpaΘ
open Fock.Flux
open Papal
open Yoke SelectionAnalysis
open Oath.BellPrice
open GaugeFieldConstruction.Phys
open Fock
open GaugeFieldConstruction
open Fathom Ember
open Calibration.Floor Calibration

open Ember.Volumetric Ember.Volumetric.FirstPackMars Mavera
open Shower
open Calibration Calibration.Floor
attribute [local instance] iG iF iX iU iT2 iW2 iV iS
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick YM.GaugeFieldConstruction.Cauchy
open SelectionAnalysis
open CF.Levier CF.Spire
open Fathom Ember Hulse Points Fathom.Salam Fathom.Palace
namespace ContinuumConstruction
-- Data telescope. Naming concordance through the flagship API (QFT: E to Story,
-- L & G to continuity, calendars to labels and paths).
variable
  {nLeaf : ℕ}
  {process : Spine}
  {scale : process.Register}
  {production : YardμN process CostUpVU PolRun PriceArtVU nLeaf}
  {growth : InterR}
  {roles : ConsoleθN production ΓmotVU 0 growth ΓstageVU}
  {axes : Axis → GaugeFieldConstruction.Empire.Across}
  {comparison : Sheds roles.Crew_N axes}
  {approvals : Supplies comparison}
  {stress : Ticket roles.Gamma_N approvals}
  {vacuum : process.Spectrum0 3}
  {costAnalysis : process.Ellis 3 vacuum}
  {c : ℕ → ℕ}
  {collars : ℕ→ℕ}
  {layers : NSF.Boundary.Waves (roles.RadianceVU stress)}
  {response : NSF.Boundary.Surface (roles.RadianceVU stress)}
  {continued : NSF.Boundary.Surface.Aurora response NSF.LD.drapeL}
  {model : roles.GlowVU stress vacuum (le_refl _) layers response}
  {screens : process.Poll 3}
variable (Certificate : Assembled (scale:=scale) (costAnalysis:=costAnalysis) (c:=c) (collars:=collars)
   (continued:=continued) (model:=model) (screens:=screens))
open ConsoleθN
open NSF.Boundary
open YM.Boundary (Test4 Joint)
open GaugeFieldConstruction.Invoice.curvΝ
open Stage Stage.Cell
open Glaze CF.XGarden.MastTin.ArtCart.BluffV CF.XGarden.MastTin.ArtCart.BluffV.Fables
open MacroGrid

open Reconstruction
open NSF.Work.C20
namespace SecondSeason
variable {τ:ℕ}{β ν:ℕ→ℝ}(hc:TemperListSt process β scale τ ν)
-- Main read primitive. Primary and Column converse
noncomputable def DoorInSt (β:ℕ→ℝ)(P:Spine)(c:P.Poll 3)(i j k s:ℕ)(L:List (MeterQueryVU P)):ℂ :=
   panelCost P β j k (TopCurrencyVU P s L ++ PollavuVU P 3 c i) / panelCost P β j k (PollavuVU P 3 c i)
-- real questions. Venue budgets caller.Product.H. PinTape stores actual query support at ANY regulator etc.
abbrev CapQuerySt (U:Set E4): Set Vantage := (WithLp.toLp 2) ⁻¹' U
lemma entersCapSt {n:ℕ}(U:Set E4)(F:Fin n→ΧiMars)(G:Fin n→SampleDose)(e:IsOpen U)(p:∀ i,(G i).Normalized)(v:SponVU n G⊆ RibΛL U n): ∀ᶠ s in atTop, roles.TerraRateVU n F G s∈ treasuryVU s (CapQuerySt U):=by
 have hw:IsOpen (CapQuerySt U):=e.preimage (by fun_prop)
 choose x hx using fun i:Fin n=> dose_visible _ (p i)
 have hs(i:Fin n): tsupport (G i).val ⊆ CapQuerySt U:=by
   intro y h; let z:=points fun j=> WithLp.toLp 2 (if i=j then y else x j)
   have ht:z∈ SponVU n G:=by
     intro j; change (if i=j then y else x j)∈tsupport (G j).val; by_cases t:i=j; · simpa [t] using (t ▸ h : y∈tsupport (G j).val)
     simpa [t] using hx j
   have ht':z∈ HeldΛL U n:=(v ht).1
   change WithLp.toLp 2 y∈U
   have hw:=Set.mem_iInter.mp ht' i; change WithLp.toLp 2 (if i=i then y else x i)∈U at hw; simpa only [if_true] using hw
 filter_upwards[eventually_all.mpr (fun i:Fin n=> roles.landedVU (F i) (G i) (CapQuerySt U) hw (hs i))] with s h
 exact (treasuryVU _ _).prod_mem fun i _=> h i

abbrev QueryActualSt (U:Set Vantage) (F:ℕ→process.Test) (b:ℂ) : Prop :=
   ∀ ε:ℝ, 0<ε → ∀ᶠ s in atTop, ∃ A:Set Vantage,
           A⊆ U ∧ process.EndTapeSt s [(F s,A)] ∧ ∀ᶠ i in atTop,
     (∀ᶠ t in atTop,
       MarketwithSt process scale β (x:=vacuum) (c:=screens) i (process.diagonalᵢ (2*t)) (process.diagonalₖ (2*t)) s [(F s,A)] ε ∧ dist (DoorInSt β process screens i (process.diagonalᵢ (2*t)) (process.diagonalₖ (2*t)) s [(F s,A)]) b<ε) ∧
     (∀ᶠ t in atTop,∀ k,
       legacy process.run (process.period t) (process.circuitDepth (process.period t) k) →
       MarketwithSt process scale β (x:=vacuum) (c:=screens) i (process.period t) (process.circuitDepth (process.period t) k) s [(F s,A)] ε ∧
        dist (DoorInSt β process screens i (process.period t) (process.circuitDepth (process.period t) k) s [(F s,A)]) b<ε)
-- local hypothesis for determining among probes on this timetable. No reference-β or theory-value assumption or even MarketwithSt necessary as input. In a strong sense operational: probe estimates mine, projective/refine sufficiency (separate analytic continuation hypotheses still needed to infer the W). include the support and budget requirements just for the operator's first inscription (poll estim & other budgets can be called internally).
abbrev QueryCountSt (U:Set Vantage) (F:ℕ→process.Test) (b:ℂ) : Prop :=
   ∀ ε:ℝ, 0<ε → ∀ᶠ s in atTop, ∃ A:Set Vantage, A⊆ U ∧ process.EndTapeSt s [(F s,A)] ∧ ∃ᶠ i in atTop,
       (∃ᶠ t in atTop,dist (DoorInSt β process screens i (process.diagonalᵢ (2*t)) (process.diagonalₖ (2*t)) s [(F s,A)]) b<ε) -- even frequently on both tracks good enough for windows

lemma canAskHereSt {s:ℕ}{i j k:ℕ}{q:process.Test}{A:Set Vantage}{ε:ℝ} (t: MarketwithSt process scale β (x:=vacuum) (c:=screens) i j k s [(q,A)] ε):dist (DoorInSt β process screens i j k s [(q,A)]) (process.singleState 3 s vacuum q)<ε:=by
 simp only [DoorInSt]; simpa only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using t.cost
include Certificate hc
lemma queryAllSt (U:Set Vantage) (F:ℕ→process.Test)(b:ℂ)(v:∀ᶠ s in atTop,F s∈ treasuryVU s U) (Z:Tendsto (fun t:ℕ=>process.singleState 3 t vacuum (F t)) atTop (𝓝 b)): QueryActualSt (β:=β) (scale:=scale) (vacuum:=vacuum) (screens:=screens) U F b:=by
 let h:CampaignSt process scale (x:=vacuum) (c:=screens) β := (keepUnityStChoices Certificate hc).localize
 intro ε e
 filter_upwards [Metric.tendsto_nhds.mp Z _ (half_pos e),v] with s H t
 have hs: process.GoodTapeSt s [(F s,U)]:= by simp only [GoodTapeSt,List.forall_mem_singleton,List.pairwise_singleton,and_true]; exact t
 obtain ⟨T,w⟩:=h.before s [(F s,U)] hs
 let A:= T (F s,U); let L:List (MeterQueryVU process):= [(F s,A)]; have hp': A⊆ U ∧ IsCompact A:= by obtain ⟨e,k,Z⟩:= w.before_read.1 _ (List.mem_singleton_self _); exact ⟨e,k⟩
 have v': process.EndTapeSt s L:= ⟨w.before_read.2,fun x z=> by rcases List.mem_singleton.mp z with ⟨⟩; exact hp'.2⟩
 refine ⟨A,hp'.1,v',?_⟩
 filter_upwards[h.elected s L v' ε e,h.elected s L v' (ε/2) (half_pos e)] with i w p
 have ht (j k) (q: MarketwithSt process scale β (x:=vacuum) (c:=screens) i j k s L (ε/2)) : dist (DoorInSt β process screens i j k s [(F s,A)]) b<ε:= lt_of_le_of_lt (dist_triangle _ (process.singleState 3 s vacuum (F s)) _) (add_halves ε ▸ add_lt_add (canAskHereSt q) H)
 exact ⟨(w.1.and p.1).mono fun t W=> ⟨W.1,ht _ _ W.2⟩,(w.2.and p.2).mono fun t T k e=> ⟨T.1 k e,ht _ _ (T.2 k e)⟩⟩
lemma countToStateSt (U:Set Vantage)(F:ℕ→process.Test)(b:ℂ)(v:QueryCountSt (β:=β) (screens:=screens) U F b) : Tendsto (fun t:ℕ=>process.singleState 3 t vacuum (F t)) atTop (𝓝 b):=by
 let h:CampaignSt process scale (x:=vacuum) (c:=screens) β := (keepUnityStChoices Certificate hc).localize
 rw [Metric.tendsto_nhds]; intro ε e; let E:=half_pos e
 filter_upwards [v _ E] with s ht
 obtain ⟨A,-,t,z⟩:=ht
 obtain ⟨i,hx,Q⟩:=(z.and_eventually (h.elected s [(F s,A)] t (ε/2) E)).exists
 obtain ⟨r,e₁,e₂⟩:= (hx.and_eventually Q.1).exists
 refine lt_of_le_of_lt (dist_triangle _ _ _) (lt_of_lt_of_le (add_lt_add ?_ e₁) (add_halves ε).le); erw [dist_comm]; exact canAskHereSt e₂
omit Certificate hc
abbrev SeriesTakeSt (U:Set E4)(Z:CloudsL):Prop:=∀ (n:ℕ)(F:Fin n→ΧiMars)(G:Fin n→SampleDose), (∀ i,(G i).Normalized) → SponVU n G⊆ RibΛL U n → QueryCountSt (β:=β) (screens:=screens) (CapQuerySt U) (fun s=> roles.TerraRateVU n F G s) (CarriageVU n F (ConjoinVU n G) Z)

lemma actual_seriesSt (U:Set Vantage) {F:ℕ→process.Test}{b:ℂ}(v: QueryActualSt (β:=β) (scale:=scale) (vacuum:=vacuum) (screens:=screens) U F b) : QueryCountSt (β:=β) (screens:=screens) U F b := by
 intro ε e; filter_upwards [v ε e] with s h; obtain ⟨A,v,t,h⟩:=h
 exact ⟨A,v,t,(h.mono fun i q=> (q.1.mono fun k t=>t.2).frequently).frequently⟩

structure DeterminesSeasonSt (hc:TemperListSt process β scale τ ν) :Prop where
 read (U:Set E4) (u:IsOpen U) (g:U.Nonempty) (n:ℕ)(F:Fin n→ΧiMars)(G:Fin n→SampleDose) (p:∀ i,(G i).Normalized) (h:SponVU n G⊆ RibΛL U n): QueryActualSt (β:=β) (scale:=scale) (vacuum:=vacuum) (screens:=screens) (CapQuerySt U) (fun s=>roles.TerraRateVU n F G s) (CarriageVU n F (ConjoinVU n G) (roles.χVX stress vacuum))
 observes (U:Set E4) (u:IsOpen U) (g:U.Nonempty) : SeriesTakeSt (β:=β) (roles:=roles) (screens:=screens) U (roles.χVX stress vacuum)
 sufficesHere(U:Set E4)(h:IsOpen U)(g:U.Nonempty)(B:CloudsL)(vB:SurfCheckL B)(Y:NSF.Boundary.Surface (roles.RadianceVU stress)) (J:NSF.Boundary.Waves (roles.RadianceVU stress))(Q:Y.Aurora NSF.LD.drapeL) (i:Q.FullBody J)(x:J.Region (SurfRimL B))(z:J.NonTangentialFree Y)(b:SeriesTakeSt (β:=β) (roles:=roles) (screens:=screens) U B) : Y=response
include Certificate hc
lemma feeSeriesSt (U:Set E4) (u:IsOpen U) (g:U.Nonempty) {n:ℕ}(F:Fin n→ΧiMars) (G:Fin n→SampleDose) (p:∀ i,(G i).Normalized) (h:SponVU n G⊆ RibΛL U n):
 QueryActualSt (β:=β) (scale:=scale) (vacuum:=vacuum) (screens:=screens) (CapQuerySt U) (fun s=>roles.TerraRateVU n F G s) (CarriageVU n F (ConjoinVU n G) (roles.χVX stress vacuum)):=by
 refine queryAllSt Certificate hc _ _ _ (entersCapSt U F G u p h) (((realized Certificate).observed.2 U u g).1 n F G p h)

lemma perhapsSeasonSt: DeterminesSeasonSt (roles:=roles) (vacuum:=vacuum) (stress:=stress) (response:=response) (screens:=screens) hc:=by
 refine ⟨fun U u g n F G p h=> feeSeriesSt Certificate hc U u g F G p h,fun U u g n F G p h=> actual_seriesSt _ (feeSeriesSt Certificate hc U u g F G p h),fun U h g B hB Y J Q i x z b=> ((realized Certificate).observed.2 U h g).2 B hB Y J Q i x z fun n F G p t=>?_ ⟩
 exact countToStateSt Certificate hc _ _ _ (b _ F G p t)
#print axioms perhapsSeasonSt
open Vale Reed Dial Pastry AcrossLands Thera Paige
omit Certificate hc
variable (process) (m:Side) (k:ℕ)
local notation "τm" => Vale.mesh m process.par.R.L k
local notation "NΜ" => Scree.mid (τm) process.par.block
-- same conventions on actual Physics Govt m at cutoff k
noncomputable abbrev FirmSt (u:Pane (NΜ)) := Lat.frame SU.matter (Cube.links u) (anticut (NΜ))
noncomputable abbrev OccupantSt (u:Pane (NΜ)):= spar process.par.K.j babyM u
noncomputable abbrev FockketSt (u:Pane (NΜ)):= changeM (m:=Vale.mesh m process.par.R.L k) process.par.U u babyM
structure FullAmplitudeSt (β:ℕ→ℝ) (h: process.FrontalAccessSt m k τ) : Prop where
   funded : VolumeInk process.par.K process.par.U (process.run.meter.a k) (β k) (mesh m process.par.R.L k)
   letters (x: Site (NΜ)) (a:SpinIdx)(t:Fin 3)(i:SU.Ten⊕ SU.F): (think (Tset (NΜ))).term ((x,a),t,i)= if a∈plusHalf then put ((x,a),t,i) else -takeF ((x,a),t,i)
   spectral_form (u:Pane (NΜ)) (p:flags (process.run.meter.a k).threshold u=∅): ∃ v L,(FirmSt process m k u).H=spectral v L ∧ OccupantSt process m k u=portW (Tulip.helix _).symm (spectral v (occ L))
   grassmann (u:Pane (NΜ))(p:flags (process.run.meter.a k).threshold u=∅): ∃ (v:UNI (Single (NΜ)))(S:Finset (Single (NΜ))), OccupantSt process m k u=twist v (cutM S) ∧ ∃ c:ℂ, ‖c‖=1 ∧ ∀ z:FC (Single (NΜ)), Reed.Plain z → c*Reed.spell (Reed.syms (Tset (NΜ))) v.val (Tset (NΜ)) S z= inner ℂ (mateK (NΜ)) (acts ((Reed.think (Tset (NΜ))).eval z) (FockketSt process m k u))
variable {process}
private lemma grass_peSt (v:UNI (Single (NΜ))) (S:Finset (Single (NΜ))) (u: Pane (NΜ)) (y₀:Sea (OccupantSt process m k u) (FockketSt process m k u)) (p:OccupantSt process m k u=twist v (cutM S)) : ∃ c:ℂ, ‖c‖=1 ∧ ∀ z:FC (Single (NΜ)), Reed.Plain z → c*Reed.spell (Reed.syms (Tset (NΜ))) v.val (Tset (NΜ)) S z= inner ℂ (mateK (NΜ)) (acts ((Reed.think (Tset (NΜ))).eval z) (FockketSt process m k u)):=by
 let s:=Tset (NΜ); let t:= FockketSt process m k u; let T:= Fock.wedge v.val S; let c:= inner ℂ T t
 let w:= mateK (NΜ); let α:= basisKet s; let d:= inner ℂ α w
 have hz : Sea (cutM s) w:= Spire.touchP (NΜ) ▸ Dial.tickB (NΜ)
 have hd:w=d • α:=by nth_rw 1 [← hz.1]; rw [cutLine, cut_oneAct]; unfold d α; rw [basis_inner]
 have y:t = c • T:=by
    have hT :Sea (OccupantSt process m k u) t:=y₀
    nth_rw 1 [← hT.1]; rw [p]; exact act_twistLine ..
 have l : ‖c‖=1:= by have he:‖t‖=1:=y₀.2; rw [y,norm_smul,show ‖T‖=1 from wedge_norm ..,mul_one] at he; exact he
 have h : ‖d‖=1:= by have he:=hz.2; rw [hd,norm_smul,show ‖α‖=1 from (by simp [α,basisKet]),mul_one] at he; exact he
 refine ⟨star d*c,by rw [norm_mul,norm_star,h,l,one_mul],fun x hx=>?_⟩
 rw [Reed.moment _ _ _ _ hx]; change _=inner ℂ w (acts _ t); rw [hd,y,map_smul,inner_smul_right,inner_smul_left]; change _=c*(star d* _); ring
include hc
lemma birthsOn_tapeSt (h:process.FrontalAccessSt m k τ) : FullAmplitudeSt process m k β h:=by
 let Z:= process.independentCash _ hc.calendar k m h
 refine ⟨Z,fun x a t i=> ?_,fun u q=> ?_,fun u q=>?_⟩
 · change (if _ then _ else _)=_; simp only [Window.mem_Tset]
 · obtain ⟨hp0,P,r⟩:=Z.aptitude u q
   obtain ⟨v,L,e⟩:= spectral_exists _ ((FirmSt process m k u).selfadjoint)
   have hp': Safe (FirmSt process m k u).H:=hp0; refine ⟨v,L,e,P.trans ?_⟩
   have hx:projector (FirmSt process m k u).H=spectral v (occ L):=by rw [e]; exact projector_spectral (h:=e ▸ hp')
   exact congr_arg _ hx
 obtain ⟨hp,g,r,o⟩:=Z.aptitude u q
 have ht: IsStarProjection (OccupantSt process m k u):=by unfold OccupantSt; rw [g]; exact (Safe.projection hp).map (love (NΜ))
 obtain ⟨v,S,V⟩:=spot_projection _ ht; exact ⟨v,S,V,grass_peSt m k v S u r V⟩
#print axioms birthsOn_tapeSt
end SecondSeason
end ContinuumConstruction
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
