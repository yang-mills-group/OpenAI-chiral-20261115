import SatinFixedContrastNovember4
import SatinThinReproofLimit
import SatinThinReproofLabels
/-!
# Obstruction test at the very interaction centers / actual data

The relevant center-motion questions: NOT about continuing general compact tests as
some other class of fields on the state. Use the same spatial translation and just
one of the interior family diagonals! Prove a local continuation price is impossible
on these fields with corresponding same or point-sized (even some larger) Mink
footprints, at **any sufficiently late** width; use true label and any candidate
with the specified positive time law with matching hypothesis on this translation
and **any identification offset ≥ 0**. And show the obstruction would apply at limit
with ANY remaining positive heat offset under those locality and identification
requirements. Or no offset but invoke that actual cost with further padding as
specified. Again look at our exact prices at this ruler, see the estimates. Never assuming
cone or claiming any Mink-local fields even WITHOUT remaining positive allowance.

See `SatinThinFieldInteraction` for the main positive result (real Euclidean, not these
attempted Wick ones). Use these to equip that experiment with actual obstruction TESTS.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 330000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
namespace Spine
open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set
open YM.SatinMacro YM.SatinEdge
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "Ω"=> P.heaven 3 ξ
local notation "ω"=> P.colorZero 3 ξ
local notation "S"=> P.seasons 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "E!"=> (S).E
local notation "U!"=> (S).U
local notation "κ"=> (S).unit
local notation "ℒ"=> Lead.Clan
variable (A:ℕ→P.Apron)(c r n:ℕ→ℕ)(w:Lead.Clan→ Prism)(V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(g h:ℕ)
local notation "W"=> P.soldTrumpet A c r n w
variable (T:P.HandleWith x c r A n)
local notation "B[" z "," i "]"=> P.sold_birth x A c r n w z i T
variable (F U:SampleDose)(s k:ℕ)(K:P.Register)
local notation "L"=> P.FullPrismLab x A c r n w V g h T 1 F U reviewEarlierBox reviewLaterBox s k K
-- use explicit var assumptions when local notations in binders
local notation "σ" z:max p:max => P.limitStripe x V w z (p:Vantage)
local notation "ξ'" z:max p:max i:max => P.orderedStripe x (W z (i:ℕ)) p
-- threshold i large. Use *that very same z mark* as used on the supported smears.
-- no need identity label / no requirement of arbitrary Mink footprints. ∀ |t|≤1
-- automatically true strict-separation even if WE ASSIGN those widths in Mink space.
-- not taking that like a Euclidean prescription! Testing its failure here.
structure CheckedMarkRefusal (z:Lead.Clan)(p:Vantage)(i:ℕ) : Prop extends P.MarkRefusal x (W z i) p B[z,i] where
 price_ne : (ξ' z p i) (p 3) ≠ 0
 vertical : ∀ j:Axis, (W z i).realWidth P j+(W z i).realWidth P j<p j
 outside : P.apronBudget (W z i)⊆ compassBudget ∧ P.apronBudget ((W z i).kiss P 3)⊆ compassBudget
 actual (t:ℝ)(v:|t|≤1): Apart (P.apronBudget ((W z i).kiss P 3)) (there (sameTravel p t) (P.apronBudget (W z i)))
lemma equal_cover (Y:P.Apron): P.apronBudget (Y.kiss P 3) = P.apronBudget Y := rfl
set_option maxHeartbeats 600000 in
lemma bookedOne (J:P.Ellis 3 x)(D:P.ThinArmada x A c r n w T V g h)(p:Vantage)(pt:∀ j:Axis,2 < p j) (z:ℒ)(i:ℕ)(hi:∀ j:Axis,(W z i).realWidth P j+(W z i).realWidth P j<p j)(e:(ξ' z p i) (p 3)≠0)(a:P.apronBudget (W z i)⊆ compassBudget) : P.CheckedMarkRefusal x A c r n w T z p i:= by
 let u:=p 3
 let Y:=W z i
 have hf : P.apronBudget (Y.kiss P 3) ⊆ compassBudget:= by rw [P.equal_cover Y]; exact a
 have hy:= (D.keep z i).2
 have hp : HasPadding (S) (π' (P.thinOrigin x Y B[z,i])):= by
    have hp(S':OS.Semigroup G timeAxis)(p:G)(a:ℝ≥0)(v:0<a)(f:∃ u:G,p=S'.E a u): HasPadding S' p:= ⟨a,v,f⟩
    apply hp _ _ _ (P.burst_p (c (n i)))
    obtain ⟨t,f⟩:= hy.2
    refine ⟨π' t,(congrArg (π') f).trans (P.bankHeat 3 ξ _ t)⟩
 exact {
    toMarkRefusal:= P.mark_refuses x Y p B[z,i] J hy.1.1 hp u (hi 3) e
    price_ne:= e
    vertical:= hi
    outside:= ⟨a,hf⟩
    actual:= fun t v y p' w hz=> compass_apart p (pt 0) v y (hf p') w (Set.image_mono a hz)
 }
lemma bookedSales (J:P.Ellis 3 x)(D:P.ThinArmada x A c r n w T V g h)(p:Vantage)(pt:∀ j:Axis,2 < p j) (z:ℒ)(v: (σ z p) (p 3)≠0) : ∀ᶠ i:ℕ in atTop,P.CheckedMarkRefusal x A c r n w T z p i:=by
 let u:=p 3; have hz:0 < u:= lt_trans zero_lt_two (pt _)
 have he:Tendsto (fun i=> (ξ' z p i) u) atTop (𝓝 ((σ z p) u)):= by
    have h:= P.illuminate_globe x A c r n w V g h T D J z z (p:=(0:Vantage)) (q:= rollCall p u) (show 0<rollCall p u 3 by rw [roll_price_time]; exact hz)
    rw [sub_zero] at h; exact h
 have hm := he.eventually (IsOpen.mem_nhds (isOpen_ne (x:=0)) (show (σ z p) u≠0 from v))
 have hs(j:Axis): ∀ᶠ i in atTop,(W z i).realWidth P j+(W z i).realWidth P j<p j:= ((D.slender z j).add (D.slender z j)).eventually (gt_mem_nhds (by simpa only [zero_add] using zero_lt_two.trans (pt j)))
 filter_upwards [eventually_all.mpr hs, hm, P.compass_width (W z) (D.slender z)] with i hi e a
 exact P.bookedOne x A c r n w V g h T J D p pt z i hi e a
structure UsesReproof (p q:Vantage) : Prop extends P.FullPrismLab x A c r n w V g h T 1 F U reviewEarlierBox reviewLaterBox s k K where
 scheduled : ∃ i:ℕ, F=slider p (chosen p i) ∧ U=slider q (chosen q i)
 spatial : ∀ i: Axis, 2 < (q-p) i
 uses (t:ℝ) (u:|t|≤1) : sameTravel (q-p) t ∈ Mink.spacelike ∧ Apart compassBudget (there (sameTravel (q-p) t) compassBudget)
 prices (z:ℒ) : (σ z (q-p)) ((q-p) 3) ≠ 0
 -- all sufficiently late markers *prior* to limit, including their width-retaining real labels
 still : ∀ᶠ i:ℕ in atTop,∀ z:ℒ,P.CheckedMarkRefusal x A c r n w T z (q-p) i
 -- at limit, any nonzero offset. Also a test with time smoothed B (per type), no offset
 horizon (z:ℒ) : P.PriceLimitRefuses x V w z (q-p)

lemma probe_rejected (J:P.Ellis 3 x)(X:L) : ∃ p∈ reviewEarlierBox.invites,∃ q∈ reviewLaterBox.invites,P.UsesReproof x A c r n w V g h T F U s k K p q:=by
 obtain ⟨u,x',v,y',i,i₀,i₁,h₀,_⟩:= X.keeps.centers
 let p:=v-u
 have he(j:Axis):2<p j:= by linarith only [show u j + 2 < v j from thin_separation u v x' y' j,show p j=v j-u j from rfl]
 have hc(z:ℒ): (σ z p) (p 3)≠0:= by rw [limitStripe,rollCall,Function.update_eq_self]; exact h₀.2 z
 let G':= X.armada
 exact ⟨u,x',v,y', {
   toFullPrismLab:= X
   scheduled:= ⟨i,i₀,i₁⟩
   spatial:= he
   prices:= hc
   uses:= fun t v'=> ⟨compass_detect p (he 0) v',compass_apart p (he 0) v'⟩
   still:=eventually_all.mpr fun z=> P.bookedSales x A c r n w V g h T J G' p he z (hc z)
   horizon:= fun z => P.limit_refuses x V w z p (G'.energy z).2.1 (fun i u=>((G'.energy z).2.2 i u).2.1) (zero_lt_two.trans (he 3)) (hc z) }⟩
end Spine
open Spine
open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six
-- NO HYPOTHESES. On same P,K,x even for MARKREFUSAL.
lemma thin_field_tested :
    let Ω':Supplier := fun _ _ _ _ _ _ _ _ _ _ _ _ => 0
    ∃ (P:Spine) (K:P.Register), uniform P K Ω' 1 1 ∧
    ∃ (x:P.Spectrum0 3)(R:P.Ellis 3 x)(c r:ℕ→ℕ), id ≤ r ∧ Experiment P K c r x R ∧
    ∃ (f s:ℕ)(v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(u:StrictMono v)(q:ℕ → Coalition) (V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), ∃ (n:ℕ→ℕ)(X:P.HandleWith x c r (P.cinema x f s v a q u) n), (∀ p:Lead.Clan→ SatinJets.Prism, ThinArmada P x (P.cinema x f s v a q u) c r n p X V f s) ∧ ∀ᶠ i:ℕ in atTop, ∃ (F G:SampleDose)(p:Lead.Clan→ SatinJets.Prism), ∃ A'∈reviewEarlierBox.invites, ∃ B'∈ reviewLaterBox.invites,P.UsesReproof x (P.cinema x f s v a q u) c r n p V f s X F G (c i) (r i) K A' B' := by
 intro u
 obtain ⟨P,K,e,x,R,c,r,h,u,v,a,f,o,w,q,V,n,X,p,l⟩:= actual_separated_thin_field_interaction
 exact ⟨P,K,e,x,R,c,r,h,u,v,a,f,o,w,q,V,n,X,p,l.mono fun i x' =>by
    obtain ⟨Z,M,p,t⟩:=x'
    exact ⟨Z,M,p,P.probe_rejected x _ c r n _ V _ _ _ _ _ _ _ K R t⟩⟩
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.thin_field_tested
#check @YM.CF.Buffered.Afterglow.Tower.VacuumSelection.thin_field_tested
