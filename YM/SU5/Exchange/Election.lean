import SU5SatinFieldRegistrationsNovember7

/-!
# A simultaneous election.

Following the constructions in Heave/Corona, Affine/SolarShop and
Velour/Tassel/Plan. For applying further costs forced on particular
x, leave the theorem also parameterized by pre-election data and by
conditions holding a.e. Not a spacetime locality or interaction theorem.
-/
set_option autoImplicit false
set_option maxHeartbeats 380000
set_option quotPrecheck false
noncomputable section
set_option synthInstance.maxSize 28000
set_option maxRecDepth 2000

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel

open SatinNucleus Six

namespace Spine
variable (P : Spine) (R : P.Register)
variable {X₀ : Supplier} {t B C : ℝ} (paid : uniform P R X₀ t B)
    (night : P.NightCop)

include paid night in
/-- Combine the requirements at *both* choices of schedules (seam sizes and
pose) and select the base Experiment as usual on ground measure. -/
theorem heavySilkStage (z : ℕ → ℕ) :
    ∃ c r : ℕ → ℕ, z ≤ r ∧ P.Heavier c r ∧ P.SilkVelour c r ∧
      ∀ᵐ x ∂ P.pillars 3, ∃ J : P.Ellis 3 x, Experiment P R c r x J := by
  choose a ha using fun i =>
    eventually_atTop.1 (P.feather paid night (P.macroStep_pos i))
  choose b hb using fun i =>
    eventually_atTop.1 (P.all_afford paid night _ (P.macroStep_pos i) _ (P.burst_p i))
  obtain ⟨r, q, l, p⟩ :=
    Prototype.outing paid keyV keyV_positive (fun i => max (z i) (max (a i) (b i)))
  have u (i : ℕ) : max (a i) (b i) ≤ r i := (le_max_right ..).trans (q i)
  have hr (i : ℕ) :
      ∀ᶠ s : ℕ in atTop,
        (P.Lightweight (P.macroStep i) (P.burst i) s (r i)) ∧
        (∃ k : ℕ, bell (timeMesh P.par) s k ≤ P.macroStep i ∧
          P.FlickTone (r i) k s (P.macroStep i)) := by
    obtain ⟨k, hk⟩ := (ha i _ ((le_max_left ..).trans (u i))).exists
    refine (hb i _ ((le_max_right ..).trans (u i))).and ?_
    filter_upwards [hk, (P.silkSpan k).eventually (ge_mem_nhds (P.macroStep_pos i))]
      with s hs s'
    exact ⟨k, s', hs⟩
  obtain ⟨c, m, mc⟩ :=
    strictCadence (fun i => (eventually_ge_atTop (l i)).and (hr i))
  obtain ⟨j, _, w⟩ := p c m fun i => (mc i).1
  refine ⟨c, r, fun i => (le_max_left ..).trans (q i),
    fun i => (mc i).2.1, fun i => (mc i).2.2, ?_⟩
  filter_upwards [P.many_stars 3 R, w] with x h wx
  obtain ⟨J⟩ := P.ellisP 3 x R
  let h' := P.parting 3 x R (P.homes_weather R 3 (P.all_phases 3 x h))
  exact ⟨J, j, wx, h', Spine.final_issues R J h', P.footway _ J R h'⟩

private lemma hefty_align(P:Spine) (f:ℕ) : Spine.twiceT (P.baseRoot f) 3= Spine.twiceT (P.plateau f) 3:=by unfold twiceT; simp only [nodeC, Pi.add_apply,Pi.smul_apply]
variable {A : ℝ} {Y : Supplier} {L M : ℝ} (e : uniform P R Y L M)
  (h0 : P.NightCop) (yK : Odd P.par.R.L.val)
  (H : ∀ᶠ s : ℕ in atTop, ∀ᶠ i : ℕ in atTop, ∀ k : ℕ,
    (P.run.voyage i).kick ≤ k → s ≤ P.run.uv k → Yoke.ShelterCost C P.run s i k)
  (a : Chronicle P.run A)

include e h0 H a yK
/-- Extra conditions on the *character* can still be forced provided they hold
 a.e. on `P`. Same almost-everywhere scope as Corona.heavier_century. -/
theorem electedTogether (z : ℕ → ℕ) (d : ℝ) (w : 0 < d) :
    ∃ c r : ℕ → ℕ, z ≤ r ∧ P.Heavier c r ∧ P.SilkVelour c r ∧
      ∃ b > (0:ℝ), ∀ᶠ s : ℕ in atTop,
       P.flightCap (P.pointEra s)< d ∧ ∀ F:P.Spectrum0 3→ Prop,(∀ᵐ x∂ P.pillars 3,F x) →
         ∃ (x:P.Spectrum0 3)(R':P.Ellis 3 x),F x ∧ CruisePreparation P A C b R c r (P.pointEra s) s x R' ∧
         ∃ (v:ℕ→ℕ)(a:ℕ→(ℕ×ℕ)→ℝ),ScoutAnthem P x A C (P.pointEra s) s b v a ∧
            (∀ j l, AtGlassRate P x j (P.pointEra s) s l v a) := by
 obtain ⟨c,r,h,Θ,hV,ρ⟩ := P.heavySilkStage R e h0 z
 let oldK := R
 obtain ⟨b,β,_,t₀⟩:= SatinJets.common_margin (max7+min7+1) min7 min_positive
 refine ⟨c,r,h,Θ,hV,b,β,?_⟩
 let A₀:=2*lensValue A; have h8:Tendsto (fun s:ℕ=>A₀ * P.repeatLoss s) atTop (𝓝 0):=by simpa only [mul_zero] using P.era_complete.const_mul A₀
 let νp:= P.pointEra; let δv:=P.future_payment
 filter_upwards [P.payment_late,δv.eventually (P.flight_soon.eventually (gt_mem_nhds w)), P.ready_granule (P.roomy), δv.eventually (P.offers_plans 3 1 zero_lt_one), δv.eventually (P.seat_many 3 1 zero_lt_one), δv.eventually (P.auditsCalendar H a), (P.lantern_go H).eventually (ge_mem_nhds (show 0< min7 /4 /4 from (by linarith only [min_positive]))), δv.eventually P.size_honors,P.reward_positive,h8.eventually (ge_mem_nhds (show 0<b/16 by positivity))] with s Hs w t δ n P0 G0 w0 W K0; let f:= νp s; have hp: f < s:= Hs.2.1
 refine ⟨w,fun F hf=>?_⟩
 let g(x: P.Spectrum0 3):Prop:= (∃ R:P.Ellis 3 x, Spine.Experiment P oldK c r x R) ∧ F x; have hz:∀ᵐ x∂ P.pillars 3,g x:= ρ.and hf
 have he:P.reached f s:= t
 have ht:Spine.twiceT (P.baseRoot f) 3 ≤ Yoke.scout P.par 1 f:= by rw [hefty_align]; exact n
 have hx':= δ.1 (P.baseRoot f) ht
 
 obtain ⟨x,⟨⟨R,h'⟩,κ'⟩,_, v,a,V,Wⱼ⟩:= P.third_winter h0 hx' hp (fun v w=>P0 v (hp.le.trans w)) G0 he w0.1 (W.2 f) K0 H g hz yK
 let Va:=V.cluster hp
 refine ⟨x,R,κ',⟨h',⟨he,hp,W.1,W.2 f⟩,Va,P.reliable_pp x he W.1 Va.price R t₀ β.le,?_⟩,v,a,V,Wⱼ⟩
 intro U V o t'; let q:Fin 3 → Bool:= fun _=>false; obtain ⟨p, e, _he, _inside, hcost⟩ := authorize q; filter_upwards [packs_within_rectangles (trans6 h') (Metric.ball p e) q hcost U V o t'] with i hi; obtain ⟨a, F, G, hF, hG, hR, hU, hV, _⟩ := hi.2; exact ⟨a, F, G, hF, hG, hU, hV, hR, P.reviewWardContrast oldK x _ _ a F G hR⟩
omit e h0 H a yK
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

set_option maxRecDepth 5000
set_option maxHeartbeats 1200000
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine
open _root_.YM.CF.Buffered.Afterglow.Hierarchy
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight
open FirstWindows FirstWindows.Chambers FirstWindows.LightBudget

open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set

open _root_.YM.SatinEdge.RealSheet Boundary Probe
open _root_.YM.SatinRegistration
open Regis.Head Regis.Head.Brecht
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
variable (P: Spine)(x:P.Spectrum0 3)(K:P.Register)(J:P.Ellis 3 x)(c r:ℕ→ℕ)
variable (g h:ℕ)(a:ℕ→(ℕ×ℕ)→ℝ)(v:ℕ→ℕ)
variable {A C b:ℝ}
include J
universe uΩ
/-- M8 camera with the full strong-star prices of Velour. -/
lemma sameCamera (s:P.NightCop)(L':Odd P.par.R.L.val)(d:∀ᶠ s:ℕ in atTop, treasury A C P s (s+1) (s+1))(hb:0<b)
    (p:CruisePreparation P A C b K c r g h x J)(S:ScoutAnthem P x A C g h b v a)(W:∀ j l, AtGlassRate P x j g h l v a) :
    ∃ (A:ℕ→P.Apron)(V:∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j)), GalaxyShow P x g h A V ∧ P.PoweredHeat x V ∧ (∀ i, PureGauge P.calibration (A i).F) ∧ P.Funding x A ∧ PlanetaryG.{uΩ} P A ∧ P.VelvetCup x A:=by
 -- Select width sequence AFTER specifying gauge station and experiment. subsidy clamp. StrictMono here on same regulator (not comparison across histories). Reuse ballot against actual attachment in `PoweredElection` proof.
 obtain ⟨ψ,q,t⟩:= (S.rides p.station.2.1).forks
 let v':= v ∘ ψ; let a':= a ∘ ψ; have hT:= S.move q; obtain ⟨d',u⟩:= hT.station
 let hj:StrictMono v':= u.fast; obtain ⟨k,Y,Z,ZV⟩:= P.velvet_radiated x v' hj a' g h K hT s p.station.2.1 L'
 let X:= P.cinema x g h v' a' k hj
 let hH:Radiates P x X Y:=Z; let V:GalaxyShow P x g h X Y:= ⟨hH,fun i=> P.pleading_b ..,fun i=> P.pleading_g ..,fun y w=> Spine.freemen P _ g h v' hj a' k Y hT p.station.2.1.le p.station.1 hb Z p.opera y w,fun j l k' u v a b t g p' => P.scenic_right x j J Z Z l k' t g (sub_pos.mpr p'),fun j l k u v a b t g p' => P.scenic_left x j J Z Z l k t g (sub_pos.mpr p')⟩
 refine ⟨X,Y,V,P.cinema_powers x _ _ v' a' hj k Y (fun j l=> ?_) V,(fun i=> P.cinema_pure ..),P.fiscal_camera x g h v' a' hj k s L' (hT.rides p.station.2.1) d t,P.planet_purchase K g h v' hj a' k x s L' (hT.rides p.station.2.1) t d, ZV⟩
 exact AtGlassRate.carries j (W j l) q


end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection

open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase
     MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound
     Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker
     ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy
     Tapestry Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open YM.Stationary (Gaia)
open CF.Onyx (riseX moor)
open Lamour.Bridge.Celeste.Morn

open CF.Velvet CF.Pannier.Chancel
open Spine Pitching.Focus
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel

open SatinNucleus Six
namespace Spine
open SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=>P.ColorHil 3 ξ
local notation "F"=>P.physicalEnergy 3 ξ
variable (c r:ℕ→ℕ)(Y:ℕ→ P.Apron) (n:ℕ→ℕ)
local notation "M" s:max d:max=> whenly (timeMesh P.par) s d

variable {K:P.Register}{J:P.Ellis 3 x}(T:P.Experiment K c r x J)
include T
lemma conjunctionSeam (h:P.Wafting c r) (S':SilkVelour P c r) : ∃ n:ℕ→ℕ, P.HandleWith x c r Y n ∧ VelvetHandle P c r Y x n ∧ ∀ x:P.Spectrum0 3, P.Guest x c r Y n:= by
 -- Reuse old seam bound on vacuum, now get operator estimates from StillFront.
 let w(i:ℕ):= (Y i).realWidth P 3
 let f(i:ℕ):= (Y i).engine P 3 (P.advocate 3 x 3)
 let A (i j:ℕ)(k:Lead.Clan): H:= f i ((F).E ((w i).toNNReal) (P.shard x k (c j) (r j)))
 let T' (i:ℕ)(k:Lead.Clan): H:= (purePrice k:ℂ) • f i (P.colorZero 3 ξ)
 let W(i j:ℕ):= ∀ k:Lead.Clan,‖A i j k-T' i k‖ ≤ P.macroStep i
 have hp(i:ℕ):∀ᶠ j:ℕ in atTop, W i j:= by
    apply eventually_all.mpr; intro k
    let v:=(w i).toNNReal; have hv:0<v:= Real.toNNReal_pos.mpr ((Y i).real_width_pos P 3)
    have he: Tendsto (fun j:ℕ=> A i j k) atTop (𝓝 (T' i k)):=by
       have he:Tendsto (fun j=> A i j k) atTop (𝓝 ((f i) ((purePrice k:ℂ) • P.colorZero 3 ξ))):=((f i).continuous.tendsto _).comp (thin_front_shard_tendsto k T (fun _=>v) (thin_compare_dew T hv _ (Eventually.of_forall fun _=>le_refl v)))
       rw [map_smul] at he; exact he
    exact ((tendsto_iff_norm_sub_tendsto_zero.1 he).eventually (ge_mem_nhds (P.macroStep_pos i)))
 let y(i):=(Y i).allowance P 3
 choose g' pg pG using fun i:ℕ=> P.fixed_cap_eng 3 (Y i)
 let V(i:ℕ):ℝ:= P.macroStep i/(1+g' i)
 obtain ⟨n,q,g⟩:= strictCadence (fun i => (T.launch.smaller.tendsto_atTop.eventually (eventually_ge_atTop (Y i).s)).and ((T.launch.eager.tendsto_atTop.eventually (eventually_gt_atTop P.calibration.ℓ)).and ((hp i).and ((P.SoftSupported c r Y x i S').and (h _ (show 0<V i from div_pos (P.macroStep_pos i) (by linarith only [pg i])) _ ((Y i).width_p P 3))))))
 refine ⟨n,⟨q,fun i=>(g i).1,fun i=>(g i).2.1,fun i k=> (g i).2.2.1 k⟩, (fun i=>(g i).2.2.2.1),fun t=>⟨fun i k=>( (g i).2.2.2.2 3 k).1.le,fun i k=>?_⟩⟩
 have ht:= ((g i).2.2.2.2 3 k).2 _ _ le_rfl le_rfl (P.advocate 3 t 3)
 change ‖P.printGaps 3 (P.advocate 3 t 3) k (c (n i)) (r (n i)) (y i) (y i)‖≤ P.macroStep i/(1+g' i) at ht
 change (1+‖(Y i).engine P 3 (P.advocate 3 t 3)‖)*_≤ _
 apply (mul_le_mul_of_nonneg_right (add_le_add_right (pG i (P.advocate 3 t 3)) (1:ℝ)) (norm_nonneg _)).trans; rw [mul_comm]; exact (le_div_iff₀ (show 0<1+g' i from by linarith only [pg i])).mp ht

end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
