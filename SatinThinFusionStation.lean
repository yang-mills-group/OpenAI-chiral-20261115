import SatinFixedContrastNovember4
import SatinThinFusionPlaybill
/-! # Seal the new G+M sensor. Credits apply to ALL strict-positive calendar times. -/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
set_option maxHeartbeats 500000
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
open MacroGrid SatinNucleus SatinJets
variable (P:Spine)(x:P.Spectrum0 3)
local notation "ξ"=> P.advocate 3 x 3
local notation "H"=> P.ColorHil 3 ξ
local notation "G"=> P.ManyF 3 ξ
local notation "S"=> P.physicalEnergy 3 ξ
local notation "Ε"=> P.seasons 3 ξ
local notation "π'"=> P.wealth 3 ξ
local notation "Z"=> Lead.Clan
variable (A:ℕ→P.Apron)(c r n:ℕ→ℕ)(w:Lead.Clan→ Prism)(z:Lead.Clan)(i:ℕ)
abbrev seasonTick (c n:ℕ→ℕ)(i:ℕ):= c (n i)
local notation "B[" i "]"=> P.stitchApron z (A i) (c (n i)) (r (n i))
-- Final stamps. At birth registration s=c(n(i)). Use as many as three cover motions
-- in each of the shifted fusion products (two internal to seam purchase, one for launching).
-- The baffle additionally differences in time in the stencil itself; see Trumpets.
def soldTrumpet : P.Apron:= P.aTuba (w z) (B[i])
local notation "W[" i "]"=> P.soldTrumpet A c r n w z i
variable (Y:P.HandleWith x c r A n)
include Y in
lemma sold_birth : P.birthF 3 (c (n i)) (W[i]).F:= P.plays_birth (w z) (B[i]) (P.stitch_clear z x c r A n Y i)
local notation "born" i:max=> P.sold_birth x A c r n w z i Y
private lemma heatedCash (L:Hilbert)(H₀:OS.Semigroup L 3)(V:Prism)(e:ℕ→ℝ≥0)(p:Tendsto e atTop (𝓝 0))(g:∀ i,0<e i)(f:ℝ→L)(A:ℕ→ℝ→L)(h:Positive H₀ f)
    (W:Operates (f:=atTop) H₀ f A)(t:ℝ)(τ:0<t): Tendsto (fun i=>H₀.E (e i) (prism_on H₀ V (e i) (A i t))) atTop (𝓝 (prism H₀ f V t)):= by
 let y:= prism H₀ f V t
 have hp:Tendsto (fun i=>H₀.E (e i) (prism_on H₀ V (e i) (A i t))) atTop (𝓝 (H₀.E 0 y)):=
    ((heat_both L 3 H₀).tendsto _).comp (p.prodMk_nhds (prism_limit H₀ f V h A W p (Eventually.of_forall g) τ))
 rw [H₀.eZero, ContinuousLinearMap.id_apply] at hp; exact hp
variable (V : ∀ j:Axis,List Axis→ℝ→ P.ColorHil j (P.advocate 3 x j))(g h:ℕ)
abbrev profilesH(t:ℝ):= prism (S) (P.route_before z x V) (w z) t
local notation "Λ[" z "]"=> P.profilesH x w z V
local notation "ΛR[" z "]"=> P.profilesZ x V w z
-- leave basis normalization unchanged (route_y)
structure ThinArmada : Prop where
 -- stored assumptions for all choices. (g,h gauge startup shelving, V all-axis gauge; used pure order)
 cinema : P.GalaxyShow x g h A V
 fusion : P.FusionFleet x c r A n Y V
 -- store tests for the final sewn series:
 sensor (z:Lead.Clan): ∀ i, P.Sensor (P.soldTrumpet A c r n w z i) z.2
 slender (z:Lead.Clan)(j:Axis) : Tendsto (fun i=> (P.soldTrumpet A c r n w z i).realWidth P j) atTop (𝓝 0)
 vacuum (z:Lead.Clan)(i:ℕ): P.singleState 3 (c (n i)) x (P.soldTrumpet A c r n w z i).F=0
 keep (z:Lead.Clan) (i:ℕ): let F:= P.thinOrigin x (P.soldTrumpet A c r n w z i) (P.sold_birth x A c r n w z i Y); projectionDark H (S) F ∧ projectionDark G (Ε) (π' F) ∧
      ∃ (y₀ : H), F=(S).E (P.burst (c (n i))) y₀
 energy (z:Lead.Clan) : Positive (S) (Λ[z]) ∧ Positive (Ε) (ΛR[z]) ∧
      ∀ t:ℝ,0<t→ projectionDark H (S) (Λ[z] t) ∧ projectionDark G (Ε) (ΛR[z] t)
 -- genuine thinning convergence. norm convergence in the TWO Hilberts, not just pointwise prices
 heated_points (z:Lead.Clan) (t:ℝ) (p:0<t):
     Tendsto (fun i=>P.cradleH x (P.soldTrumpet A c r n w z i) (P.sold_birth x A c r n w z i Y) t) atTop (𝓝 (Λ[z] t))∧
     Tendsto (fun i=>P.cradleG x (P.soldTrumpet A c r n w z i) (P.sold_birth x A c r n w z i Y) t) atTop (𝓝 (ΛR[z] t))

private lemma pcslender (Q:P.FusionFleet x c r A n Y V) (z:Lead.Clan)(j:Axis) : Tendsto (fun i=> (P.soldTrumpet A c r n w z i).realWidth P j) atTop (𝓝 0):=by
 unfold soldTrumpet; simp_rw [P.tuba_width]; let k:ℕ:= lastTuba (w z) + 1; have he:= (Q.thin z j).add ((P.macroStep_zero.comp Q.high.tendsto_atTop).const_mul (k:ℝ)); rw [mul_zero,zero_add] at he; exact he

private lemma pckeep  (z:Lead.Clan) (i:ℕ): let F:= P.thinOrigin x (P.soldTrumpet A c r n w z i) (P.sold_birth x A c r n w z i Y); projectionDark H (S) F ∧ projectionDark G (Ε) (π' F) ∧
      ∃ (y₀ : H), F=(S).E (P.burst (c (n i))) y₀:=by
 let B':= P.stitchApron z (A i) (c (n i)) (r (n i)); let q:= P.stitch_clear z x c r A n Y i
 have ht:= P.tuba_prep_dark x B' (w z) q; exact ⟨ht.1,ht.2,_,P.trumpet_cost (w z) B' ξ q⟩

private lemma pcenergy (R:P.GalaxyShow x g h A V)(Q:P.FusionFleet x c r A n Y V) (z:Lead.Clan) : Positive (S) (Λ[z]) ∧ Positive (Ε) (ΛR[z]) ∧
      ∀ t:ℝ,0<t→ projectionDark H (S) (Λ[z] t) ∧ projectionDark G (Ε) (ΛR[z] t):=by
 have he(X:Hilbert)(U:OS.Semigroup X 3)(p:ℝ→X)(h:Positive U p)(W:Prism): ∀ t:ℝ,0<t→ projectionDark X U (prism U p W t):=fun _ u=> ⟨prism_dark U p W h u,prism_night p W U h u⟩ -- order
 exact ⟨prism_pos _ _ _ (Q.profile z),P.profile_pos x g h V w R z,fun t p=> ⟨he H (S) _ (Q.profile z) _ t p,he G (Ε) _ (P.route_pos x g h V R z) _ t p⟩⟩

private lemma pcheated_points (R:P.GalaxyShow x g h A V)(Q:P.FusionFleet x c r A n Y V) (z:Lead.Clan) (t:ℝ) (p:0<t):
     Tendsto (fun i=>P.cradleH x (P.soldTrumpet A c r n w z i) (P.sold_birth x A c r n w z i Y) t) atTop (𝓝 (Λ[z] t))∧
     Tendsto (fun i=>P.cradleG x (P.soldTrumpet A c r n w z i) (P.sold_birth x A c r n w z i Y) t) atTop (𝓝 (ΛR[z] t)):=by
 let e(i:ℕ):= P.burst (c (n i)); have ht:Tendsto e atTop (𝓝 0):= P.burst_zero.comp Q.high.tendsto_atTop; have hu(i):0<e i:= P.burst_p _
 refine ⟨(heatedCash H (S) (w z) e ht hu _ _ (Q.profile z) (Q.receipt z).1 t p).congr ?_, (heatedCash G (Ε) (w z) e ht hu _ _ (P.route_pos x g h V R z) (Q.receipt z).2 t p).congr ?_⟩
 · exact fun i=> (P.tuba_quenches x _ _ (P.stitch_clear z x c r A n Y i) t).symm
 exact fun i=> (P.tuba_quenchesG x _ _ (P.stitch_clear z x c r A n Y i) t).symm

lemma get_armada (R:P.GalaxyShow x g h A V)(Q:P.FusionFleet x c r A n Y V): P.ThinArmada x A c r n w Y V g h := by
 exact {
    cinema:= R
    fusion:= Q
    sensor:= fun a i=> P.plays_sensor _ (w a) (P.stitchApron a (A i) (c (n i)) (r (n i))) (Q.paper a i)
    slender:= P.pcslender x A c r n w Y V Q
    vacuum:= fun a i=> P.trumpets_center (w a) (P.stitchApron a (A i) (c (n i)) (r (n i))) x
    keep:= P.pckeep x A c r n w Y
    energy:= P.pcenergy x A c r n w Y V g h R Q
    heated_points:= P.pcheated_points x A c r n w Y V g h R Q }
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
#print axioms YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Spine.get_armada
