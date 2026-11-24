import GaugeFieldConstruction.BelleLotusL
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxSize 28000
set_option maxRecDepth 3000
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
namespace RosterJ
namespace BoonsθJ
open JetCurry JetCurry.TrekJ ProbeθJ Yoke SelectionAnalysis
open Repertoire 
variable {P:Spine}
namespace Shower
open SignetS
variable {cost:ℕ→P.Test→ℂ} {j: Axis}(C:Porch P cost j)
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Ember YM.GaugeFieldConstruction.Ember.Volumetric FirstPackMars Stage Calibration Phys Calibration.Floor
open NSF.Table.Pairing
attribute [local instance] Ember.iG Ember.iF Ember.iX Ember.iU Ember.iT2 Ember.iW2 Ember.iV Ember.iS
variable {n:ℕ}{S: City} {P0:Axis→Empire.Across} {L:Sheds S P0} {Cu: Supplies L} {u:ℕ→Carat}
-- axis carried thru. CPI covariance proper. Suit has ALL axes declared, no H3 tilt for phase yet
variable (Cw:∀ j:Axis,Porch P cost j)
variable (R:ΧiMars →ₗ[ℂ]ScreensJ P) (G:CloudsL) (t:Ticket u Cu)
open NSF.Boundary NSF.OS.Semigroup -- no OS namespace clash
open NSF.LD
-- (137)-->(138) variant: projection joint on actual POS. norm displacement criterion; everything commutes on same Hil. use E2 costs, no invocation of L1 for chosen x until after L3!
variable (a:Axis)(p: Points n)(v:eastL n a p)(F:Fin n→ ΧiMars)(J:StallLeadMars a p P)
variable (χ:P.Spectrum0 3)(U:CheckΩL R)
local notation "κx" x:max=> P.privateH x
local notation "ΤP"=> P.publicH
local notation "Ψ" Φ:max a:max=> LightLiftL (Φ a)
local notation "Τ" x:max=> (Ψ (κx x) a)
local notation "Αx"=>P.Spectrum0 3
local notation "μL"=>P.pillars 3
noncomputable def FlickNixL (z:OS.Cross a)(χ:P.Spectrum0 3):ℝ:=let v:= (LightLiftL ((κx χ) a)).orth (RiverBoreL (κx χ) R a F p J); ‖v-(LightLiftL ((κx χ) a)).U z v‖^2
include U
lemma Z_RiverL (z: OS.Cross a)(L:Tendsto (MapFareL P.publicH R a p F z) atTop (𝓝 0)): ∀ᵐ x ∂μL,(Τ x).U z ((Τ x).orth (RiverBoreL (κx x) R a F p J)) = (Τ x).orth (RiverBoreL (κx x) R a F p J):=by
 let k:=HoldThreshL a (R ∘ F) p J
 let δ:=k+k; let V:=FlickNixL R a p F J z; let M(n:ℕ)(x:P.Spectrum0 3):= MapFareL (κx x) R a p F z (n:ℝ≥0)
 have he(n):Integrable (M n) μL:= (BergRollL R a p F J U n z).1
 have hx(n x): ‖M n x‖≤ δ^2:= BergCapL R a p F J U n z x
 have hh(x:P.Spectrum0 3): Tendsto (fun n=> M n x) atTop (𝓝 (V x)):= (tideMapL (κx x) R a p F J U z).comp tendsto_natCast_atTop_atTop
 have hu:Tendsto (fun n=> ∫ x,M n x∂ μL) atTop (𝓝 0):= Tendsto.congr' (Eventually.of_forall (fun i=> (BergRollL R a p F J U i z).2.symm)) (L.comp tendsto_natCast_atTop_atTop)
 have hb :V=ᵐ[μL] 0:=by
    have hp(x): 0≤V x:= sq_nonneg _; have hv(x): ‖V x‖ ≤ δ^2:=le_of_tendsto ((hh x).norm) (Eventually.of_forall (fun i=> hx i x))
    have hm: AEStronglyMeasurable V μL:=aestronglyMeasurable_of_tendsto_ae _ (fun i=>(he i).aestronglyMeasurable) (Eventually.of_forall hh) -- tune
    apply (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall hp) ((integrable_const (δ^2)).mono' hm (Eventually.of_forall hv))).1
    exact tendsto_nhds_unique (tendsto_integral_of_dominated_convergence (μ:=P.pillars 3) (fun _=>δ^2) (fun i=>(he i).aestronglyMeasurable) (integrable_const _) (fun i=> Eventually.of_forall (hx i)) (Eventually.of_forall hh)) hu
 filter_upwards [hb] with x ht; exact (sub_eq_zero.mp (norm_eq_zero.mp (eq_zero_of_pow_eq_zero ht))).symm -- tune
-- actual Lodestar hypotheses from review. Need full Hil. Reduce via glass.
omit U
-- separate
local notation "Χv"=> (κx χ) a
lemma timeFeelL {j:Axis}(C:Porch P cost j) (x:ℝ): (LightLiftL C).edge x=C.BrightHab.edge x:= rfl -- tune
lemma RankEstL (e:P.lodestar 3 χ)(y:(Χv).DegreeHab)(h:∀ b:E4,(Τ χ).unit.translation b y=y):∃ z:ℂ,z • (Χv).groundHab=y :=by
 let C:= Χv; let A:=C.BrightHab
 have hp:∀ b:E4,A.unit.translation b y=y:= fun b=> by
    have hB:=h b; change (Τ χ).edge (b a) ((Τ χ).U _ y)=_ at hB
    rw [timeFeelL] at hB; exact hB
 obtain ⟨ht,hv⟩:= (SelectionAnalysis.invariant_glass C.canopy (daylight (timeMesh P.par)) C.Time C.heat_share y).mp hp
 let x:=P.otherSpectrum 3 a χ
 have he:(y.val:(Χv).H) ∈ rooted (P.portion a x) (P.jointTest a):=(P.vacuum_full a x y.val).2 ⟨ht,fun ⟨n,b,k⟩=>by
    change C.ρ (P.movesOf a (n,b,k)) y.val=y.val; rw[← C.canopy_plays k n b]; exact hv ..⟩
 rw [P.rank_here a (e a)] at he
 have hu: (show P.PortionHil a x from y.val) ∈ Submodule.span ℂ ({P.emptyV a x} : Set (P.PortionHil a x)):= he
 obtain ⟨z,w⟩:= Submodule.mem_span_singleton.mp hu
 exact ⟨z,Subtype.ext w⟩
-- ground projected through E,U now actual joint on selected
lemma dockVacantL (e:P.lodestar 3 χ)(y:(Χv).DegreeHab)(w:∀ t,(Τ χ).E t y=y)(h:∀ b:NSF.OS.Cross a, (Τ χ).U b y=y):∃ z:ℂ,z • (Χv).groundHab=y:=by
 apply RankEstL a χ e; intro x; change (Τ χ).edge _ ((Τ χ).U _ y)=_; rw[h, timeFeelL]
 exact (SelectionAnalysis.lamp_fixed (Χv).BrightHab y).2 w _
lemma RankEstHereL (e:P.lodestar 3 χ)(y:(Χv).DegreeHab)(h:∀ b:NSF.OS.Cross a, (Τ χ).U b ((Τ χ).orth y)= (Τ χ).orth y): (Τ χ).orth y= (inner ℂ (Χv).groundHab y) • (Χv).groundHab:=by
 let Y:= (Τ χ).orth y; obtain ⟨z,q⟩:= dockVacantL a χ e Y ((Τ χ).fixed Y|>.1 (Submodule.starProjection_apply_mem _ _)) h
 let δ:=(Χv).groundHab
 have ht:inner ℂ δ Y=inner ℂ δ y:= by
    apply tendsto_nhds_unique ((tendsto_const_nhds (x:=δ)).inner ((Τ χ).emerges y)); apply Tendsto.congr' _ tendsto_const_nhds
    refine Eventually.of_forall (fun i=>?_); dsimp only; rw [←(Τ χ).swing]; change _=_; rw [show (Τ χ).E i δ= δ from SpireHTMars ..]
 have hp: inner ℂ δ δ=1:=by rw [inner_self_eq_norm_sq_to_K]; rw [show ‖δ‖=1 from (Χv).normΩ]; norm_num
 change Y= inner ℂ δ y • _; rw [←ht,←q, inner_smul_right]; change z • δ= (z* (inner ℂ δ δ)) • δ; rw [hp,mul_one]
#print axioms RankEstHereL
#print axioms Z_RiverL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
