import GaugeFieldConstruction.ChasmLightYL
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
open Set Complex
variable (J0: SunlitL P.publicH R G)(f: SurfCheckL.boisterL t G)
variable (E:∀ᵐ x∂P.pillars 3,P.lodestar 3 x) (Z:∀ᵐ x∂P.pillars 3, CriteriaL (P.privateH x) R)
open PlaneL
variable {m:ℕ}
variable (x:Points n)(y:Points m)(V: Fin m→ ΧiMars)
abbrev PureXYL (χ:P.Spectrum0 3):Prop:= PurePC_L (P.privateH χ) R t
noncomputable abbrev shineYL (χ:P.Spectrum0 3)(F:Fin n→ΧiMars)(p:Points n):= tessL (P.privateH χ) R t U F p
-- uniform domination on compact motions
lemma plasmaSureYL (s:SO)(z:E4):Continuous (plazaYL (n:=n) s z):= (calendarSureL _ _).comp (motionθL s)
include J
lemma ReserveYL :∀ᶠ x in 𝓝 p, ∃ K:StallLeadMars a x P,HoldThreshL a (R ∘ F) x K=HoldThreshL a (R∘ F) p J:=by
 have hp:∀ᶠ x:Points n in 𝓝 p,ΦplanR n x∈ OpenR a J.σ J.L:= (ΦlegR n).continuousAt.tendsto.eventually ((Opens_R _ _ _).mem_nhds J.pays)
 have he:∀ᶠ x:Points n in 𝓝 p,∀ i:Fin n, 0< x i a-StallJ P (J.σ i):= eventually_all.mpr fun i=> ((show Continuous (fun x:Points n=>x i a-StallJ P (J.σ i)) by fun_prop).continuousAt.tendsto).eventually (lt_mem_nhds (J.toll i)) -- tune lt
 filter_upwards [hp,he] with x t w using ⟨⟨J.L,J.σ,J.pol,t,w⟩,rfl⟩
omit J
include U
lemma closeCrownYL (p:Points n)(h:p∈conf n):∃ k:ℝ,∀ᶠ x in 𝓝 p,∀ χ:P.Spectrum0 3, PureXYL R t χ→ ‖shineYL R t U χ F x‖≤k:=by -- tune argument order U χ
 obtain ⟨s,v⟩:=denseQuiverL timeAxis p h; let a:=timeAxis; obtain ⟨c,⟨J⟩⟩:= spikeWestL (P:=P) timeAxis _ v; let F':= compassPiMars t s ∘ F; let L:=plazaYL (n:=n) s c
 refine ⟨HoldThreshL a (R∘ F') (L p) J,?_⟩; filter_upwards [((plasmaSureYL (n:=n) s c).tendsto p).eventually (ReserveYL R a (L p) F' J), (conf_open n).eventually_mem h] with y u hy x hx
 obtain ⟨K,hK⟩:=u
 rw [shineYL, ← TessCovL (P.privateH x) R t F U hx s y hy, ← WorldLaceL (P.privateH x) R t _ F' U hx (NSF.Points.move_in _ hy) c] -- rw unnecessary
 rw [TessBlueL (P.privateH x) R t F' U hx _ (westBlueL _ (StallWestYL a (L y) K)), ←hK]; exact priceToneL R a _ F' K x U
omit U
lemma skyCardYL {X:Type*}[TopologicalSpace X](P:X→ℕ→Prop)(L:Set X)(h:IsCompact L)(e:∀ x, Monotone (P x))(v:∀ x∈ L,∃ k:ℕ,∀ᶠ i in 𝓝 x,P i k):∃ k:ℕ,∀ x∈ L,P x k:=by
 let U(n:ℕ):=interior {x:X | P x n}; have he :Monotone U:=fun i j hj=>interior_mono (fun x hp=>e x hj hp)
 have hcov:L⊆ ⋃ i,U i:=by
    intro x h; obtain ⟨k,T⟩:=v x h; exact mem_iUnion.mpr ⟨k,mem_interior_iff_mem_nhds.mpr T⟩
 obtain ⟨k,h⟩:= h.elim_directed_cover U (fun _=>isOpen_interior) hcov (fun i j=>⟨max i j,he (le_max_left ..),he (le_max_right ..)⟩) -- subgoals order choose
 exact ⟨k,fun x p=> show x∈{x:X|P x k} from interior_subset (h p)⟩
include U
lemma CrownU_YL (L:Set (Points n))(h:IsCompact L)(v:L⊆ conf n):∃ k:ℝ,∀ x∈L,∀ χ:P.Spectrum0 3, PureXYL R t χ→ ‖shineYL R t U χ F x‖≤k:=by
 let T (x:Points n)(i:ℕ):Prop:= ∀ χ:P.Spectrum0 3,PureXYL R t χ→ ‖shineYL R t U χ F x‖≤ (i:ℝ)
 have hcov:∀ x∈L,∃ k:ℕ,∀ᶠ i in 𝓝 x,T i k:=by
    intro x p; obtain ⟨k,f⟩:= closeCrownYL R t F U x (v p); obtain ⟨n,e⟩:= exists_nat_gt k; exact ⟨n,f.mono fun _ v χ q=> (v χ q).trans e.le⟩
 obtain ⟨k,e⟩:=skyCardYL T L h (fun x i j k f χ p=> (f χ p).trans (Nat.cast_le.mpr k)) hcov
 exact ⟨k,e⟩
lemma BranchCapYL (h:x∈conf n)(v:y∈conf m): ∃ k:ℝ,∃ j:ℕ,∀ᶠ p:Points n in 𝓝 x, ∀ i:ℕ,j ≤ i → apartYL (EarYL i) p y∈conf (n+m) ∧∀ χ:P.Spectrum0 3, PureXYL R t χ → ‖shineYL R t U χ (Fin.append F V) (apartYL (EarYL i) p y)‖≤k:=by
 obtain ⟨s,H,Y,h⟩:=OasisYL timeAxis x y h v; let a:=timeAxis; obtain ⟨c,⟨T⟩⟩:= pitaPrimeYL (P:=P) timeAxis x s H; obtain ⟨e,⟨B⟩⟩:= spikeWestL (P:=P) timeAxis _ Y
 let L:=pitaYL a s c (n:=n); let F':= FlyWYL t s a F; let y':=plazaYL s e y; let V':= compassPiMars t s ∘ V; let U':= SailUYL s c e a; let H':= SailHYL s c e a
 obtain ⟨j,u⟩:= eventually_atTop.mp ((accelsYL a s c e h).eventually (eventually_ge_atTop 0))
 refine ⟨HoldThreshL a (R∘ F') (L x) T*HoldThreshL a (R∘ V') y' B,j,?_⟩; filter_upwards [(((CalendarUL a n).comp (plasmaSureYL s c)).tendsto x).eventually (ReserveYL R a (L x) F' T)] with p q i e'
 obtain ⟨K,hK⟩:=q
 have H:=u i e'; refine ⟨fromPlazaYL s c _ ?_,?_⟩ -- decompose
 · rw[←GustSailYL a s c e p y i H]; exact blueConfL _ (westBlueL _ (WrapL K (ReefShedsL y' B (H' i) (U' i))))
 intro χ v; rw [shineYL, ComposedYL R t a F χ U s c e p y V K B v i H,←hK]; exact metersL R a χ U _ _ _ _ _ _ K B
lemma BoundCapYL (v:y∈conf m)(L:Set (Points n))(h:IsCompact L)(e:L⊆ conf n): ∃ k:ℝ,∀ᶠ i:ℕ in atTop, ∀ x∈ L, apartYL (EarYL i) x y∈conf (n+m) ∧∀ χ:P.Spectrum0 3, PureXYL R t χ→ ‖shineYL R t U χ (Fin.append F V) (apartYL (EarYL i) x y)‖≤k:=by
 let Z(x:Points n)(j:ℕ):Prop:=∀ i:ℕ,j ≤ i  → apartYL (EarYL i) x y∈ conf (n+m) ∧∀ χ:P.Spectrum0 3, PureXYL R t χ→ ‖shineYL R t U χ (Fin.append F V) (apartYL (EarYL i) x y)‖≤(j:ℝ)
 have hcov:∀ x∈L,∃ k:ℕ,∀ᶠ i in 𝓝 x,Z i k:=by
    intro x hx; obtain ⟨k,j,u⟩:= BranchCapYL R t F U x y V (e hx) v; obtain ⟨b,f⟩:= exists_nat_gt k; refine ⟨max j b, u.mono fun z q i w=>?_⟩; exact ⟨(q i ((le_max_left ..).trans w)).1,fun χ P=>(q i ((le_max_left ..).trans w)).2 χ P|>.trans (f.le.trans (Nat.cast_le.mpr (le_max_right ..)))⟩
 obtain ⟨j,H⟩:= skyCardYL Z L h (fun x i j k T m e=> let u:=T m (k.trans e); ⟨u.1,fun χ v=>(u.2 χ v).trans (Nat.cast_le.mpr k)⟩) hcov
 exact ⟨j,(eventually_ge_atTop j).mono fun i p x v=> H x v i p⟩
include f J0 E Z
lemma ParcelCapYL (v:y∈conf m)(L:Set (Points n))(h:IsCompact L)(e:L⊆ conf n): ∃ k:ℝ,∀ᶠ i:ℕ in atTop, ∀ x∈ L, apartYL (EarYL i) x y∈conf (n+m) ∧ ‖G (n+m) (apartYL (EarYL i) x y) (Fin.append F V)‖≤k:=by
 obtain ⟨k,T⟩:= BoundCapYL R t F U y V v L h e; refine ⟨k*(P.pillars 3).real univ,?_⟩; filter_upwards [T] with i w x q; obtain ⟨A,B⟩:= w x q; refine ⟨A,?_⟩; rw [meanVinesL R G t _ _ U J0 f A]; exact norm_integral_le_of_norm_le_const ((PureAllL R G t U J0 f E Z).mono fun χ p=>B χ p)
lemma MeanStarYL (h:x∈conf n)(v:y∈conf m): Tendsto (fun i:ℕ=> G _ (apartYL (EarYL i) x y) (Fin.append F V)) atTop (𝓝 (∫ χ,shineYL R t U χ F x*shineYL R t U χ V y∂ P.pillars 3)):=by
 let Q(i:ℕ):=apartYL (EarYL i) x y; let A(i:ℕ)(χ:P.Spectrum0 3):= shineYL R t U χ (Fin.append F V) (Q i)
 obtain ⟨k,j,e⟩:= BranchCapYL R t F U x y V h v; have hp:=mem_of_mem_nhds e -- `e` Eventually not Set but defeq
 have he:= PureAllL R G t U J0 f E Z; have d:= eventually_ge_atTop j
 refine Tendsto.congr' (f₁:=fun i:ℕ=>∫ χ, A i χ∂ P.pillars 3) (d.mono fun i p=> (meanVinesL R G t (Q i) _ U J0 f (hp i p).1).symm) ?_ -- syntax tuner args
 refine tendsto_integral_filter_of_dominated_convergence _ (d.mono fun i p=> (show StronglyMeasurable (A i) from TessCarbonL R t (Q i) _ U (hp i p).1).aestronglyMeasurable) (d.mono fun i b=>he.mono fun χ p=> (hp i b).2 χ p) (integrable_const k) ?_
 filter_upwards [he,Z,E] with χ g u v'; exact HighFactorYL R t F χ U x y V g u v' h v
#print axioms MeanStarYL
#print axioms CrownU_YL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
