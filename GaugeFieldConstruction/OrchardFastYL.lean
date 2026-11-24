import GaugeFieldConstruction.EstreLiteL
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
include J
lemma StallWestYL: p∈westL n a:= char_R ⟨J.pol,OpenRollR J.pays⟩ -- tune
lemma StallRecitesYL (d:Equiv.Perm (Fin n)): ∃ H:StallLeadMars a (NSF.Points.rearrange d p) P,RiverBoreL Cw R a (F ∘ d) (NSF.Points.rearrange d p) H=RiverBoreL Cw R a F p J :=by
 let p':=NSF.Points.rearrange d p; let l:= J.L;let σ:= J.σ
 let M:= l.map d.symm; let τ:= σ ∘ d
 have hz(i:Fin n): ΦplanR n p' (d.symm i)= ΦplanR n p i:=by unfold ΦplanR; dsimp [p', NSF.Points.rearrange]; rw [d.apply_symm_apply] <;> rfl -- tune
 have ht(i): τ (d.symm i)=σ i:=by simp [τ]
 have hp: ΦplanR n p'∈ OpenR a τ M:=by refine List.pairwise_map.mpr ((show RollBestR _ _ from J.pays).imp fun {k j} a=>?_); rw [hz,hz,ht,ht]; exact a
 have hv:PolesR M:=⟨J.pol.1.map d.symm.injective,fun i=> List.mem_map.mpr ⟨d i,J.pol.2 _,d.symm_apply_apply i⟩⟩
 let W:StallLeadMars a p' P:=⟨M,τ,hv,hp,fun i=> J.toll _⟩
 refine ⟨W,?_⟩; let c:= Cw a
 change ActorMars _ _ (some 0) (billActMars c τ (BodyΘ P (fun i=> R ((F ∘ d) i)) a τ) (ΦplanR _ p') M)=_
 apply congrArg (ActorMars _ _ _); change billActMars _ _ _ _ M=billActMars _ σ _ _ l; unfold billActMars; dsimp only [M]; rw[List.map_map]; apply congrArg (fun u:Fin n→VignMars c.DegreeHab=> l.map u); ext1 i; simp only [Function.comp_apply,hz,ht,BodyΘ,Equiv.apply_symm_apply] <;> rfl -- tune
lemma StallRidsYL (h:CriteriaL Cw R)(z:OS.Cross a) : (LightLiftL (Cw a)).U z ((LightLiftL (Cw a)).orth (RiverBoreL Cw R a F p J))= (LightLiftL (Cw a)).orth (RiverBoreL Cw R a F p J):=by
 let d:= Tuple.sort (fun i=> p i a); let p':=NSF.Points.rearrange d p
 obtain ⟨H,e⟩:= StallRecitesYL Cw R a p F J d
 have he:eastL n a p':=by
    refine ⟨Monotone.strictMono_of_injective (Tuple.monotone_sort (fun k=> p k a)) (StallWestYL a p' H),fun i=>?_⟩; exact lt_of_lt_of_le (H.toll i) (sub_le_self _ (H.σ i).2.le)
 rw [← e]; exact h n a p' H he _ _
omit J
include U
lemma SanctuaryYL (Z:CriteriaL (P.privateH χ) R)(e:P.lodestar 3 χ){n m:ℕ}(F:Fin n→ΧiMars)(A:Fin m→ΧiMars)(k:Points n)(y:Points m)(s:StallLeadMars a k P)(t:StallLeadMars a y P) (b:ℕ→OS.Cross a)(q:ℕ→ℝ≥0)(hp:Tendsto q atTop atTop):
 Tendsto (fun i:ℕ=>BerryEarthL R a (q i) (b i) F A k y χ) atTop (𝓝 ((Star.star (pearlL R χ F k))*pearlL R χ A y)):=by
 let C:=P.privateH χ a; let p:= LightLiftL C; let ν:=C.groundHab
 let f:=RiverBoreL (P.privateH χ) R a F k s; let g:=RiverBoreL (P.privateH χ) R a A y t
 have d(z:NSF.OS.Cross a):p.U z (p.orth g)=p.orth g:=StallRidsYL (P.privateH χ) R a y A t Z z
 have hv:=RankEstHereL a χ e g d
 change p.orth g= inner ℂ ν g • ν at hv
 have he: inner ℂ f (p.orth g)= Star.star (pearlL R χ F k) * pearlL R χ A y :=by
    rw [hv,inner_smul_right,mul_comm]
    have hp:inner ℂ ν g=pearlL R χ A y:= ConquerL (P.privateH χ) R a y A t U
    have ht:inner ℂ f ν = Star.star (inner ℂ ν f):= (inner_conj_symm _ _).symm
    rw [hp,ht,show inner ℂ ν f= _ from ConquerL (P.privateH χ) R a k F s U]; rfl
 let w(i:ℕ):= p.E (q i) (p.U (b i) g)
 have hu:Tendsto w atTop (𝓝 (p.orth g)):=by
    apply tendsto_iff_dist_tendsto_zero.mpr; have hz:= tendsto_iff_dist_tendsto_zero.mp ((p.emerges g).comp hp); refine hz.congr ?_
    intro i; unfold w; rw [←ContinuousLinearMap.comp_apply (p.E _),p.independent,ContinuousLinearMap.comp_apply]
    change dist _ _= dist (p.U _ _) (p.orth g); nth_rw 2 [← d (b i)] -- tune
    rw [dist_eq_norm,dist_eq_norm,←map_sub,p.unitary]; rfl
 rw [←he]; refine (((innerSL ℂ f).continuous.tendsto _).comp hu).congr ?_; intro i; exact ReefRealL (P.privateH χ) R U F A a k y s t _ _
#print axioms SanctuaryYL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
