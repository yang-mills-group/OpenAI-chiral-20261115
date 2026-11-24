import GaugeFieldConstruction.VennInkYL
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
open YM.GaugeFieldConstruction YM.GaugeFieldConstruction.Fathom Points Bulb
variable (k: Fin n)(b:Fathom.Bulb)(r:ℝ)
-- frame pack continuity all F
variable (U3: PureXYL R t χ)
include U
private noncomputable def particleDYL(p:Points n): MultilinearMap ℂ (fun _ : Fin n=> grainMars) ℂ:= (GlobeLightL (P.privateH χ) R t U _ p).compLinearMap (fun _ : Fin n=>FreightMars.symm.toLinearMap)
include U3
lemma particleYL (T:Fin n→ grainMars)(X:Points n)(v:X∈conf n): ContinuousAt (fun p:Points n ×(Fin n→ grainMars)=> shineYL R t U χ (FreightMars.symm ∘ p.2) p.1) (X,T):=by
 let B(i:SpeckMars):grainMars:= Pi.single i 1; let w(ρ:Fin n→ SpeckMars):Fin n→ grainMars:= B ∘ ρ
 let K(ρ:Fin n→SpeckMars)(y:Points n × (Fin n→ grainMars)):=(∏ i:Fin n, y.2 i (ρ i))* shineYL R t U χ (FreightMars.symm ∘ w ρ) y.1
 have he(q: Fin n→SpeckMars): ContinuousAt (K q) (X,T):=by
    unfold K; apply ContinuousAt.mul
    · fun_prop
    exact ((TessLightL (P.privateH χ) R t _ (FreightMars.symm ∘ w q) U U3 v).tendsto.comp (continuousAt_fst (p:=(X,T))).tendsto)
 refine (show ContinuousAt (fun x=> ∑ i:Fin n→SpeckMars,K i x) (X,T) from tendsto_finsetSum _ (fun i _=> (he i).tendsto)).congr ?_
 apply Eventually.of_forall; rintro ⟨z,A⟩
 let F(i:Fin n)(j:SpeckMars):grainMars:= A i j • B j; have hf(i:Fin n): A i=∑ j:SpeckMars,F i j:=by ext1 b; simp [F,B,Finset.sum_apply,Pi.single_apply]
 change (∑ i:Fin n→ SpeckMars,K i (z,A)) = particleDYL R t χ U z A
 symm; conv_lhs=> rw[show A=fun i=>∑ j:SpeckMars,F i j from funext hf]
 simp_rw[MultilinearMap.map_sum]; apply Finset.sum_congr rfl; intro i _; exact (particleDYL R t χ U z).map_smul_univ (fun j=>A j (i j)) (w i)
omit U3 U
abbrev GrainJYL (n:ℕ):= Fin n→ grainMars
abbrev ArcStYL (a:Axis)(k:Fin n)(b:Fathom.Bulb): Set (Points n ×ℝ):= {x | calmYL k a x.2 x.1 b}
abbrev BoxStYL (k:Fin n)(b:Fathom.Bulb): Set (Points n) := {x | BreatherMars b k x}
abbrev CalmPadYL (b:Fathom.Bulb)(a:Axis)(k:Fin n):= ArcStYL a k b × GrainJYL n
abbrev WardPadYL (b:Fathom.Bulb)(k:Fin n):= BoxStYL k b × GrainJYL n
variable {X:Type*}[TopologicalSpace X]
lemma coastClearYL (F:X→Fin n→ΧiMars)(S:ΧiMars)(q:Continuous fun x=> FreightMars ∘ F x): Continuous fun x=> FreightMars ∘ (Fin.cons (α:=fun _=>ΧiMars) S (F x)):=by
 apply continuous_pi; intro i; refine Fin.cases (motive:=fun i=>Continuous (fun x=>(FreightMars ∘ (Fin.cons (α:=fun _=>ΧiMars) S (F x))) i)) ?_ ?_ i
 change Continuous (fun _ : X=>FreightMars S); exact continuous_const
 intro i; have hp:= Continuous.comp (show Continuous (fun f: Fin n→ grainMars=> f i) from continuous_apply i) q; exact hp
lemma windowSugarYL (F:X→Fin n→ΧiMars)(W:ΧiMars)(k:Fin n)(q:Continuous fun x=> FreightMars ∘ F x):Continuous fun x=>FreightMars ∘ (Function.update (F x) k W):=by
 apply continuous_pi; intro i; by_cases s:i=k
 · subst i; simp only [Function.comp_apply,Function.update_self]; exact continuous_const
 simp only [Function.comp_apply,Function.update_of_ne s]; exact (continuous_apply i).comp q
include U U3
lemma PillarsContYL (f:X→Points n)(F:X→Fin n→ΧiMars)(p:Continuous f)(z:∀ x,f x ∈ conf n)(q:Continuous (fun x=> FreightMars ∘ F x)): Continuous (fun x=> shineYL R t U χ (F x) (f x)) :=by
 let B(x:X):= (f x,FreightMars ∘ F x)
 have h:Continuous (fun x=> shineYL R t U χ (FreightMars.symm ∘ (B x).2) (B x).1):= continuous_iff_continuousAt.mpr fun x=> (particleYL R t χ U U3 (B x).2 (B x).1 (z x)).tendsto.comp ((p.prodMk q).tendsto x)
 exact h.congr fun x=>by dsimp only [B]; rw [show FreightMars.symm ∘ (FreightMars ∘ F x)=F x from funext fun i=> FreightMars.symm_apply_apply _]
omit U U3
lemma sloganYL {Y:Type*}[MetricSpace Y][MeasurableSpace Y][BorelSpace Y][CompactSpace Y](μ:Measure Y)[IsFiniteMeasure μ](Z:X→Y→ℂ)(v:Continuous (Function.uncurry Z)): Continuous fun x=>∫ y,Z x y∂μ:=by
 rw [← continuousOn_univ]; exact continuousOn_integral_of_compact_support isCompact_univ v.continuousOn (fun _ x _ p=> (p (Set.mem_univ _)).elim)
include U U3
-- continuous price on Arc
noncomputable def YTopMarkYL (x:CalmPadYL b a k):= TopNoteYL t k b a x.1.val.1 (FreightMars.symm ∘ x.2) x.1.val.2 (fun n F p=> shineYL R t U χ F p)
noncomputable def YNoteMarkYL (x:WardPadYL b k):= AnthemYL t k b a x.1.val (FreightMars.symm∘ x.2) (fun n F p=> shineYL R t U χ F p)
lemma VestSmartYL : Continuous (YTopMarkYL R t a χ U k b):=by
 let Y:= CalmPadYL b a k; let S(x:Y):= x.1.val.1; let r(x:Y):=x.1.val.2; let F'(x:Y):= FreightMars.symm ∘ x.2
 have pf:Continuous (fun x:Y=>FreightMars ∘ F' x):= continuous_snd.congr (fun x=>funext (fun _=> (FreightMars.apply_symm_apply _).symm))
 have hr: Continuous r:= continuous_snd.comp (continuous_subtype_val.comp continuous_fst); have hs:Continuous S:=continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
 let X':=fun x:Y=>ledgeYL k a (r x) (S x) 1
 have hm: Continuous X':= hs.add ((show Continuous (fun _ : Y=>(1:ℝ)) from continuous_const).smul (show Continuous (fun x:Y=>r x • mirDirYL k a) from hr.smul continuous_const))
 have H(x:Y):calmYL k a (r x) (S x) b:= x.1.2
 let T':CostsYL:=fun n F p=>shineYL R t U χ F p
 change Continuous (fun x:Y=> T' n (F' x) (X' x) - (T' n (F' x) (S x)+r x • ∑ i:Axis, ScrollOpYL a (S x) b i k (r x) (T' _ (Fin.cons (TotalStarsMars t i a) (F' x)))))
 refine (PillarsContYL R t χ U U3 X' F' hm (fun x=> (calm1_YL _ _ _ _ _ (H x)).bounds) pf).sub ((PillarsContYL R t χ U U3 S F' hs (fun x=> (calm0_YL _ _ _ _ _ (H x)).bounds) pf).add (hr.smul (continuous_finsetSum _ fun i _=>?_)))
 haveI:= RΦayComYL b i; haveI:= RΦayCanYL b i; let Z:= ZonesYL b i
 let J(x:Y×Z): Points (n+1):= rayMoveYL a (S x.1) k (r x.1) b i x.2
 let Tm(x:Y×Z):Fin (n+1)→ΧiMars:= Fin.cons (TotalStarsMars t i a) (F' x.1)
 have hj: Continuous J:=by
    have p:Continuous (fun x:Y×Z=>x.2.2.val):= continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    have hq: Continuous (fun x:Y×Z=>x.2.1.val):= continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
    exact alabasterYL.comp (p.prodMk ((hs.comp continuous_fst).add (hq.smul ((hr.comp continuous_fst).smul continuous_const))))
 exact sloganYL (rayonZYL b i) _ (((RΦayPriceYL b i).comp continuous_snd).mul (PillarsContYL R t χ U U3 J Tm hj (fun x=> RΦayHappyYL a _ b i k _ (H x.1) _) (coastClearYL _ _ (pf.comp continuous_fst))))
lemma AnthemSmartYL : Continuous (YNoteMarkYL R t a χ U k b):=by
 let Y:= WardPadYL b k; let S(x:Y):= x.1.val; let F'(x:Y):= FreightMars.symm ∘ x.2
 have pf:Continuous (fun x:Y=>FreightMars ∘ F' x):= continuous_snd.congr (fun x=>funext (fun _=> (FreightMars.apply_symm_apply _).symm))
 have hs:Continuous S:=continuous_subtype_val.comp continuous_fst
 have H(x:Y):BreatherMars b k (S x):= x.1.2
 let T':CostsYL:=fun n F p=>shineYL R t U χ F p
 change Continuous (fun x:Y=> ∑ j:Axis,∑ i:Axis, MeterA_YL b i (S x) (Fin.cons (TotalStarsMars t i j) (Function.update (F' x) k (TotalStarsMars t j a))) T')
 refine continuous_finsetSum _ (fun j _=>continuous_finsetSum _ (fun i _=>?_))
 haveI:= vestFinYL i b; haveI:= isCompact_iff_compactSpace.mp (vestKYL i b); let Z:= VestHYL b i
 let J(x:Y × Z):= YM.Points.cons x.2.val (S x.1); let Tm(x:Y×Z):Fin (n+1)→ ΧiMars:= Fin.cons (TotalStarsMars t i j) (Function.update (F' x.1) k (TotalStarsMars t j a))
 have hj: Continuous J:= alabasterYL.comp ((continuous_subtype_val.comp continuous_snd).prodMk (hs.comp continuous_fst))
 simp_rw [MeterA_YL, raysVisitYL]
 exact sloganYL (landRentYL (VestHYL b i)) _ (((beamInkYL i b).comp (continuous_subtype_val.comp continuous_snd)).mul (PillarsContYL R t χ U U3 J Tm hj (fun x=> RoomMars _ _ _ (H x.1) _ (Bulb.cone b i x.2.2)) (coastClearYL _ _ (windowSugarYL _ _ _ (pf.comp continuous_fst)))))
#print axioms AnthemSmartYL
#print axioms VestSmartYL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
