import GaugeFieldConstruction.PlenSpeΛ
import GaugeFieldConstruction.CosmosSpeΛ
import GaugeFieldConstruction.OrchardFastYL

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
-- ties allowed in Conf strict positive. Price in same Porches. Do not assert Aura estimates hold at finite pad shared on ties.
variable (Y:SunlitL Cw R G)(h:SurfCheckL G)
open NSF.Table.Pairing
local notation "T♀" => SimArchMars
noncomputable def BorePeakPV (v:SawMars a n): (Cw a).DegreeHab:= RiverBoreL Cw R a F v.val.val (Classical.choice (AppointsMars a v.val.val ⟨v.property,v.val.property.2⟩ P))
noncomputable def EmergePeakPV (x:SimArchMars a n): (Cw a).DegreeHab:= (denseArchMars a n).extend (BorePeakPV Cw R a F) x
abbrev CatchGrainPV {n m:ℕ}(a:Axis)(W:Fin n→ΧiMars)(V:Fin m→ΧiMars)(q:SimArchMars a n × SimArchMars a m): ℂ:= G _ (closedUp a q.1.val q.2.val) (Fin.append (TurnupMars a ∘ W) V)
include h
lemma StoutPV {n m:ℕ}(W:Fin n→ΧiMars)(V:Fin m→ΧiMars): Continuous (CatchGrainPV G a W V) := by
 apply ContinuousOn.comp_continuous (g:=fun y=>G (n+m) y (Fin.append (TurnupMars a ∘ W) V)) (h.sm _).continuousOn (((pairIso (n:=n) (m:=m) a).symm.continuous).comp (continuous_subtype_val.prodMap continuous_subtype_val)) (fun i=> spans i.1.property i.2.property)
omit h
include Y
lemma FirmPV {n m:ℕ}(p:SimArchMars a n)(q:SimArchMars a m)(x: StallLeadMars a p.val P)(y:StallLeadMars a q.val P)(A:Fin n→ΧiMars)(B:Fin m→ΧiMars): inner ℂ (RiverBoreL Cw R a A _ x) (RiverBoreL Cw R a B _ y)= CatchGrainPV G a A B (p,q):=by
 rw [GulfSignL Cw R Y.toCheckΩL]; exact (Y.invoice _ (Fin.append (TurnupMars a∘ A) B) _ (Set.mem_iUnion.mpr ⟨_,WrapL x y⟩)).symm
lemma castPV {n m:ℕ}(p:SawMars a n)(q:SawMars a m)(A:Fin n→ΧiMars)(B:Fin m→ΧiMars):inner ℂ (BorePeakPV Cw R a A p) (BorePeakPV Cw R a B q)= CatchGrainPV G a A B (p.val,q.val):=FirmPV Cw R G a Y _ _ _ _ A B
include h
lemma turnsPeakPV : Continuous (EmergePeakPV Cw R a F) ∧ ∀ x:SawMars a n, EmergePeakPV Cw R a F x.val=BorePeakPV Cw R a F x:= LopeArcMars (J:=(Cw a).DegreeHab) (denseArchMars a n).isDenseInducing_val _ _ (StoutPV G a h F F) (fun i k=> castPV Cw R G a Y i k F F)
lemma CurrencyPairPV{n m:ℕ}(p:SimArchMars a n)(q:SimArchMars a m)(A:Fin n→ΧiMars)(B:Fin m→ΧiMars):inner ℂ (EmergePeakPV Cw R a A p) (EmergePeakPV Cw R a B q)= CatchGrainPV G a A B (p,q):=by
 let S:=SawMars a n ×ˢ SawMars a m
 have E₁:= turnsPeakPV Cw R G a A Y h; have E₂:= turnsPeakPV Cw R G a B Y h
 apply Set.EqOn.closure (s:=S) (f:=fun y=> inner ℂ (EmergePeakPV Cw R a A y.1) (EmergePeakPV Cw R a B y.2)) ?_ ((E₁.1.comp continuous_fst).inner (E₂.1.comp continuous_snd)) (StoutPV G a h A B) (((denseArchMars a n).prod (denseArchMars a m)) (p,q))
 intro y hy; change inner ℂ _ _=_; rw [E₁.2 ⟨_,hy.1⟩,E₂.2 ⟨_,hy.2⟩]; exact castPV Cw R G a Y ⟨_,hy.1⟩ ⟨_,hy.2⟩ A B
lemma ThanksPV (g:AxFearSpeΛ Cw R)(x: SimArchMars a n):((LightLiftL (Cw a)).ℚmeasure).region (SkyRootsSpeΛ a)ᶜ (EmergePeakPV Cw R a F x)=0:=by
 apply g; let T:= Submodule.span ℂ (ΧMΦSpecΛ Cw R a); have he:Set.MapsTo (EmergePeakPV Cw R a F) (SawMars a n) ↑T.topologicalClosure:=by
    intro i b; rw [(turnsPeakPV Cw R G a F Y h).2 ⟨_,b⟩]; exact T.le_topologicalClosure (Submodule.subset_span (show _∈ΧMΦSpecΛ Cw R a from ⟨n,i.val,F,_,rfl⟩)) -- Lean infer.
 have hp:= turnsPeakPV Cw R G a F Y h; apply closure_minimal (t:= EmergePeakPV Cw R a F ⁻¹' (↑T.topologicalClosure)) he (T.isClosed_topologicalClosure.preimage hp.1) (denseArchMars a n x)
-- heat shifts preserve.Carry
lemma returnsPV (x:SimArchMars a n)(y:StallLeadMars a x.val P): EmergePeakPV Cw R a F x= RiverBoreL Cw R a F _ y:=by
 have b:x∈ SawMars a n:= StallWestYL a x.val y
 rw [(turnsPeakPV Cw R G a F Y h).2 ⟨_,b⟩]; exact FeelRiverL Cw R Y.toCheckΩL a F _ _ _
omit Y h in
def GlidePV (u:SimArchMars a n)(t:ℝ≥0)(z:OS.Cross a): SimArchMars a n:=⟨ReefMapL t z u.val,by
 constructor
 · intro i k g; apply u.property.1; exact add_right_cancel g -- tune
 intro i; have h:0<u.val i a:= u.property.2 i
 change 0 < ΦplanR n (ReefMapL t z u.val) i a; rw[ReefShiftL,Pi.add_apply,ReefRodL]; exact add_pos_of_pos_of_nonneg h t.coe_nonneg⟩
lemma CarAxisPV (x:SimArchMars a n)(t:ℝ≥0)(z:OS.Cross a): EmergePeakPV Cw R a F (GlidePV a x t z) = (LightLiftL (Cw a)).E t ((LightLiftL (Cw a)).U z (EmergePeakPV Cw R a F x)):=by
 have hΓ:Continuous (fun u:SimArchMars a n=> GlidePV a u t z):=by
    apply Continuous.subtype_mk; unfold ReefMapL
    exact (show Continuous (fun v:Points n=> NSF.Points.across (ReefOutL t z) v) by exact continuous_id.add (continuous_const (y:=points (n:=n) (fun _=> ReefOutL t z)))).comp continuous_subtype_val -- tune
 let F':= LightLiftL (Cw a)
 let M:=EmergePeakPV Cw R a F
 have hu:= (turnsPeakPV Cw R G a F Y h).1
 apply Set.EqOn.closure (s:= SawMars a n) (f:=fun k=> M (GlidePV a k t z)) (g:=fun k=> F'.E t ((F'.U z) (M k))) _ (hu.comp hΓ) ((F'.E t).continuous.comp ((F'.U z).continuous.comp hu)) (denseArchMars a n x)
 intro i b; obtain ⟨S⟩:= AppointsMars a i.val ⟨b,i.property.2⟩ P
 change EmergePeakPV _ _ _ _ _= F'.E t (F'.U z (EmergePeakPV Cw R a F i))
 rw [returnsPV Cw R G a F Y h _ (ReefShedsL i.val S t z), returnsPV Cw R G a F Y h i S]; exact TrailMovedL (Cw a) i.val _ S t z
#print axioms CarAxisPV
#print axioms ThanksPV
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
