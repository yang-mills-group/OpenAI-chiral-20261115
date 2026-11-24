import GaugeFieldConstruction.EarthBoltL
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
structure SunlitL : Prop extends CheckΩL R where
 invoice : ∀ n (v:Fin n→ΧiMars)(x:Points n), ΦplanR _ x∈ CardsR (Fin n) → G n x v=SπR Cw (fun i=>R (v i)) (ΦplanR n x)
-- extends syntax fix
abbrev suitAxL (s:SO)(a b:Axis):Prop:=∀ x:E4,s.val.motion x b=x a
lemma suitsPoleL {s:SO}{a b:Axis}(h:suitAxL s a b): s.val.motion (basis a)=basis b:=by
 apply ext_inner_left ℝ; intro v; obtain ⟨v,rfl⟩:= s.val.motion.surjective v; rw [s.val.motion.inner_map_map,real_inner_comm, YM.basis_inner,← h v, real_inner_comm (basis b) _, YM.basis_inner]
lemma PlanetSuitL (a b:Axis):∃ s:SO,suitAxL s a b:=by
 by_cases p:a=b; subst b; exact ⟨1,fun x=>congrArg (fun v:E4=> v a) (Ortho.move_one x)⟩
 refine ⟨Angles.rise (Ortho.plane b a) (Real.pi/2),fun x=>?_⟩
 have he:= (YM.Work.A13.plane_givens (Ne.symm p) x (Real.pi/2)).1; change Ortho.move (Ortho.oneParameter (Ortho.plane b a) (Real.pi/2)) x b=x a; simpa using he
lemma suitsEQL {s:SO}{a b:Axis}(h:suitAxL s a b): Signed.reflect b *s.val= s.val* Signed.reflect a:=by
 have hu(v:E4)(i:Axis):Ortho.move (Signed.reflect i) v=v-(2*(v i)) • basis i:=by
    ext j; by_cases p:j=i; · subst j; simp; ring
    simp [p]
 apply Ortho.ext; intro x; rw [Ortho.move_mul,Ortho.move_mul,hu,hu]; change s.val.motion x- _ • _= s.val.motion (x- _ • _)
 rw [map_sub,LinearIsometryEquiv.map_smul, suitsPoleL h]; exact congrArg (fun z:ℝ=>s.val.motion x -(2*z) •basis b) (h x)
noncomputable def PlissCL {s:SO}{a b:Axis}(h:suitAxL s a b)(v:OS.Cross a): OS.Cross b:=⟨s.val.motion v.val, (h v.val).trans v.property⟩
lemma Pliss0L {s:SO}{a b:Axis}(h:suitAxL s a b):PlissCL h 0=0:= Subtype.ext (s.val.motion.map_zero)
lemma tickSuitL {s:SO}{a b:Axis}(h:suitAxL s a b)(x:ΧiMars): TurnupMars b (compassPiMars t s x)=compassPiMars t s (TurnupMars a x):=by
 let H:= Signed.mirror a * (Signed.mirror b)⁻¹; have hp: signBit H=false:=by simp [H, signBit_mul] -- sign_inv
 let w:=signMot H hp; have u: HueTurnsMars (Signed.mirror b).ortho s=s*w:=by
    apply Subtype.ext
    change Signed.reflect b * s.val * (Signed.reflect b)⁻¹ = s.val * H.ortho
    have hu:= suitsEQL h
    have hw:H.ortho= Signed.reflect a * (Signed.reflect b)⁻¹:=by change Signed.inclusionO _= _; rw [map_mul,map_inv]; rfl
    rw[hw,hu,mul_assoc]
 rw [TurnupMars,← shadePiMoon, DutyPiiotMars,u,sailMulMars]; change _=_; rw[PiProperMoon]
 apply congrArg; change (spinFrame four H) ((spinFrame four (Signed.mirror b)) (shade _ _))= _; rw[←Module.End.mul_apply,← map_mul, show H*(Signed.mirror b)= _ from mul_inv_cancel_right ..] -- tune
lemma dressE4L {s:SO}{a b:Axis}(h:suitAxL s a b)(v:OS.Cross a)(p:ℝ≥0) : s.val.motion (ReefOutL p v)=ReefOutL p (PlissCL h v):=by unfold ReefOutL; rw [map_add,LinearIsometryEquiv.map_smul,suitsPoleL h]; rfl
lemma DistantL {s:SO}{a b:Axis}(h:suitAxL s a b)(v:OS.Cross a)(p:ℝ≥0)(x:Points n): motionMoonMars s (ReefMapL p v x)=ReefMapL p (PlissCL h v) (motionMoonMars s x):=by
 ext1 i; change s.val.motion (_ + _)= _+_; rw [map_add, dressE4L h]; rfl
lemma ticketSuitL {m n:ℕ}(x:Points m)(y:Points n){s:SO}{a b:Axis}(h:suitAxL s a b): motionMoonMars s (closedUp a x y)=closedUp b (motionMoonMars s x) (motionMoonMars s y):=by
 ext1 i; refine Fin.addCases (fun j=>?_) (fun j=>?_) i
 · rw [NSF.Table.Pairing.enter]; change s.val.motion _= _; rw[NSF.Table.Pairing.enter]
   exact (Eq.trans (Ortho.move_mul _ _ _).symm ((congrArg (fun z:Ortho=> z.move (x j)) (suitsEQL h).symm).trans (Ortho.move_mul _ _ _))) -- tune move defeq
 rw [NSF.Table.Pairing.leave]; change s.val.motion _=_; rw[NSF.Table.Pairing.leave]; rfl
lemma WrapL {m n:ℕ}{x:Points m}{y:Points n}{a:Axis}(h:StallLeadMars a x P)(w:StallLeadMars a y P): ΦplanR _ (closedUp a x y)∈ VplaneR _ a:= char_R ⟨PolesLMars h.L w.L h.pol w.pol,OpenRollR (TerraceOpensMars x y h w)⟩
variable (K:SunlitL Cw R G)(f: SurfCheckL.boisterL t G)
include K f
lemma OroLineL {m n:ℕ}{x:Points m}{y:Points n}{a:Axis}(h:StallLeadMars a x P)(w:StallLeadMars a y P){s:SO}{b:Axis}(p:suitAxL s a b)(F:Fin m→ΧiMars)(V:Fin n→ΧiMars):
 GulfPriceL Cw R F V a x y = GulfPriceL Cw R (compassPiMars t s ∘ F) (compassPiMars t s ∘ V) b (motionMoonMars s x) (motionMoonMars s y):=by
 let A:=closedUp a x y; let KA:=compassPiMars t s
 have he: Fin.append (TurnupMars b ∘ (KA ∘ F)) (KA∘ V)= KA ∘ (Fin.append (TurnupMars a∘ F) V):=by
    ext1 i; refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp only[Fin.append_left,Fin.append_right,Function.comp_apply]; exact tickSuitL t p _
 have hx:=WrapL h w
 have hp:=f (m+n) (Fin.append (TurnupMars a ∘ F) V) A (fun i j e=>hx (congrArg (fun v:E4=>v a) e)) s
 have hy:ΦplanR _ (motionMoonMars s A)∈CardsR _:=Set.mem_iUnion.mpr ⟨b,fun i j g=>hx ((p _).symm.trans (g.trans (p _)))⟩ -- g is PhiPlanR defeq
 rw [K.invoice _ _ _ hy,K.invoice _ _ _ (Set.mem_iUnion.mpr ⟨_,hx⟩),← he,ticketSuitL x y p] at hp -- A
 exact hp.symm
#print axioms OroLineL
end Shower
end BoonsθJ
end RosterJ
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
end
