import Lucent.Banner
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry

open TopologicalSpace
namespace Spine
open Lamour.Bridge.Celeste
open Lamour.Bridge.Celeste.Morn
open Py.Rate.LocalLimit.Papal (Weaver household)
open TopologicalSpace Tapestry.Exhibition

open Spine Preparation.Yoke Lucent EmberWind
variable (P:Spine)
local notation "Ξ" => household (P.calibration)
local notation "φ" => P.groundZero 3
local notation "Kₚ" => P.calibration

universe v0
variable {I:Type}[Fintype I]
variable {β:ℕ→ℝ}{R:ℕ→ℝ}{r:ℕ→ℕ}
variable {W:ℕ→I→Staff} {S:Stencil I} {m a:ℕ}{b:ℕ→ℕ}{d:FieldPlan I}
local notation:max "gong" => soundOf P β R W b S m a
local notation "mu" => P.pillars 3

open Preparation.Yoke.Lucent.Arity
namespace Banner
variable {P}
variable (h:Banner I P)(z: Window.Family)

/-- readiness on a list, listing gauge appointments -/
structure Laden (h:Banner I P)(β:ℕ→ℝ)(L:List I)(a:ℕ)(S:Stencil I)(f:ℕ→P.Test):Prop where
    graded : Tariff L a S
    matched : ∀ᶠ s in atTop, (f s).val=Ξ (soundOf P β h.R h.W h.b S L.length a s)
    sound:∀ᶠ s in atTop,Singing (h.W s) S

variable {L Q:List I} {a' : ℕ}{T:Stencil I}
lemma sound_mul (T:Stencil I)(s a':ℕ):
    soundOf P β h.R h.W h.b (S*T) (L++Q).length (a+a') s=
    soundOf P β h.R h.W h.b S L.length a s*soundOf P β h.R h.W h.b T Q.length a' s:=by
 rw [List.length_append]; exact qr_mul _ _ _ _ _ _ _ _ _ _
variable {h}{f g:ℕ→P.Test}
lemma Laden.mul (e:Laden h β L a S f)(t:Laden h β Q a' T g):
   Laden h β (L++Q) (a+a') (S*T) (f*g):=by
 refine ⟨e.graded.paid t.graded, ?_, e.sound.mp (t.sound.mono fun _ ht he=> sing_mul _ _ _ he ht)⟩
 filter_upwards [e.matched,t.matched] with s v w
 change (f s).val*(g s).val=_; rw [sound_mul,v,w];rfl

open Tariff

lemma Laden.oyster(e:Laden h β L a S f)(g:L.Nodup):
    Whelk h.R h.r h.b h.W S L.length a h.plan :=by
 refine ⟨h.bill,e.sound,e.graded.degree,h.scale,e.graded.due _ ?_⟩
 refine List.Pairwise.imp ?_ g
 intro i j b w; exact (h.money.apart b).x2 (by rw [w,sub_self];rfl)
lemma Laden.showtime(e:Laden h β L a S f)(p:P.WickAtNative β)(g:L.Nodup):
   WakePoll P f (faq h.plan S):=P.fullPoll p h.quick (e.oyster g) _ e.matched
variable (h)(β)
abbrev tintC(t:I):=rush P β h.R h.W h.b (V t) 1 1
abbrev pairC:= h.tintC β h.i*h.tintC β h.j
abbrev axialC(z:Window.Family):=rush P β h.R h.W h.b (D z h.k) 0 1
abbrev shearC:= rush P β h.R h.W h.b (G h.u h.v) 2 0

lemma charged (e:Tariff L a S)(t:∀ᶠ s in atTop,Singing (h.W s) S):
    Laden h β L a S (rush P β h.R h.W h.b S L.length a):=by
 obtain ⟨B,l,g⟩:=h.bill
 exact ⟨e,(songrent P g).mono fun _ w=>P.encode_wide w,t⟩
lemma tintB(t:I): Laden h β [t] 1 (V t) (h.tintC β t) :=charged _ _ (v_fee _) (Eventually.of_forall fun _=>v_sings _ _)

lemma pairB:Laden h β [h.i,h.j] 2 (V h.i*V h.j) (h.pairC β):= (h.tintB β _).mul (h.tintB β _)
lemma shearB:Laden h β [h.u,h.v] 0 (G h.u h.v) (h.shearC β):= charged _ _ (g_fee _ _) (h.together.mono fun _ hh=>g_sings _ _ _ hh)
lemma axialB:Laden h β [] 1 (D z h.k) (h.axialC β z):= charged _ _ (d_fee _ _) (Eventually.of_forall fun _=>d_sings _ _ _)

abbrev CardI:= (Option Bool) ⊕ (Bool×Window.Family)
def casting:CardI→ℕ→P.Test
   | .inl none => h.pairC β
   | .inl (.some false)=>h.shearC β
   | .inl (.some true) => h.shearC β*h.pairC β
   | .inr (false,z)=>h.axialC β z
   | .inr (true,z)=>h.pairC β*h.axialC β z

def part:CardI→Stencil I
   | .inl none => V h.i*V h.j
   | .inl (.some false)=>G h.u h.v
   | .inl (.some true) => G h.u h.v*(V h.i*V h.j)
   | .inr (false,z)=>D z h.k
   | .inr (true,z)=>(V h.i*V h.j)*D z h.k

abbrev lyricC(e:CardI):= faq h.plan (h.part e)
theorem castingRev (p:P.WickAtNative β) (e:CardI): WakePoll P (h.casting β e) (h.lyricC e):=by
 have t:=h.money.guests
 have r:=h.shearB β;have v:=h.pairB β
 rcases e with (_|⟨(_|_)⟩)|⟨(_|_),z⟩
 · exact v.showtime p (by simp at *;tauto)
 · exact r.showtime p (by simp at *;tauto)
 · exact (r.mul v).showtime p (by simp at *;tauto)
 · exact (h.axialB β z).showtime p .nil
 exact (v.mul (h.axialB β z)).showtime p (by simp at *; tauto)

#print axioms castingRev
