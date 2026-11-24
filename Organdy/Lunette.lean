import Organdy.Chinchilla

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy.Royal
open Buffered Buffered.Afterglow
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Pastry Tenant Tower

open VacuumSelection


open Lamour.Bridge.Celeste Lamour.Bridge.Celeste.Clock
open CF.Pannier.Chancel Hookah Tapestry

open Yoke Yoke.Bazaar
open Optic
open Larva (Chip Domaine dint)
open Hookah.Rake
open Pressure Worth BProof
open Papal



open Sour Swell

open Hive Levier Urn


abbrev veer (T:Shape):= detX (twin T).s
abbrev hmMark {N:Side}(T:Shape) (f:Mark N):Mark N:=
 voltaM (Levier.ray (veer T) T)⁻¹ f
def flick {K:Calibration}(T:Shape)(f:Buffered.Family K):Buffered.Family K:=
 suede T (veer T) (spinU (veer T) (twin T).s) f

variable {K:Calibration}{S:Finset Cover}{f:Buffered.Family K}(T:Shape)
lemma veer_sign : veer T = detX T.s:=by
 have h:=det_p (twin T).s T.s
 rw [show (twin T).s * T.s=1 from inv_mul_cancel (T.s),det_i] at h
 unfold veer; revert h;cases detX (twin T).s <;>cases detX T.s<;>decide
lemma flick_holds (h:InTest K true S false f):
 InTest K true (S.image T.motion) false (flick T f):=inSuede T _ _ (spinZ (veer T) (twin T).s) h

lemma flick_scale(z:ℂ):flick T (z • f)=z • flick T f:=suede_scale ..
lemma flick_sub(g:Buffered.Family K):flick T (f-g)=flick T f - flick T g:=funext fun _=>funext fun _=>map_sub _ _ _

lemma flick_money{a:ℝ}(p:pay f a):pay (flick T f) a:=by
 have e{N:Side}(b:Bool)(U:UNI (Single N))(x:FC (Single N)): ‖lotB b b U x‖=‖x‖:=by
    cases b
    · change ‖twist (quantU U) x‖=‖x‖;rw [twist_norm]
    change ‖theta U (cc x)‖=‖x‖
    unfold theta; rw [twist_norm,norm_cc,norm_cc]
 intro n v
 unfold flick suede
 rw [e];apply p

variable {n:Side}
open Reed
open BProof.Bide
lemma paidFlick (h:InTest K true S false f):
 (flick T f) n= hmMark T (f n):=by
 funext W
 unfold hmMark voltaM flick suede
 rw [inv_inv]
 have e:flashA (Levier.ray (N:=K.c n) (veer T) T) = stir (xtra (veer T)) T:=funext (stir_e T (veer T))
 rw [voltaF,e, ←tunnel_choice]
 apply Eq.symm
 apply hono _ _ _
 exact Chord.keys_of_chord (Chord.full ((h.support n).allV _).sector)


variable {I:Type*}{l:Filter I}
lemma Q.tangle {F:I→Buffered.Family K} (h:Q l S F f):
 Q l (S.image T.motion) (fun i=>flick T (F i)) (flick T f):=by
 obtain ⟨a,d,c,z⟩:=h.budget
 exact ⟨fun i=>flick_holds T (h.goes i), flick_holds T h.toBe,
  ⟨a,d,flick_money T c,z.mono (fun i=>flick_money T)⟩, fun e t=> (h.car e t).mono fun i b=>by rw [←flick_sub];exact flick_money T b⟩ -- bracket budget nesting

lemma Bolt.tangle {N:I→Side}{n:I→Side}{e:∀i,K.c (n i)=N i}
 {Y:(i:I)→Mark (N i)}{F:I→Buffered.Family K}
 (a:Bolt l S n e Y F f):
 Bolt l (S.image T.motion) n e (fun i=>hmMark T (Y i)) (fun i=>flick T (F i)) (flick T f):=by
 refine ⟨a.queue.tangle T,?_⟩
 have h:=a.sees; have p:K.c∘n=N:=funext e;subst N
 intro i
 exact (paidFlick T (a.queue.goes i)).trans (congrArg (hmMark T) (h i))
