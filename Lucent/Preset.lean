import Lucent.Fair
import Lucent.Toccata
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.Lucent
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Buffered Buffered.Lifted Skye MeasureTheory NormedSpace
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Ballad EmberWind Window Lamour.Bridge Celeste
open WakeInvestment

open Peaks Scree
open Pannier.Chancel Py.Rate.Pannier
open Cube Laic Buffered.Afterglow Journey Dial
open Rous Pressure Worth
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
variable (s i k:ℕ)
set_option quotPrecheck false
local notation "■" => RootBook Y i k s
local notation "ℕ'" => side Y i s
local notation "flatP" => Dial.spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
open Buffered.Afterglow
open Window Cliplet

open Gist Kea
open Onyx
variable {I:Type}[Fintype I]


/-- Paint No. 1. every staff registers both kinds of comparators,
with dust required only between compared emitted colors of each monomial. -/
structure FieldPlan (I:Type) where
  hands:I→Hand
  roles:I→Role
def Dusty (d:FieldPlan I)(S:Stencil I) := ∀ b∈S.out,Dust d.hands b.flash
def faq (d:FieldPlan I)(S:Stencil I):ℂ:=S.quote (heed (fair d.hands) (aria d.roles))
/-- stencil scale at gauge pixels R -/
def maxZoom (R:ℝ)(m d:ℕ):ℂ:= ((R:ℂ)^2)^m * ((R:ℂ)^3/16)^d
def qr (W:I→Staff)(ρ R t:ℝ)(S:Stencil I)(m d r:ℕ):Papal.Weaver:= maxZoom R m d • kite r ρ t W S

structure OnScale (d:FieldPlan I)(W:ℕ→I→Staff)(R:ℕ→ℝ)(r:ℕ→ℕ):Prop where
    gauge: FairRoad W R d.hands
    body: ∀ n, Lucent.body (W n)=upstairs d.roles
    matchRise: Twah.riseUp (fun n=>rostrum (W n)) r (outside d.roles)
    grouping: Twah.plateau (fun n=>rostrum (W n)) (outside d.roles)

variable {ss ii kk r:ℕ→ℕ}{ρ R:ℕ→ℝ}{W:ℕ→I→Staff}{d:FieldPlan I}
local notation "ν" n:max => side Y (ii n) (ss n)
local notation "■R" n:max => (RootBook Y (ii n) (kk n) (ss n))

structure ToWick (ss ii kk:ℕ→ℕ)(ρ R:ℕ→ℝ)(r:ℕ→ℕ):Prop where
    yspin:Yard (fun n=>side Y (ii n) (ss n)) (fun n=>(r n:ℝ))
    warp: Yard (fun n=>More (side Y (ii n) (ss n))) R
    fitting:Tendsto (fun n=>R n / (r n:ℝ)) atTop (𝓝 2)
    pad:∀ n,Kea.Pad P.K.j (side Y (ii n) (ss n))
    exactG:Tendsto (fun n=> reachCost Y (ss n) (ii n) (kk n) (ρ n)) atTop (𝓝 1)
variable (Z:ToWick Y ss ii kk ρ R r)(T:OnScale d W R r)
include Z T
local notation "pressing" n:max => press Y (ss n) (ii n) (kk n) (W n)
lemma pressScaled (L:List (Loop I)): Tendsto (fun n=> ((R n:ℂ)^3/16)^L.length * (pressing n) L) atTop (𝓝 (aria d.roles L)):=by

 have h:=pressWake (kk:=kk) Y Z.yspin Z.pad T.body T.matchRise T.grouping L
 have v:=(((Z.fitting.ofReal.pow 3).div_const (16:ℂ)).pow L.length).mul h
 rw [show (↑(2:ℝ):ℂ)^3/(16:ℂ)=1/2 from by norm_num] at v
 apply v.congr; intro n; rw [←mul_assoc,←mul_pow]; have he:(r n:ℂ)≠0:= by exact_mod_cast (Z.yspin.pos n).ne'
 push_cast
 field_simp

omit Z T in
lemma quote_road (S:Stencil I){h:Join I→ℂ}{G:ℕ→ℂ}{f:ℕ→Join I→ℂ}
    (p:∀ b∈S.out,Tendsto (fun n=> G n*f n b.toJoin) atTop (𝓝 (h b.toJoin))):
    Tendsto (fun n=> G n*S.quote (f n)) atTop (𝓝 (S.quote h)):=by
 cases S with|mk L=>induction L with
 | nil=>simp [Stencil.quote]
 | cons b L ih=>
    simp_rw [Stencil.cons_q,mul_add]
    exact (((p b List.mem_cons_self).const_smul b.k).congr fun i=> (mul_smul_comm ..).symm).add (ih fun b' hb'=>p b' (List.mem_cons_of_mem b hb'))

theorem answered (m a:ℕ)(S:Stencil I)
    (g:S.degree m a)(q:Dusty d S):
    Tendsto (fun n=> maxZoom (R n) m a * dontStop Y (ss n) (ii n) (kk n) (W n) (ρ n) S)
      atTop (𝓝 (faq d S)):=by
 simp_rw [breath_bill]
 unfold faq; apply quote_road; intro b t
 obtain ⟨u,v⟩:=g _ t
 have e:=vellFare Y Z.warp T.gauge Z.exactG b.flash (q _ t)
 have f:=pressScaled Y Z T b.loom
 rw [v] at f; rw [u] at e
 apply (e.mul f).congr; intro n; unfold heed maxZoom; ring
#print axioms answered
