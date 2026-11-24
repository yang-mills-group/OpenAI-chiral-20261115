import Merino.Footloom
set_option quotPrecheck false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 28000
noncomputable section
namespace YM.CF.Merino
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Drapes Metric
open _root_.Zephyr.Chern
open scoped Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Finset Swell

variable {n:Side}

open Py.Rate.LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Skye Scree Vale RG
open Py (hueW stemS pinpr)
variable (P:Spine)


/-- Economic terms of single-root purchase. Not indexed by height:
single constants and single cool functions. Width/radius/h/mesh
set by the target Spine and m. -/
structure Bolts where
 a: ℝ
 c: ℝ
 F: ℝ→ℝ
 D: ℝ→ℝ
 decay:0<a
 crown:0<c
 paying:BPress.NPL F
 birthing:BPress.NPL D


variable (s i k:ℕ)
local notation "N"=> RegNum P s i
local notation "K"=> LoomM P s i
local notation "R"=> LedgerM P s i k
local notation "q"=> P.par

variable (p:Bolts)(m:ℕ)

open Swell
local notation "T"=> Openc (More N) P.par.d
local notation "M"=> funde P.par.K.j (R).J.M N
local notation "pigment"=>Moire.bloom (R).J.P

/-- Store even the short decomposition witness *and* all
the pricing data, including a license to use the exact signed numerator
program and denominator. No assuming *a priori* identifications across tori. -/
structure Dress(o: Site N) where
  y : Spool N
  clips : Axis→SOp N
  selv : SOp N
  program : Sour.Bag N
  hot:Hot P s i k m
  here:y.origin=o
  leap:y.stepY=m
  /-- contact, price, physical license in one -/
  ticket:Tailoring P.par.U R K y p.a p.c P.par.d (hueM P s) P.par.J.n 24 P.par.h
     (rScale (R).p) program (p.F (scaleM P s)) (p.D (scaleM P s)*Qprice P s)
  echoes(i₀):Soak (node o) (clips i₀) p.a (loseM P p.a s*p.c) P.par.d
  wane:Soak (node o) selv p.a (loseM P p.a s*p.c) P.par.d
  spur_funds(i₀)(U:T): spur (millIntro M pigment) o i₀ m U.val=y.spin i₀ U.val+clips i₀ U.val
  glaze_funds(U:T): (M U.val-Dial.tickA N)*windmill o m=y.color U.val+selv U.val

/-- Master contract, unconditional when applied to our elected tuple. -/
def woven (P:Spine)(m:ℕ)(p:Bolts):Prop:=onReg P fun s i k=> ∀ o,Nonempty (Dress P s i k p m o)

variable (ro:P.Roster)(h:Compass_sol P.run)(t:RateStamp P.run)
include ro h t
theorem weave: ∃ p,woven P m p:=by
  obtain ⟨a,c,F,D,u,v,f,d,H⟩:=factorium P.run ro.prepared h t m
  refine ⟨⟨a,c,F,D,u,v,f,d⟩,?_⟩
  have z:=fired P h m; unfold onReg at z
  unfold woven onReg
  filter_upwards [H,z] with b l S
  filter_upwards [l,S] with j r e k g o
  have w:=e k g
  obtain ⟨A,C,X,Y,TJ,EC,TX,EY,hJ,hX,bag,bp⟩:=r k g.2 o
  have eq:loseM P a b=Real.exp (-a*((((LedgerM P b j k).p.B/10:ℕ)):ℝ)):=by rw [w.claims]
  refine ⟨⟨⟨o,m,A,X⟩,C,Y,bag,w,rfl,rfl,
    ⟨w.usable,⟨w.sky,u.le,TX,TJ⟩,w.yard,bp⟩,?_,?_,hJ,hX⟩⟩
  · have hE := EC; change ∀ i,Soak (node o) (C i) a (_ * c) _ at hE; rw [←eq] at hE; exact hE
  change Soak _ Y a (loseM P a b*c) _; rw [eq]; exact EY
end YM.CF.Merino
