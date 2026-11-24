import Organdy.Filigree
import Organdy.Velvetina
import Organdy.Sceptre
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra

open _root_.Zephyr.Chern
open Vale Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Yoke Yoke.Bazaar
open Optic Larva -- remove

namespace Royal
open Buffered.Afterglow Satin Journey Tower

/- What we buy. Package constants. -/
structure Cuts where
 a:ℝ
 b:ℝ
 r:ℝ
 cost:ℝ
 γ:ℝ
 m:ℕ
 a':ℝ
 b':ℝ
 D:ℝ
 δ:ℝ
 w:ℕ
 f:ℝ→ℝ
 g:ℝ→ℝ
abbrev Cuts.legacy (P:Spine)(c:Cuts) :Prop:=
 Carnival P c.m c.a c.b c.a' c.b' c.D c.δ c.r c.cost c.γ c.w c.f c.g

structure Stores where
 M:ℕ
 v:ℕ
 L:Side
 Ψ:ℝ→ℝ
 Φ:ℝ→ℝ
 α:ℝ
abbrev Stores.lease (P:Spine)(c:Cuts)(d:Stores) :Prop:=
 SignedLease P d.M d.L (moveFare c.f) (moveFare (scaledBirth P c.g)) d.Ψ d.Φ d.v

abbrev guineas (P:Spine)(s:ℕ) := Vale.hat P.par.R.L P.par.x s
abbrev shaft (P:Spine)(s:ℕ) := Pressure.radiusB (guineas P s)
abbrev station (P:Spine)(s:ℕ) := mortise (shaft P s)
abbrev glowB (P:Spine)(s:ℕ) := Pressure.temp (guineas P s)
-- stock 
abbrev kitGap (P:Spine)(s i:ℕ):=age P.run i s

abbrev fast(P:Spine)(s i k:ℕ):=(RootBook P.run i k s).p
abbrev tie(P:Spine)(s i:ℕ):=(P.run.voyage i).CapeT s

/-- simultaneous price ticket and Kyanite, origin and all translates -/
structure Seating (P:Spine)(c:Cuts)(d:Stores)(s i k:ℕ):Prop where
 reef: Reef P i k s c.m c.w d.v d.M d.L c.a c.b c.a' c.b' c.D c.δ c.f c.g d.Ψ d.Φ d.α
 fil: Filigree P i k s c.m c.a c.b c.r c.cost c.γ
 stock: Tower.Tivoli (station P s) (kitGap P s i)

structure Suit (N:Side) where
 X:SOp N
 Y:SOp N
 J:Axis→SOp N
 T:Axis→SOp N
 V:Sour.Bag N

variable {P:Spine}{s:ℕ}{I:Type}
abbrev sealed (c:Cuts)(i k:ℕ)(X:Suit (kitGap P s i)):=
 Agate P i k s c.m 0 c.a c.b c.f c.g X.J X.T X.X X.Y X.V
lemma Seating.fits{c d i k}(b:Seating P c d s i k):
 ∃ X:Suit (kitGap P s i),sealed c i k (s:=s) (P:=P) X:=
 let ⟨j,t,x,y,v,h⟩:=b.reef.opening 0
 ⟨⟨x,y,j,t,v⟩,h⟩

abbrev Suits (P:Spine)(s:ℕ)(i:I→ℕ):= ∀ z,Suit (kitGap P s (i z))


abbrev Gallon (l:Filter I)(P:Spine)(s:ℕ)(i:I→ℕ)(S:Finset Cover):=
 Bolt l S (moment P s i) (patronise P s i)
abbrev PackE(I:Type)(P:Spine):=Pin→I→Buffered.Family P.calibration
abbrev Lot(P:Spine):=Pin→Buffered.Family P.calibration
abbrev modal (P:Spine)(c:Cuts)(s i k:ℕ)(q:Suit (kitGap P s i)) :=
 tooled (tie P s i) (fast P s i k) q.X q.J c.m
structure Parade(l:Filter I)(P:Spine)(c:Cuts)(d:Stores)(s:ℕ)(i k:I→ℕ)
 (X:Suits P s i)(F:PackE I P)(x:Lot P):Prop where
 rate:RateNet l P i k
 vintage (v:I):Seating P c d s (i v) (k v)
 slot (v:I):sealed c (i v) (k v) (P:=P) (s:=s) (X v)
 pins (j:Pin):
    Gallon l P s i (station P s) (fun v=>modal P c s (i v) (k v) (X v) j) (F j) (x j) ∧
    (∀ v,Plumage (F j v)) ∧ Plumage (x j)
 pure (j:Pin): j=.stone∨j=.horn → (∀ v,Cello (station P s) (F j v)) ∧ Cello (station P s) (x j)

lemma invited
 {u:Ultrafilter I}{c:Cuts}{d i k} (b:c.legacy P)
 (q:RateNet (↑u:Filter I) P i k)
 (w:∀ z, Seating P c d s (i z) (k z)):

 ∃ X F x, Parade (↑u:Filter I) P c d s i k X F x:=by
 let j:=b.1.1
 choose X a using fun z=>(w z).fits
 let H(z):=(a z).toSquid.toKit
 let r(z):=(w z).reef.clearing
 let β:=shaft P s
 let v(z):=(r z).stages

 obtain ⟨z,_⟩:=(Eventually.of_forall (f:=(↑u:Filter I)) fun _=>True.intro).exists
 have c₀:Bezel (N:=tunnel P s i) c.a c.b P.par.d (glowB P s) β c.m
     (fun z=>fast P s (i z) (k z)) (fun z=>tie P s (i z)) 
     (fun z=>(X z).X) (fun z=>(X z).J):=
    ⟨⟨j.slope.le,j.cost.le,P.par.dpos,(fun v=> (r v).radius),fun t=> (r t).sphere,
      fun t=>dressing (v t),fun t=> (H t).knot⟩,v,fun t=>(H t).medal,
     fun t=>by
        obtain ⟨A,G⟩:= ((w t).fil.classic _ _ _ _ (H t)).1
        have a:=G.plate
        rw [(r t).radius] at a
        exact ⟨_,_,_,_,_,a⟩,
    le_trans (r z).lot (r z).radius.le⟩
 obtain ⟨F,x,p0,y⟩:=fundedPins c₀ (moment P s i) u (fun t=>(w t).stock) (patronise P s i)
 exact ⟨X,F,x,q,w,a,p0,y⟩

def arrivals(P:Spine)(c:Cuts)(d:Stores)(s:ℕ):Prop:=
 ∃ (i k:Pair→ℕ),∃ X F x, Parade (↑session:Filter Pair) P c d s i k X F x ∧
    ∀ᶠ z in (↑session:Filter Pair), i z=P.period z.1 ∧ k z=P.cutoff z.2

lemma halls {c:Cuts}(x:c.legacy P) (M v:ℕ)(L:Side):
 ∃ Ψ Φ α, let d:Stores:=⟨M,v,L,Ψ,Φ,α⟩
          d.lease P c ∧ ∀ᶠ s in atTop,∀ᶠ i in atTop,∀ᶠ k in atTop, Seating P c d s i k :=by
 obtain ⟨Ψ,Φ,α,a,b⟩:=x.2.2.2.2 M v L
 refine ⟨Ψ,Φ,α,a,?_⟩
 filter_upwards [b] with s t
 filter_upwards [t,Tower.turning P.run P.large s (station P s)] with i r q
 filter_upwards [r] with k z
 rw [terrain P.run P.large (P.run.ir i) s] at q
 exact ⟨z.1,z.2,q⟩

lemma exposed {c:Cuts}(x:c.legacy P)(M v:ℕ)(L:Side):
 ∃ Ψ Φ α, let d:Stores:=⟨M,v,L,Ψ,Φ,α⟩
          d.lease P c ∧ ∀ᶠ s in atTop,arrivals P c d s:= by
 obtain ⟨Ψ,Φ,α,y,b⟩:=halls x M v L
 refine ⟨Ψ,Φ,α,y,b.mono fun s h=>?_⟩
 obtain ⟨i,k,q,w,t⟩:=booking (P:=P) h
 obtain ⟨X,F,v,b⟩:=invited (u:=session) x q w
 exact ⟨i,k,X,F,v,b,t⟩

#print axioms exposed
