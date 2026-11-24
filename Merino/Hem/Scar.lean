import Merino.Cuff.Ink
import YM.RG.Bounded
set_option autoImplicit false
noncomputable section
namespace YM.CF.Merino.Hem
open Cuff MeasureTheory RG
open Function Finset Lattice Wilson
open scoped InnerProductSpace Topology
variable {G:Gauge}{N:Side}

/-- All face chords strict. Matches Scree.pingS without that import. -/
def Lave (τ:ℝ)(X:Support N)(V:Config G N) :=
   ∀ i: Face (Per N), ¬Disjoint X (touched i) → G.chord (faceValue V i)<τ
/-- Slack between inspection and polynomial reach. -/
def slim(m:ℕ):=m-(m/15)
lemma slim_le (m): slim m≤m:=Nat.sub_le ..
abbrev Bundle (G:Gauge)(N:Side):=Inky (Husk G N)
abbrev Yardlet (N:Side)(m:ℕ): Support N :=halo m {0}
/-- Origin stencil. m single radius in gauge units, τ passing threshold,
r chart radius, C a combined cost (even through fails), E cubic supplement. -/
structure Scar (m:ℕ)(τ r C E:ℝ)(f:Config G N→ℂ)(T:Bundle G N):Prop where
 cloth : Sheath 0 (slim m) C T
 bound (V): ‖f V‖≤C
 readable : Measurable f
 region : LocalOn (Yardlet N m) f
 sang : GaugeInvariant f
 debt (V) (Y:Directions G N): ‖Y‖≤r →
  Lave τ (Yardlet N m) V → Agrees (Yardlet N m) V (increment 1 Y) →
   ‖f V-(dripQ T (cseed Y) (cseed Y):ℂ)‖≤ C*‖Y‖^3+E
