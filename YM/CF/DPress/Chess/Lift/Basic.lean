import YM.CF.DPress.Chess.Lift.Vat
import YM.CF.Bloom.Flux
/-!
 boundary.Lift issued at any actual step. This is the exact deterministic linear pullthrough
 of Π tilt etc, not a vacuum-only expectation. Cost numbers before purchasing h (but include
 Mold.Shape). -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.DPress.Chess.Lift
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Fock Cube Lat Tenant Tulip Girt
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire Branch Brace Drapes Peaks Dial Tap Haro
variable {C P B L:Side}{j:ℕ}{ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{e u:ℝ}
 {G:Ratio (mid C B) (mid P B)} {R:Grasp Y B e}
 (h:G.count=L)(p:R.roundZ≤(mid C B).val)(t:0<e){X:Nom (mid C B) (mid P B)}(v:JointB G X e)
 (M:Tulip.Male) (Q:Haro.SpaceM)
include h p t v
lemma apt_H : Along j L ho (Thread j) true M G (unionP X) :=by
 obtain ⟨y,l⟩:= cue_from X.2; let Z:=starfish C B X.2 y; have he:=pose_g R t G h p X v Z (starK R.capY t.le v.cg l); exact (Y.cap G h (R.needed.trans p) M _ he.glyph).chart true
lemma beam_M (x: Phys (mid P B)) : beamZ (mid C B) (pathH G j M X Q.val x)= beamZ (mid P B) x:=by
 rw [pathH, show beamZ (mid C B) (scaleZ Q.val _) = _ from shoulderL ..]; exact ((Spire.shuttle G h p X v t M).2 _).trans (Fock.sigh (switchG G).symm.toEmbedding _ (shelfG ..) _ _)
structure Tag(j:ℕ)(N:ℕ)(L:Side):Prop where
 h :∀{a b:Side}(G:Ratio a b),G.count=L→∀ i:Male,Symbol.Stroke G (pulse G j i) N
omit h p t v
lemma realT (L:Side)(p:Odd L.val)(j:ℕ):∃ N:ℕ, Tag j N L:= (Symbol.Stroke.clothB j L p).imp (fun i h=>⟨h⟩)
end YM.CF.DPress.Chess.Lift
