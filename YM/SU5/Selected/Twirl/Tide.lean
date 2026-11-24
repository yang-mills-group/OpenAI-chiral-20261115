import YM.SU5.Selected.Airy.Income
import YM.CF.Lattice.Reference
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Topology Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset Fock Rush Lat
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
local instance : CompactSpace grounds:= isCompact_iff_compactSpace.mp groundsCompact
-- assemble unnormalized spine first. `Coined` expects covector Leg with bound 1 => scale later.
variable (N:Side) (n p:ℕ)(G D:Side)(g:8≤G.val)(e:n≥4)
local notation "Y"=> artisans G n p e
local notation "V"=> plinth G n p e
local notation "Fp"=>children G n p
local notation "ρ"=> Real.exp (-(1/2))

-- Additional lane reserve for maintaining punctuality between TWO different Frames.
def harbor (n p:ℕ):= n + 3*p
abbrev depthL (n p:ℕ)(k:ℤ):Prop := n ≤ k ∧ k ≤ (↑(n+ harbor n p):ℤ) -- lower + lane length
abbrev depthE (n p:ℕ)(k:ℤ):Prop := - (harbor n p:ℤ) ≤ k ∧ k ≤ 0
abbrev lateR (n p w:ℕ)(i:SpinIdx)(x: Cover):Prop:= Piece x w ∧ i=2 ∧ depthL n p (-(x 3))
abbrev earlyR (n p w:ℕ)(i:SpinIdx)(x:Cover):Prop:= Piece x w ∧ (i∈ plusHalf → depthE n p (-(x 3)))
structure TideFrame {G:Side} (n p:ℕ)(X Z: Coast→Wq p)(D:Side)(w:ℕ)(δ η C:ℝ): Prop where
    late : ∀ i j, Color (lateR n p w i) (fun t=> X t i j)
    early : ∀ i j, Color (earlyR n p w i) (fun t=> Z t i j)
    ticket : ∀ᶠ M:Jill.Male in mtn,∀ (N:Side){v:Type}[Fintype v][DecidableEq v],∀ (x:v→ Site N×Fin p), Beacons G D p x→
       let F':= hire p X x; let V':= hire p Z x; ‖F'‖ ≤ C∧‖V'‖ ≤ C∧‖F'ᴴ * V'-1‖ ≤ δ ∧ ‖(1-tip N M)* V'‖≤ η

variable {N G n p D} {δ ε R:ℝ}{w:ℕ}{X Z:Coast→ Wq p}
lemma Frame.havens (p':Frame (G:=G) n p X Z D w δ ε R): TideFrame (G:=G) n p X Z D w δ ε R:=by
 refine ⟨fun i j=> Color_mono (p'.late i j) ?_,fun i j=> Color_mono (p'.early i j) ?_,p'.ticket⟩
 · rintro x ⟨b,i,r⟩; refine ⟨b,i,?_⟩; rw [r]; unfold depthL strikeL harbor; omega
 rintro x ⟨b,r⟩; refine ⟨b,fun t=>?_⟩; obtain ⟨a,f⟩:=r t; rw [f]; unfold depthE strikeE harbor; omega
variable (h:TideFrame (G:=G) n p X Z D w δ ε R){v:Type}[Fintype v][DecidableEq v](x:v→ Site N×Fin p)
include h
lemma TideFrame.turnY (a:SpinIdx)(y:Site N)(i:v) (p':hire p Z x (y,a) i≠0): ∃ k:Cover, y=(x i).1+wrap N k ∧ Piece k w ∧ (a∈plusHalf→ depthE n p (k 3)):=by
 unfold hire at p'; rw [mask_mem,← Prod.eta (p:=x i)] at p'; obtain ⟨k,⟨t,f⟩,hz⟩:= leaves y _ _ _ (h.early a (x i).2) p'
 refine ⟨-k,?_,?_,?_⟩; · rw [hz,map_neg,sub_eq_add_neg]
 · exact fun i=> (Int.natAbs_neg _).trans_le (t i)
 intro u; exact f u
lemma TideFrame.turnX (a:SpinIdx)(y:Site N)(i:v) (p':hire p X x (y,a) i≠0): ∃ k:Cover, y=(x i).1+wrap N k ∧ Piece k w ∧ a=2∧ depthL n p (k 3):=by
 unfold hire at p'; rw [mask_mem,← Prod.eta (p:=x i)] at p'; obtain ⟨k,⟨t,f,l⟩,hz⟩:= leaves y _ _ _ (h.late a (x i).2) p' -- ⟨t,⟨f,l⟩⟩ autosubst
 refine ⟨-k,?_,?_, f,l⟩; · rw [hz,map_neg,sub_eq_add_neg]
 exact fun i=> (Int.natAbs_neg _).trans_le (t i)
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms TideFrame.turnY
#print axioms TideFrame.turnX
#print axioms Frame.havens

