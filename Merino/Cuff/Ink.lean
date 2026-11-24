import Merino.Cuff.Parol
import YM.PCalc.Chart
set_option autoImplicit false
noncomputable section
namespace YM.CF.Merino.Cuff
open Function Finset Lattice Wilson
open scoped InnerProductSpace Topology
variable {G:Gauge}{N:Side}


abbrev Chips(G:Gauge):=G.ColorIndex
/-- Color coordinates in the probe/Wick comparisons. -/
abbrev dust {G:Gauge}(i:Chips G)(X:G.Color):ℝ:=X i
abbrev gem {G:Gauge}(i:Chips G):G.Color:=EuclideanSpace.basisFun (Chips G) ℝ i


lemma jewels(x:G.Color):x=∑ i:Chips G,dust i x • gem i:=by
 symm; simpa [gem,EuclideanSpace.basisFun_repr] using (EuclideanSpace.basisFun (Chips G) ℝ).sum_repr x
lemma gem_norm(i:Chips G): ‖gem i‖=1:= (EuclideanSpace.basisFun (Chips G) ℝ).norm_eq_one _

abbrev Stripe (G:Gauge):=PlaqAxes × Chips G -- macroscopic F
abbrev Husk (G:Gauge)(N:Side):=Face (Per N) × Chips G -- microscopic, torus
abbrev ridge {G:Gauge}{N:Side}(t:Husk G N):Stripe G:=(t.1.2,t.2)
abbrev cref {N:Side}(p:Face (Per N))(X:RG.Directions G N):G.Color:=
 Exterior.linkSum X p.1 (square p.2.val.1 p.2.val.2)
abbrev cseed (X:RG.Directions G N)(i:Husk G N):=dust i.2 (cref i.1 X)


/-- Face polynomial affordability at radius k. Square application needs +2.
Wick comparison may see *all* layers to k, so don't pay any factor of k in cost. -/
structure Sheath (o:Site N)(k:ℕ)(C:ℝ)(T:Inky (Husk G N)):Prop where
 flip:symmetric T
 rent:laden T≤C
 abode(i j:Husk G N): T i j≠0 → separation o i.1.1 ≤ k

lemma Sheath.both {o:Site N}{k:ℕ}{C:ℝ}{T:Inky (Husk G N)}(U:Sheath o k C T)
    {i j}(p:T i j≠0):
    separation o i.1.1≤k ∧ separation o j.1.1≤k:=
 ⟨U.abode _ _ p, U.abode _ _ (by rwa [U.flip])⟩
end YM.CF.Merino.Cuff
