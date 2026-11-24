import YM.CF.BProof.Shore.Fire
import YM.CF.BProof.Nest.East
import YM.CF.BProof.Stave.Coins
/-! Assembly – first for ANY tori satisfying commissions. Law to be generated later. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mesh.Shore
open Function Filter Metric Finset Lattice Wilson Nest Stave Gallery
open scoped Matrix Matrix.Norms.Frobenius Topology BigOperators NNReal Classical
-- setup plate borel not inferred; define scoped Shore instance
scoped instance pltm(I:Type*) : MeasurableSpace (plate I) := borel _
scoped instance pltb(I:Type*) : BorelSpace (plate I) := ⟨rfl⟩

variable {n:Side}{K:Type*}{S l q:ℕ}{u ε:ℝ}
structure Score (n:Side)(q:ℕ) where
 cur : Wool n q
 fine : Wool n q
 orderC : Vent n
 fire : Site n→ Bool

local notation "Sκ"=>Site n
abbrev Home:=SU.group
local notation "Z"=>Nerve.Halo
def gapR (l:ℕ):=2*(Z*l+1)+1
abbrev Radius(S l:ℕ):ℕ:=Wool.palm S+4*(gapR l)
namespace Score
variable (T:Tray (Floor q) ε)(A:Score n q)(U:Config SU.group n)
def Key(x:Sκ):=T.tag (A.fine.hue x) (A.fire x) (A.cur.native A.orderC U x)
variable (S l u)
def sound (x:Sκ):= Clear u (Radius S l) U x
local notation "Yκ"=> sound S l u U -- order?
def caught(x:Sκ): Prop:= ∀ i∈ A.fine.group x, sound S l u U i
def team (x y:Sκ) := (((A.fine.both x y).filter (sound S l u U)).image (Key T A U))
abbrev rollup(q:ℕ){ε:ℝ}(T:Tray (Floor q) ε) := Tray.Mint T.q (Fin q)
def tagger(x:Sκ):Pool (rollup q T):= bale (sound S l u U) (Key T A U) (A.fine.wheel x)
abbrev C₀(a:ℝ)(δ:ℝ) :ℝ:=5*Wool.cash a δ
structure Seal (g: Score n q)(S l:ℕ)(b a:ℝ) : Prop where
 small : Nerve.SmallN S n
 ch : g.cur.Rub S b
 mi : g.fine.Rub l a
-- requests assembly
structure Writ (q:ℕ){ε:ℝ}(T:Tray (Floor q) ε)(S l:ℕ)(u a b δ d θ:ℝ) (F: Gallery.Drum (rollup q T) (Floor q)) : Prop where
  pe : 0 < ε
  hC : 0 < S
  hδ : 0 < δ
  err : Nest.Law Home u δ (Nerve.King*S)
  fees : C₀ b δ * (4*(gapR l:ℝ)) ≤ θ - 2*ε -- snap both, gap.
  cost_a : 0 < θ
  cost_b : θ ≤ d
  cost_c : C₀ b δ ≤ d
  book : (T.house (Fin q)).Coat d 4 θ F
  gleam (V:Finset (rollup q T)) (p:(T.house (Fin q)).tonic θ V) (g:V.card≤4) (x y:Pool (rollup q T))(hx:Fuse V x)(hy:Fuse V y)(he:dist x y ≤ a) : dist (dummy F x) (dummy F y) ≤ d
end Score
end YM.CF.BProof.Mesh.Shore
