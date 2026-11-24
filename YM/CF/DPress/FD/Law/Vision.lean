import YM.CF.DPress.FD.Law.Together
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.DPress.FD
open Function Set Filter Finset Lattice Cash
open scoped Topology BigOperators ENNReal NNReal Classical
variable {I J K:Type*}[Fintype I][Fintype J][Fintype K]{n:Side}{r d:ℕ}
abbrev Far (r:ℕ)(S T:Support n):Prop:= ∀ i∈S,∀ j∈T,r < separation i j
theorem Far.down {S T V W:Support n}(h:Far r S T)(t:d ≤ r)(s:V ⊆ S)(u:W⊆T):Far d V W:=fun i x j y=>t.trans_lt (h i (s x) j (u y))
structure Vision (n: Side)(r:ℕ) (I: Type*)[Fintype I] where
 c : Cash I
 set(S:Support n): Setoid I
 dim : ∀ S T:Support n,Far r S T → c.Pair (set S) (set T)
 le : ∀ S T:Support n,S⊆T→∀ x y:I,(set T).r x y→(set S).r x y
namespace Vision
variable (V:Vision n r I)
abbrev looks(S:Support n) (x y:I):Prop:= (V.set S).r x y
abbrev idT {Y:Type*}(f:I→Y)(D:Support n):Prop:= Holds f (V.set D)
lemma grow {Y: Type*}{S T:Support n}{f:I→Y}(h: S⊆ T)(p:idT V f S):idT V f T:= fun i j u=> p i j (V.le S T h i j u)
abbrev rearm (p:r ≤ d): Vision n d I:=⟨V.c, V.set,fun S T f=> V.dim S T (f.down p (Finset.Subset.refl _) (Finset.Subset.refl _)),V.le⟩ -- type def.
abbrev pair (W:Vision n r J): Vision n r (I×J):=⟨V.c.duo W.c,fun S=> Cash.join (V.set S) (W.set S),fun S T f=> Pair.joinT V.c (V.dim S T f) (W.dim S T f),fun S T f i j u=> ⟨V.le S T f i.1 j.1 u.1,W.le S T f _ _ u.2⟩⟩
abbrev bunch [DecidableEq I] {K:I→Type*}[∀ i,Fintype (K i)](V:∀ i,Vision n r (K i)):Vision n r ((i:I)→K i):=⟨Cash.pi (fun i=>(V i).c),fun S=> allT fun i=>(V i).set S,fun S T f=> pity _ (fun i=>(V i).dim S T f),fun S T f i j u p=> (V p).le S T f _ _ (u p)⟩
-- independent array attached to given site (or use any center for attaching footprints of cells). for other support allows no reads.
abbrev harsh (T:Site n)(C:Cash I):Vision n r I:=⟨C,fun S=> if T∈S then ruleFx id else Keep I,by
 intro S X v; by_cases h:T∈X; swap; · rw [if_neg h]; exact swiv C _
 have hp:T∉S:=fun l=> by have ht:= v T l T h; rw [separation_self] at ht; omega
 rw [if_neg hp]; exact Pair.sym C (swiv C _), fun S X v i j h=>by
 by_cases t:T∈ S; rw [if_pos t]; rw [if_pos (v t)] at h; exact h
 rw [if_neg t]; exact True.intro⟩
abbrev trim : Vision n r (Up V.c):=⟨V.c.permit,fun S=> liftF V.c (V.set S),fun S T v=>Pair.liftF_P V.c (V.dim S T v),fun S T v x y h=>V.le S T v _ _ h⟩
end Vision
end YM.CF.DPress.FD
