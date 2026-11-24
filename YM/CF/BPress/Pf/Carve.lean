import YM.CF.BPress.Pf.Resolve
/- Costs of linear systems near the hole bound. Letter matrices arbitrary in the actual tilted/cut budgets. Derive 
after those strong estimates; constants may depend on both gaps (not required to make contraction small). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Pf
open Function Filter NormedSpace Finset Fock Branch Spin Spin.Quad Spin.Cellar Spin.Cellar.Pass Spin.Pledge
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
namespace Serve
variable {c d r:ℝ}
variable {I D Y:Type}[Fintype Y][DecidableEq Y][Fintype I][LinearOrder I][Nonempty I][TopologicalSpace D]{b:Stage Y I D Empty}
def tollP (T E:Pledge):Pledge:=(((T.times E).times (unary.plus T)).times E).times T
def compression (T E:Pledge):Pledge:=(T.times E).times T
lemma loss_p {P C:Raw D I} {T E:Pledge}(p:T.Costs b P)(g:E.Costs b C): (tollP T E).Costs b (fun i=>lost (P i) (C i)):= Costs.mul (Costs.mul (Costs.mul (Costs.mul p g) (Costs.sub Costs.one (Costs.stars p))) (Costs.stalk g)) p
lemma compress {P C:Raw D I} {T E:Pledge}(p:T.Costs b P)(g:E.Costs b C): (compression T E).Costs b (fun i=>cutC (P i) (C i)):= Costs.mul (Costs.mul p g) (Costs.stars p)
lemma rain (V:Pledge)(T:Pledge)(h:0≤r)(u:r<1)(v:0≤d) :∃ U:Pledge,∀ {I D Y:Type}[Fintype Y][DecidableEq Y][Fintype I][LinearOrder I][Nonempty I][TopologicalSpace D]{b:Stage Y I D Empty}{P C:Raw D I}, Capacity b d→ V.Costs b P→T.Costs b C→ (∀ x, Bore (P x) (C x) r) →U.Costs b (fun x=>dislodge (P x) (C x)):=by
 obtain ⟨R,p⟩:= (unary.plus (tollP V T)).invertible v (show 0<1-r^2 by nlinarith); refine ⟨((compression V T).times R).times V,?_⟩; intro I D Y _ _ _ _ _ _ b B C f P W L
 have ht:= p f (Costs.sub Costs.one (loss_p P W)) (fun x=> (L x).robust); exact Costs.mul (Costs.mul (compress P W) (Costs.stars ht)) (Costs.stars P)
lemma light_f (P L A:Pledge)(p:0<c)(v:0≤d): ∃ F G H:Pledge,∀ {I D Y:Type}[Fintype Y][DecidableEq Y][Fintype I][LinearOrder I][Nonempty I][TopologicalSpace D]{b:Stage Y I D Empty}{T K S U: Raw D I}, Capacity b d→P.Costs b T→L.Costs b S→A.Costs b U→(∀ x, Pass (T x) (K x) (S x) (U x) c)→ F.Costs b (fun x=> flatten (T x) (U x))∧ G.Costs b (fun x=> rebound (T x) (S x) (U x)) ∧ H.Costs b (fun x=> ramp (S x) (T x) (U x)):=by
 let X:= A.times P; obtain ⟨V,t⟩:= Trans.value _ p v P X; let Z:=A.plus V; obtain ⟨H,u⟩:= Trans.value _ p v Z (L.times Z); refine ⟨(V.times V).times P,Z.times H,H,?_⟩; intro I D Y _ _ _ _ _ _ b T K S U k l m n B
 obtain ⟨_,_,a,h⟩:= t k (fun i=>(B i).gate1) l (Costs.mul n l); let A₀:=fun i=>rent0 (T i) (U i); have he: Z.Costs b A₀:=Costs.sub n h; obtain ⟨_,_,t,U⟩:= u k (fun i=>(B i).gate0) he (Costs.mul m he); exact ⟨Costs.mul (Costs.mul h (Costs.stalk a)) l, Costs.mul he t,U⟩
lemma price_all (P Q L A C M:Pledge)(p:0<c)(v:0≤d)(r:ℝ)(h:0≤r)(u:r<1) :∃ W:Pledge,∀ {I D Y:Type}[Fintype Y][DecidableEq Y][Fintype I][LinearOrder I][Nonempty I][TopologicalSpace D]{b:Stage Y I D Empty}{T K S U J: Raw D I}, Capacity b d→P.Costs b T→Q.Costs b K→L.Costs b S→A.Costs b U→C.Costs b J→ (∀ x, Pass (T x) (K x) (S x) (U x) c)→ (∀ x, PairBoard (T x) (K x) (S x) (J x))→(∀ x, Bore (ramp (S x) (T x) (U x)) (J x) r)→ ∀{X Y':Raw D I}, M.Costs b X→M.Costs b Y'→ W.Costs b (fun i=> fitP (T i) (K i) (S i) (U i) (J i) (X i) (Y' i))∧ W.Costs b (fun i=>fitW (T i) (K i) (S i) (U i) (J i) (X i) (Y' i)):=by
 obtain ⟨F₁,F₂,Z,f⟩:=light_f P L A p v; obtain ⟨G₁,G₂,Z',g⟩:= light_f Q L (unary.plus A) p v; obtain ⟨H,t⟩:=rain Z C h u v; let U:=F₁.times M; let V:=G₁.times M; let D':=(L.times (M.plus V)).plus (C.times (L.times (M.plus U))); let E:=H.times D'; let W:=D'.plus (C.times E); let X':=U.plus (F₂.times E); let Y':= V.plus (G₂.times W); refine ⟨X'.bond Y',?_⟩; intro I D Y _ _ _ _ _ _ b T K S X Z a T0 K0 S0 X0 Z0 s c' r x y hx hy
 obtain ⟨p',l,g'⟩:= f a T0 S0 X0 s; obtain ⟨q',t',_⟩:= g a K0 S0 (Costs.sub Costs.one (Costs.stars X0)) (fun i=>Dual.dualPass (c' i) (s i));
 -- same h/h' purchases along all comparisons.
 have hu:=Costs.mul p' hx; have hv:=Costs.mul q' hy
 have hk : D'.Costs b (fun i=> capw (T i) (K i) (S i) (X i) (Z i) (x i) (y i)):= Costs.sub (Costs.mul S0 (Costs.sub hy hv)) (Costs.mul (Costs.stars Z0) (Costs.mul S0 (Costs.sub hx hu)))
 have he' := Costs.mul (t a g' Z0 r) hk; have hm : W.Costs b (fun i=> find_w (T i) (K i) (S i) (X i) (Z i) (x i) (y i)):= Costs.plus hk (Costs.mul (Costs.stars Z0) he')
 exact ⟨Costs.up (P:=X') (Costs.plus hu (Costs.mul l he')) (bond_lel ..), Costs.up (P:=Y') (Costs.plus hv (Costs.mul t' hm)) (bond_ler ..)⟩
end Serve
end YM.CF.BPress.Pf
