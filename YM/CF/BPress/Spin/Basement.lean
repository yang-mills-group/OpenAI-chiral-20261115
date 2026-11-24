import YM.CF.BPress.Spin.Stoop
import YM.CF.BPress.Spin.Pledge
/-! Extra support costs on lifted data. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Spin
open Function Filter NormedSpace Finset Fock Branch Dial Pledge Cellar Cellar.Pass
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace
attribute [local instance] opCStarAlgebra
namespace Basement
variable {Y I D:Type}[Fintype I][DecidableEq I][Nonempty I][TopologicalSpace D][Fintype Y][DecidableEq Y] {b:Stage Y I D Empty}{c:ℝ}
/- projections and paths can use a simple variation parameter (units)
 in monotone stage. include derivatives of slide for later. -/
def slopeP1 (Q L: Op I)(u:ℝ):=L+(2*u) • Q
def slip (P Q L A:Op I)(u:ℝ):=slopeP1 Q L u*rent1 P A+ Q*rent0 P A

def relay (Q:Pledge):Pledge:= (unary.scales 1).times Q

def c1Price (P Q L:Pledge):= (P.plus (relay L)).plus (relay (relay Q))
def c0Price (Q L:Pledge):= L.plus (relay Q)
def d1Price (Q L:Pledge):= L.plus ((relay Q).scales ‖(2:ℝ)‖)

structure Share (P:Pledge)(b:Stage Y I D Empty)(B C L A:Raw D I)(v:D→ℝ): Prop where
 ray1 : P.Costs b (fun i=> rent1 (B i) (A i))
 ray0 : P.Costs b (fun i=> rent0 (B i) (A i))
 rump : P.Costs b (fun i=> ramp (L i) (B i) (A i))
 share : P.Costs b (fun i=> slide (B i) (C i) (L i) (A i) (v i))
 shear : P.Costs b (fun i=> smoothP (B i) (C i) (L i) (A i) (v i))
 incline : P.Costs b (fun i=> slip (B i) (C i) (L i) (A i) (v i))
 strat : P.Costs b (fun i=> Trans.pinv (A i) (slide (B i) (C i) (L i) (A i) (v i)))

private lemma integral(P Q W U L X Y:Pledge): ∃ R:Pledge,P≤R∧Q≤R∧W≤R∧U≤R∧L≤R∧ X≤R∧Y≤R:=by
 -- destruct? simple
 let a:= P.bond Q; let b:=W.bond U; let c:= L.bond X
 let d:= a.bond b; let e:= c.bond Y; let f:=d.bond e
 have he:d≤ f:= Pledge.bond_lel ..; have hh:e≤ f:=bond_ler ..; exact ⟨f,(bond_lel P Q).trans ((bond_lel a b).trans he),(bond_ler P Q).trans ((bond_lel a b).trans he),(bond_lel W U).trans ((bond_ler a b).trans he),(bond_ler W U).trans ((bond_ler a b).trans he),(bond_lel L X).trans ((bond_lel c Y).trans hh),(bond_ler L X).trans ((bond_lel c Y).trans hh), (bond_ler c Y).trans hh⟩
theorem funding (P Q W U:Pledge)(h:0<c)(C:ℝ)(p:0≤C): ∃ S:Pledge, ∀{Y I D:Type} [Fintype Y][DecidableEq Y][Fintype I][DecidableEq I][Nonempty I][TopologicalSpace D]{b:Stage Y I D Empty}
 (B E L A:Raw D I)(v:D→ℝ), Capacity b C→ (∀ x, Cellar.Pass (B x) (E x) (L x) (A x) c)→ P.Costs b B→Q.Costs b E→W.Costs b L→U.Costs b A→Trans.Tune b v 1→ Share S b B E L A v :=by
 obtain ⟨R,H⟩:= Trans.value c h p P (U.times P); let T:=U.plus R; obtain ⟨F,X⟩:= Trans.value c h p T (W.times T); let G:= ((c1Price P Q W).times R).plus ((c0Price Q W).times T); let D':=((d1Price Q W).times R).plus (Q.times T); obtain ⟨I,M⟩:= Trans.value ((magnet c)^2) (pow_pos (positivity_M h) _) p U G; obtain ⟨S,p₁,p₂,p₃,p₄,p₅,p₆,p₇⟩:= integral R T F G D' I I -- final duplicate identity
 refine ⟨S,?_⟩; intro Y I' D _ _ _ _ _ _ b B E L A v t hX bX eX lX aX T'
 let V(i:D):= Cellar.rent1 (B i) (A i); let Z(i:D):= Cellar.rent0 (B i) (A i); let N(i:D):= slide (B i) (E i) (L i) (A i) (v i)
 have hV:R.Costs b V:=(H t (fun i=>(hX i).gate1) bX (Costs.mul aX bX)).2.2.2
 have hZ:T.Costs b Z:=Costs.sub aX hV
 have hF:= (X t (fun i=>(hX i).gate0) hZ (Costs.mul lX hZ)).2.2.2
 have hg(C:Pledge)(φ:Raw D I') (h:C.Costs b φ) : Costs (relay C) b (fun i=>v i • φ i):= Trans.conducts T' h
 have hx :=hg _ E eX
 have he : (relay (relay Q)).Costs b (fun x=> v x^2 • E x):= by simp_rw [pow_two,mul_smul]; exact hg _ _ hx
 have hN:G.Costs b N:= Costs.plus (Costs.mul (Costs.plus (Costs.plus bX (hg W _ lX)) he) hV) (Costs.mul (Costs.plus lX hx) hZ)
 have hl : D'.Costs b (fun i=>slip (B i) (E i) (L i) (A i) (v i)):=by unfold slip slopeP1; simp_rw [mul_smul]; exact Costs.plus (Costs.mul (Costs.plus lX (Costs.scale hx _)) hV) (Costs.mul eX hZ)
 obtain ⟨_,_,iX,pX⟩:= M t (fun i=>(hX i).enjoy (v i) (T'.costs i)) aX hN; exact ⟨hV.up p₁,hZ.up p₂,hF.up p₃,hN.up p₄,pX.up p₆,hl.up p₅,iX.up p₇⟩
lemma slide_ray (P Q L A:Op I)(u:ℝ) : HasDerivAt (slide P Q L A) (slip P Q L A u) u:=by
 let f(x:ℝ):=x^2; have he:HasDerivAt f (2*u) u:=by convert! ((hasDerivAt_id' u).pow 2) using 1; simp; -- ((hasDerivAt_id' u).pow 2)
 have ht: HasDerivAt (coeff0 Q L) Q u:=by convert! ((hasDerivAt_id' u).smul_const Q).const_add L using 1; simp
 have hg : HasDerivAt (coeff1 P Q L) (slopeP1 Q L u) u:=by unfold slopeP1; nth_rw 2 [← one_smul ℝ L]; exact ((((hasDerivAt_id' u).smul_const L).const_add P).add (he.smul_const Q)) -- tune
 exact (hg.mul_const _).add (ht.mul_const _)
end Basement
end YM.CF.BPress.Spin
