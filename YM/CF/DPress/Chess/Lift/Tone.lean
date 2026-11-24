import YM.CF.DPress.Chess.Lift.Vat
import YM.CF.DPress.Chess.Lift.Fluor
/-! Use the cost before h from the compact time-range proof. Track generator lifts with full
 reflection at the two levels. `Q` for the physical lift, not a Borel choice after the pair of inputs is split. Create the lift on all weight evaluations. -/
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.DPress.Chess.Lift
open Function Filter Finset Lattice Rush Scroll Tulip Lat Peaks Cube Dial SU Branch Wilson Fock Fixed NormedSpace Spire Scree Skye Tap Reed Print
open scoped Topology BigOperators NNReal ENNReal Kronecker Classical Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {n m L:Side}(G:Ratio n m)(M: Male)(j:ℕ){o: Odd L.val}(Q:Op Slot)
abbrev CoverS(n:Side):= Support (More n)
abbrev ReOp(n:Side):= FC (Single n)
def RefineE (S:CoverS n)(b:Bool)(A:ReOp n): Prop:= Reed.Fine (upperIndices n) (matterRegion n S) b A
abbrev rise (A:ReOp n)(X:Nom n m)(B:ReOp m):Prop:= ∀ v:Phys m, acts A (pathH G j M X Q v)=pathH G j M X Q (acts B v)
abbrev WaveK(T K:Side):= Nom T K→ ReOp K
structure PrintU (S:CoverS m) (b:Bool)(A:ReOp n)(F:WaveK n m): Prop where
 contF : Continuous F
 Port :∀ X Y:Nom n m,Agrees S X.1 Y.1→F X=F Y
 FineF : ∀ x,RefineE S b (F x)
 Up(X):∀ {L:Side}{o:Odd L.val}, Along j L o (Vault.Thread j) true M G (unionP X)→ rise G M j Q A X (F X)
 peer(X) (v:Shape)(U:UNI SpinIdx) (p:JetS v.s false true U): let Y:=stanza G v inert X; ∀ {L:Side}{o:Odd L.val},Along j L o (Vault.Thread j) true M G (unionP Y) → rise G M j Q (theta (ψθ v U n) A) Y (theta (ψθ (v.broad G) U m) (F X)) -- use general orientation True
-- Nuts algebra
variable {G Q j M}
namespace rise
variable {A B:ReOp n}{f g:ReOp m}{X:Nom n m}
lemma add (h: rise G M j Q A X f)(t:rise G M j Q B X g) : rise G M j Q (A+B) X (f+g):=by intro v; rw [act_add,h,t,act_add]; unfold pathH; unfold scaleZ Dial.fire effectK cartsL; simp only [map_add,smul_add]
lemma mul(h: rise G M j Q A X f)(t:rise G M j Q B X g):rise G M j Q (A*B) X (f*g):= by intro v; rw [act_mul,t,h,←act_mul];
lemma color(c:ℂ)(h:rise G M j Q A X f): rise G M j Q (c • A) X (c • f):=by intro v; rw [act_smul,act_smul,h]; unfold pathH scaleZ Dial.fire effectK cartsL; simp only [map_smul]; simp only [smul_smul]; ring_nf -- tune module comm
lemma zero (X:Nom n m): rise G M j Q 0 X 0:=by intro v; rw [act_zero,act_zero]; simp only [pathH,scaleZ,Dial.fire,effectK,cartsL,map_zero,smul_zero]
lemma one(X:Nom n m): rise G M j Q 1 X 1:= fun _=>by rw [act_one,act_one]
end rise
namespace PrintU
variable {S:CoverS m} {b c:Bool} {X Y: ReOp n}{F U:WaveK n m}
lemma zero : PrintU G M j Q S b 0 0:=⟨continuous_const,fun _ _ _=>rfl,fun _=> Fine.empty _,fun X _ _ p=> rise.zero _,fun X v U p _ _ _=> by rw [theta_zero, show (0:WaveK n m) X=0 from rfl,theta_zero]; exact rise.zero _⟩
lemma one : PrintU G M j Q S false 1 1:=⟨continuous_const,fun _ _ _=>rfl,fun _=> Fine.one,fun X _ _ p=> rise.one _,fun X v U p _ _ _=> by rw [theta_one, show (1:WaveK n m) X=1 from rfl,theta_one]; exact rise.one _⟩
lemma add (h:PrintU G M j Q S b X F)(t: PrintU G M j Q S b Y U) :PrintU G M j Q S b (X+Y) (F+U):=⟨h.contF.add t.contF,fun _ _ u=> congrArg₂ (·+·) (h.Port _ _ u) (t.Port _ _ u),fun i=> Reed.Fine.add (h.FineF i) (t.FineF i), fun X _ _ p=>rise.add (h.Up X p) (t.Up X p),fun i v U' x _ _ h'=>by rw [Pi.add_apply,theta_add,theta_add]; exact rise.add (h.peer i v U' x h') (t.peer i v U' x h')⟩
lemma mul (h:PrintU G M j Q S b X F)(t: PrintU G M j Q S c Y U) :PrintU G M j Q S (b.xor c) (X*Y) (F*U):=⟨h.contF.mul t.contF,fun _ _ u=> congrArg₂ (·*·) (h.Port _ _ u) (t.Port _ _ u),fun i=> Reed.Fine.grow (h.FineF i) (t.FineF i), fun X _ _ p=>rise.mul (h.Up X p) (t.Up X p),fun i v U' x _ _ h'=>by rw [Pi.mul_apply,theta_mul,theta_mul]; exact rise.mul (h.peer i v U' x h') (t.peer i v U' x h')⟩
lemma color (h:PrintU G M j Q S b X F)(c:ℂ): PrintU G M j Q S b (c • X) (c • F):=⟨h.contF.const_smul _,fun _ _ u=> congrArg (fun x:ReOp m=> c • x) (h.Port _ _ u),fun x=> Fine.scale (h.FineF x) _,fun X _ _ p=> rise.color _ (h.Up X p),fun i v U p _ _ h'=>by rw [Pi.smul_apply,theta_smul,theta_smul]; exact rise.color _ (h.peer i v U p h')⟩
end PrintU
end YM.CF.DPress.Chess.Lift
