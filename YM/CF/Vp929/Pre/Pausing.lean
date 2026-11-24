import YM.CF.Vp929.Pre.Azure
/- Generic Fee continuation on a pair-published market. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 480000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Finset MeasureTheory
open Lattice Wilson RG Push.AbsoluteSums Trees Cube
open Mew Lat Spire Paige Vault Phase Fock Tulip Pastry
open Nor Larch Vow Salt Ione Jet Skye Scree
open scoped Topology ContDiff BigOperators Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open scoped Mew
variable {m:Side}{p:BudgetPoint}{u d h a b:ℝ}{F:Pax m}{f:Pair (Pax m)} {T:Set ℂ}{A:ℂ→Pair (Pax m)}
def give_X (p: BudgetPoint)(X:Pair (Pax m)): Pair (Pax m) := Pair.cat (FeeD p (Pair.plus X)) (FeeD p (Pair.minus X))
lemma real_X(F:Pax m) : give_X p (F,0)=(FeeD p F,0):= by apply Pair.ext_pm <;> simp [give_X] <;> simp [Pair.plus,Pair.minus]
lemma plusX (g:Both (fun x=>MonoQ p h u x b) f) : Both (fun x=>MonoQ p h u x (b+b)) (Pair.plus f,Pair.minus f):= by
 have H:=g.1; have J:MonoQ p h u (Complex.I • f.2) b:= by simpa only [Complex.norm_I,one_mul] using MonoQ.scale g.2 Complex.I
 exact ⟨MonoQ.add H J,MonoQ.sub H J⟩
variable (q:FeeBook p.B b d) (h':1≤h)(v:0≤u)
include q h' v
lemma give_earns (g:Both (fun x=>MonoQ p h (u+d) x (b/2)) f) : Both (fun x=>MonoQ p h u x (ticket_f p.B b d)) (give_X p f):= by
 obtain ⟨A,Z⟩:= plusX g; rw [add_halves] at A Z; exact FeeBook.MonoQ_join (q.fee v h' A) (q.fee v h' Z)
lemma give_shows (pA:∀ z∈ T,Both (fun x=>MonoQ p h (u+d) x (b/2)) (A z))(hT:IsOpen T)(e:Census T A) : Census T (fun z=> give_X p (A z)):= by
 have hm z p₁: Both (fun x=>MonoQ p h (u+d) x b) (Pair.plus (A z),Pair.minus (A z)):= add_halves b ▸ plusX (pA z p₁)
 exact Census.recombine (q.analytic v h' hT _ (fun z h=>(hm _ h).1) (e.plus_curve)) (q.analytic v h' (hT.preimage Complex.continuous_conj) _ (fun z h=>(hm _ h).2) e.minus_curve)
end YM.CF.Py.Rate
