import YM.CF.Graph.Zing
set_option autoImplicit false
noncomputable section
namespace YM.CF.Graph
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
open Skye RG Laic
open Nacre Font Pec
variable {n:Side}{v h b a:ℝ}{p:BudgetPoint}
structure Ledger (h v η r C:ℝ)(R: GramM n):Prop where
 reg: IncX (fun _=>False) R.F R.p h v
 slip:IncX (fun _=>False) R.slip R.p h v
 force:Dark (fun _=>False) R.K R.p h η
 field: R.J.under r C r C r C
-- tolerance vA>0
variable {v η e a h x y r C vA k c:ℝ}{R: GramM n}{X:Loom n}
def pittance(n:Side)(d C:ℝ):ℝ:= d^2*C*n.val^4
abbrev lark(n:Side):ℝ:=180*n.val^4
def doorF(n:Side)(d C:ℝ):ℝ:= lark n*(45*((d+d^2)*C))
def actF {n:Side}(j:ℕ) (R:GramM n)(T:Loom n)(V:Orbit n):Op (Single n) := Kennel.capT (spar j R.J.M (T V)) (R.J.P.den (T V))
-- toll notation collision. field parameters Interest.under r b x y ... expands aim.toll r x C y; CardK b≥.
lemma door_b (W:Ledger h v η r C R){y':Orbit n}(g:HelpP (X y') vA r)(e:0≤vA)(a:0≤r)(b:0≤C)(V:Aim n) (H:V=R.J.P): ‖V.den (X y')‖ ≤ doorF n vA C :=by
 subst V; unfold Aim.den doorF; simp only [Pi.add_apply]; have hK:=W.field.1; obtain ⟨i,j⟩:= hK; exact (norm_add_le ..).trans ((add_le_add (forge _ _ i g a e b) (forge _ _ j g a e b)).trans_eq (by rw [Pic.units_t (N:=n)]; unfold lark; ring))
variable {m B L:Side}{j:ℕ}
lemma gap_b (W:Ledger h v η r C R)(t:Orbit n)(g:HelpP (X t) vA r)(e:0≤vA)(a:0≤r)(b:0≤C) (p:IsStarProjection (spar j R.J.M (X t))): ‖actF j R X t‖ ≤ doorF n vA C :=by
 have ht:= door_b W g e a b _ rfl; unfold actF Kennel.capT; refine (norm_mul_le ..).trans ((mul_le_of_le_one_right (by positivity) (p.norm_le _)).trans ((norm_mul_le ..).trans ((mul_le_of_le_one_left (by positivity) (p.one_sub.norm_le _)).trans ht)))
def axle(n:Side)(v:ℝ):= (v+v)*(More n).val^4
def mile (j:ℕ)(R:GramM n)(T:Loom n)(V:Orbit n): FC (Single n):= Complex.exp (-(pigment R.J.I (T V))) • (Scree.tank (spar j R.J.M (T V)) (R.board V) * exp (dg (actF j R T V)))
open Paige Vault
variable {ho:Odd L.val}{Y:Pricing j L ho (Thread j)}{P:Grasp Y B e}
def beam(r:GramM (mid m B))(P:Grasp Y B e)(G:Loom (mid m B))(V:Orbit (mid m B)): Phys (mid m B):= acts (mile j r G V) (changeM P (G V) r.J.M)
lemma mote(F:GramM (mid m B))(P:Grasp Y B e)(t:Loom (mid m B))(V:Orbit (mid m B)): denZ F P t V=Complex.exp (F.H0 V.1) • beam F P t V:=by
 unfold denZ beam GramM.betaL mile; rw [act_smul,act_mul, sub_eq_add_neg, Complex.exp_add, smul_smul]; rfl
end YM.CF.Graph
