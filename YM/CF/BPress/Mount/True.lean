import YM.CF.BPress.Mount.Honesty
import YM.CF.BPress.Wealth.Mark
/- actual applied Spin Portrait. Keep origin & physical Occupied line. Eq:B-Ms approval still requires Photo./Geometry.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Mount
open Function Finset NormedSpace MeasureTheory Filter Metric Lattice Wilson Branch Fock Spin SpinSign Spin.Pledge Cube Lat SU Spin.Paint Nacre Laic Font Tulip Tenant Dial Scroll Thera Meadow Topology Habitat Habitat.Upled Habitat.Plain Engine Nougat Pf Primary
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Classical YM.CF.BPress.Vesper YM.CF.BPress.Habitat YM.CF.BPress.Habitat.Plain YM.CF.BPress.Habitat.Driver
attribute [local instance] opCStarAlgebra
open Driver Currency RealBook Actor Ledger Spark Vesper Shale Fare Machine Shot Till Store Skye Girt Scree Voice Noon Phase Extensor Stamps Grid Hazel Net Locale Push.AbsoluteSums --
variable {m B L:Side} {j:ℕ} {ho: Odd L.val}
open Paige Vault Peaks Spire -- tune
variable {Y:Pricing j L ho (Thread j)} {d:ℝ}
variable (U:Grasp Y B d) (V:GramM (mid m B))(R:Loom (mid m B))
-- Pacer.
namespace Recital
def car (U:Grasp Y B d)(V:GramM (mid m B))(r ε:ℝ): Driver (mid m B):= ⟨d,max 1 priceTone,r,ε,U.p,j,V.J.M,V.J.P⟩ -- tuning supply ε/r
abbrev tempo (U:Grasp Y B d)(V:GramM (mid m B))(r ε:ℝ):= (car U V r ε).Pose
abbrev drama := (U.cost m V.J.M)
variable (H:Pearl U)(v:Stamped j L ho Y)(r ε:ℝ) (t: 1≤j)(q:U.roundZ ≤ (mid m B).val) (x:tempo U V r ε)
local notation "Dℙ"=> car U V r ε
local notation "Ξ"=> decks Dℙ
local notation "∂x"=> x.val.G
def pin : Prop := Slow ∂x (hook x.val.X) H.q ∧ (Ξ).H x 0= fun i=> SU.Pair.fullM (hook x.val.X i)
def rel : Phys (mid m B):= relV U V.J ∂x
include t q v
lemma checkspin (uH:pin U V H r ε x): TrueSpin Dℙ (rel U V r ε x) (drama U V) x:=by
 have S: Issued ((Ξ).keys true x) ((Ξ).keys false x) ((Ξ).A x) ((Ξ).M x) ((Ξ).col x) ((Ξ).col' x) r ε:= x.property.state; let a:=(Ξ).A x; let u0: (Ξ).col x 0=postC x.val.X:=by apply congrArg coupling uH.2; -- tune
 let u:= changeM (m:=m) U ∂x V.J.M; let C:=(Ξ).M x; have he:Sea a u:=sea_g q ∂x x.property.glow V.J.M; have ht:=topOnSea (P:=a) S.proj he; have hp:rel U V r ε x= craft a C u 1:=by
    change acts (exp (dg C)) u = _; rw [tallied C S.she.nil]; unfold craft zom; rw [one_smul]
 rw [hp]; refine ⟨ Issued.rising S ht _, S.offset_bill (z:= ηLog x (drama U V)) ht he.2 (by simp [ηLog,zen]) ?_⟩ -- tune args order
 let Q:= x.property.state.birth; let K:= uPivot a ((Ξ).col x 0); have hv:Real.exp K= ‖filled a ((Ξ).col x 0)‖:= Issued.pivot_cost Q; have hx:filled a ((Ξ).col x 0)=coneP j V.J.M ∂x x.val.X:=by rw [u0]; rfl
 rw [hx]; exact change_v H v q t V.J.M ∂x x.property.glow x.val.X uH.1 K (hv.trans (congrArg norm hx)) -- parser
omit t q v
lemma still_den (b:Orbit (mid m B))(e:R b=∂x) : Wealth.relieve (Fixed.rescaleOffset U V R) V.path V.funds V.p V.beta b= Complex.exp (-duesF V x) • acts (tank ((Ξ).A x) (V.board b)) (rel U V r ε x):=by
 unfold Wealth.relieve; rw [BPress.strip,smul_smul,e, Complex.ofReal_exp,← Complex.exp_add]; congr 2; unfold duesF; ring -- tuning parent
end Recital
end YM.CF.BPress.Mount
#print axioms YM.CF.BPress.Mount.combined
#print axioms YM.CF.BPress.Mount.Recital.checkspin
#print axioms YM.CF.BPress.Mount.Passports.settled
