import Anomaly.Contact
import YM.SU5.Interaction.Title.Bonnet
import YM.SU5.Exchange.Pilot.Bundle
/-! `Barrage` purchases in the same currency as
`Preparation.enrollCurrency`. We plan to use the OrbitRack variant
for collective Keys (keeps first-Reg identity and nonlinear
coefficients); this establishes in particular payment of Title and of
BirthRight for the same openings. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Sour
open Function Filter NormedSpace Lattice Wilson Finset Skye Scree
open Cadre Palot MeasureTheory RG
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill
attribute [local instance] Rill.boreKSpace Rill.boreXN
variable {n:Side} {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)} {h a b:ℝ} {q:ℕ}

lemma Herb.title (p:Herb P q Y h V a) : Title P h (cipherK q) V Y a := ⟨p.body, p.offer,fun X v i t j=> (p.clean X v i t j).symm,p.price⟩
lemma Flight.birth (p:Flight P q Y h V a b): BirthRight P h V Y b:=by
  obtain ⟨G,H,v⟩:=p.forms
  intro X u
  obtain ⟨A,z,t,g⟩:= (BirthRight.whole H.title X u).pay
  refine ⟨A,z,t,?_⟩
  intro W w D i
  refine (g W w D i).germ ?_
  filter_upwards [whileLit (Z:=D) w] with y p
  let R : Orbit n := (pressQ P D W.1 y,W.2)
  change G R i ∅= V R i ∅
  rw [← skyF (G R) i, ← skyF (V R) i, v X u R p]

/-- For a single opened seat. Incidence over all roots follows with
additional rate consumption; this receipt is support-totals anchored at
a pin. It uses `S` for required root-core included. -/
theorem Barrage.currency {S:Support (More n)} {G:Bag n} {s:ℝ}
    (p:Barrage P q S h G s a b)(hp:3 ≤ P.B)(hx:0≤h): ∃ A B : Aura n→ℝ,
    voyageB A P.B s ≤ a ∧ voyageB B P.B s ≤ b ∧ (∀ X:Aura n,¬S⊆X.val → A X=0 ∧ B X=0) ∧
    ∃ m:∀ X,Title P h (cipherK q) (G X) X (A X),
    (∀ X,BirthRight P h (G X) X (B X)) ∧ WickL P h (cipherK q) (Title.powerQ G A m).payX A B (fun i Y=>G Y i) S:=by
  obtain ⟨A,B,f,t,u,v⟩:=p.price; let F(X):= (f X).tube.title; let Z(X):=(f X).birth
  exact ⟨A,B,u,v,fun Y p=>(t Y p).2,F,Z,covenant hp G A B F Z hx _ fun i p=> (t i p).1⟩
end YM.CF.Sour
