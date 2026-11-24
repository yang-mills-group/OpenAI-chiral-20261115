import Merino.Bias
import Merino.Salon
import YM.SU5.Exchange.Stack.Nest
import YM.CF.Continuum.Square

/-! Pass a spool's prices to its physical Mark via a bra equality.
This retains the *ratio*, not an equality for absolute/variation measures.
The unit of account for single-root expenses here is the price of the
corresponding insertion into the excitation program. No assertion that
the `Integral` functional on arbitrary programs contracts those prices. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n
open Window Buffered StressExchange Dial

open Kennel Paige Vault Vow.TreasuryFog
variable {m B L:Side}{j:ℕ}{odd:Odd L.val}
local notation "N"=>mid m B
section
variable {A:Pricing j L odd (Thread j)}{e:ℝ}(U:Grasp A B e)
    (R:GramM (mid m B))(K:Scree.Loom (mid m B))
/-- Certification for one input. Preserve poses in `dec` for later use
on translated and reflected copies; prices here asserted *at this root*.
-/
structure Tailoring (dec:Spool N)(a b d:ℝ)
    (fac:ℂ)(q l:ℕ)(h s:ℝ)(F:Bag N)(c cost:ℝ) : Prop where
  usable:∀ z:Orbit N,IsStarProjection (spar j R.J.M (K z))
  hem:dec.Hem K R.p a b d
  width:24*dec.stepY ≤ R.p.B
  BP: Nest U R K q l dec.post h s (dec.release K R.p fac) F c cost
end

abbrev baseT(R:GramM n)(z:Orbit n):Wave (Dwell n):=
  Cadre.poseL _ (fueled R.p R.K z)

lemma pilot_den {A:Pricing j L odd (Thread j)}{e:ℝ}(U:Grasp A B e)
    (R:GramM (mid m B))(K:Scree.Loom (mid m B))(z:Orbit N)
    (w:IsStarProjection (spar j R.J.M (K z))):
    denZ R U K z=pilotH U R K z w (baseT R z):=by
 let hr:=showUp (R:=R) U K z w 0 R.K
 have hp:exponentL R.p 0 z.1=0:=by simp [exponentL,numbE]
 rw [hp,exp_zero,one_mul,add_zero] at hr
 exact hr

namespace Tailoring
variable {A:Pricing j L odd (Thread j)}{e:ℝ}{U:Grasp A B e}
    {R:GramM (mid m B)}{K:Scree.Loom (mid m B)}
    {y:Spool (mid m B)} {a b d c cost:ℝ}
    {fac:ℂ}{q l:ℕ}{h s:ℝ}{badgeX:Bag (mid m B)}
    (t:Tailoring U R K y a b d fac q l h s badgeX c cost)
local notation "cake"=> y.opening K R.p fac
local notation "hatC"=> y.release K R.p fac
local notation "paidY" z:max=> pilotH U R K z (t.usable z)
def delivered (z:Orbit N):Phys N:=(paidY z) (acts (∑ i:Aura N, badgeX i z) (baseT R z))
lemma delivers (z:Orbit N):
    acts (hatC z) (denZ R U K z)=t.delivered z:=by
 rw [pilot_den U R K z (t.usable z)]
 exact (t.BP.science _ _ _).symm


lemma read_other (z:Orbit N){M:Finset (Single N)}{v:Bool}{T:FC (Single N)}
    (l:Disjoint (modesIn N (y.canvas R.p)) M) (u:Fock.Sector M v T) :
    beamZ N (acts (T*cake z.1) (denZ R U K z))=beamZ N (acts T (t.delivered z)):=by
 unfold beamZ; rw [t.hem.have_y t.width z fac u l,act_mul,t.delivers]

lemma gross {D:Evaluation N}{M:Finset (Single N)}{v:Bool}
    (l:Disjoint (modesIn N (y.canvas R.p)) M)(u:∀ z:Pane N,Fock.Sector M v (D z)) :
    moment (denZ R U K) (D*cake) = ∫ z:Orbit N,beamZ N (acts (D z.1) (t.delivered z)) ∂city N:=
  integral_congr_ae (Eventually.of_forall fun z=> t.read_other z l (u z.1))

lemma ratio {D:Evaluation N}{M:Finset (Single N)}{v:Bool}
    (l:Disjoint (modesIn N (y.canvas R.p)) M)(u:∀ z:Pane N,Fock.Sector M v (D z)) :
    finiteForm A U R K (D*cake) =
    (∫ z:Orbit N,beamZ N (acts (D z.1) (t.delivered z)) ∂city N) /
    (∫ z:Orbit N,beamZ N ((paidY z) (baseT R z)) ∂city N):=by
 rw [by_denominator,t.gross l u]
 unfold partitionZ
 simp_rw [←pilot_den]

open Py.Rate.LocalLimit

lemma takes {D:Marks.Tagged N}{M:Finset (Single N)}{v:Bool}
    (l:Disjoint (modesIn N (y.canvas R.p)) M)
    (u:∀ z,Fock.Sector M v (D z)) (env:Envelope D)
    (cold: Integrable (denZ R U K) (Scree.city N)) :
    let L:Marks.Tagged N:= D*(fun z=>cake z.1);
    Integrable (fun z=> Marks.read L z (denZ R U K z)) (Scree.city N) ∧
    Integrable (fun z=>beamZ N (acts (D z) (t.delivered z))) (Scree.city N) ∧
    Marks.evaluate (denZ R U K) L=
      ∫ z:Orbit N,beamZ N (acts (D z) (t.delivered z)) ∂Scree.city N :=by
 intro L
 have e:=Marks.lift_env cake (t.hem.licensed _).bill
 have he:=Marks.read_int L cold (Girt.kitE _ _ (·*·) (by fun_prop) env e)
 have hh(z):Marks.read L z (denZ R U K z)=beamZ N (acts (D z) (t.delivered z)):=t.read_other z l (u _)
 refine ⟨he,?_,integral_congr_ae (Eventually.of_forall hh)⟩
 exact he.congr (Eventually.of_forall hh)
end Tailoring
end YM.CF.Merino
