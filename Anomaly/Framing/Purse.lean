import Anomaly.Framing.ArcRent
import Anomaly.Framing.Fair
import Anomaly.Rack.Facets
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour.Turning
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Hake Jet Sault Stax Rill Ione Ione.Clock Salt
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
variable {q:ℕ}{h a b d e t:ℝ}
local notation "T"=> strive_E P.order
local notation "Vn" => Aura n

lemma unitT (p : BudgetPoint):0 ≤ strive_E p.order:=by unfold strive_E composeCost; positivity
lemma carries_herb (s:Sweep n)(sW:s∈Whirl n)(v:Herb P q (moldA s X) h V a)(hv:0≤h):
    Herb P q X h (fireTurn s⁻¹ V) (strive_E P.order*a):=by
  refine ⟨mul_nonneg (unitT _) v.price,fun Y t D w u=>?_,fun Y g V' z i=>?_⟩
  · have hp:Bias.αt X Y D (cipherK q):= ⟨t,w,u⟩; obtain ⟨e,b',w⟩:= (optic s D X Y _).2 hp; exact carry_fares s sW (v.offer _ e _ b' w) hv
  have ht:(yellA s V').1 ∈ σX P (moldA s Y) ∅:= by
    have hz:flashA s V'.1∈σX P (moldA s Y) (actY s ∅):=(lights_C ..).2 z
    rwa [show actY s ∅=(∅:Support (More n)) from map_empty _] at hz
  unfold fireTurn; simp only [inv_inv]; exact congrArg (sauce s⁻¹.charge (detX s⁻¹.s) (γS s⁻¹)) (v.clean (moldA s Y) (map_subset_map.mpr g) (yellA s V') ht (bun s i)) -- syntax curry
lemma carries (s:Sweep n)(sW:s∈Whirl n)(v:Flight P q (moldA s X) h V a b)(hv:0≤h):
    Flight P q X h (fireTurn s⁻¹ V) (strive_E P.order*a) (strive_E P.order*b) :=by
  obtain ⟨W,p,e⟩:= v.forms
  refine ⟨carries_herb _ sW v.tube hv,fireTurn s⁻¹ W,carries_herb _ sW p hv,fun Y g V' z=>?_⟩; unfold fireTurn; simp only [inv_inv,←Sault.plower]
  congr 1; have ht:(yellA s V').1∈σX P (moldA s Y) ∅:=by
    have hz:flashA s V'.1∈σX P (moldA s Y) (actY s ∅):=(lights_C ..).2 z
    rwa [show actY s ∅=(∅:Support (More n)) from map_empty _] at hz
  exact e _ (map_subset_map.mpr g) _ ht

def cartTurn (s:Sweep n)(F:Bag n) : Bag n:= fun i=> fireTurn s (F (moldA s⁻¹ i))
lemma bag_cost (s:Sweep n)(U:Aura n→ℝ)(p:BudgetPoint)(a s':ℝ) : voyageB (fun i=>a*U (moldA s i)) p.B s'=a*voyageB U p.B s':=by
  rw [voyage_scale]; apply congrArg (a*·); unfold voyageB; refine Finset.sum_equiv (moldA s) (by simp) (fun i _=>?_); congr 1; exact congrArg (fun x:ℕ=> Real.exp (s'* (x:ℝ))) (glow_q s p.B i.val).symm

lemma urge (s:Sweep n)(sW:s∈Whirl n) (F : Bag n)(p:Barrage P q D h F t a b)(z:0≤h): Barrage P q (actY s D) h (cartTurn s F) t (strive_E P.order*a) (strive_E P.order*b):=by
  obtain ⟨Q,J,u,g,v,t'⟩:=p.price
  refine ⟨fun i=>T * Q (moldA s⁻¹ i), fun i=>T* J (moldA s⁻¹ i), fun X=> ?_, ?_, (bag_cost _ _ _ _ _).trans_le (mul_le_mul_of_nonneg_left v (unitT _)),(bag_cost _ _ _ _ _).trans_le (mul_le_mul_of_nonneg_left t' (unitT _))⟩
  · unfold cartTurn
    have hp:= carries _ (inv_mem sW) (u (moldA s⁻¹ X)) z; rwa [inv_inv] at hp
  intro i p
  obtain ⟨i,rfl⟩:=(moldA s).surjective i; change ¬actY s D ⊆ actY s i.val at p
  obtain ⟨x,k,v⟩:= g i (fun v=> p (map_subset_map.mpr v)) -- tune
  · unfold cartTurn; rw [show moldA s⁻¹ (moldA s i)=i from Subtype.ext (tape_C s _),x]; refine ⟨funext fun X=> map_zero (Urn.lotY ..),?_,?_⟩<;> dsimp only <;> rw [show moldA s⁻¹ (moldA s i)=i from Subtype.ext (tape_C s _)] <;> simp [k,v] -- map_zero

lemma runs (s:Sweep n)(F:Bag n)(V:Orbit n)(i:Vn): cartTurn s F (moldA s i) (yellA s V)=sauce s.charge (detX s.s) (γS s) (F i V):=by
  unfold cartTurn; rw [step_turn, show moldA s⁻¹ (moldA s i)=i from Subtype.ext (tape_C s _)]

lemma yrev (s:Sweep n)(V:Orbit n):yellA s (yellA s⁻¹ V)=V:=by
  have ht:yellA s⁻¹⁻¹ (yellA s⁻¹ V)=V:= Prod.ext (revB s⁻¹ V.1) (tuftT s⁻¹ V.2); rwa [inv_inv] at ht
lemma yspec (s:Sweep n):Surjective (yellA s):=fun x=> ⟨_,yrev s x⟩
lemma crosses (F:Bag n)(p:∀ (X:Aura n)(V:Orbit n),Sector (camp X.val) false (F X V))(s t:Sweep n)(i:Vn)(V:Orbit n):
    cartTurn (s*t) F (moldA t i) (yellA t V)= sauce t.charge (detX t.s) (γS t) (cartTurn s F i V):=by
  obtain ⟨i,rfl⟩:=(moldA s).surjective i; obtain ⟨V,rfl⟩:=(yspec s) V
  rw [show moldA t (moldA s i)=moldA (s*t) i from Subtype.ext (tape_B ..),show yellA t (yellA s V)=yellA (s*t) V from yell_t ..,runs,runs]
  exact (spin_spin (p ..) ..).symm
lemma crosses_one (F:Bag n)(p:∀ (X:Aura n)(V:Orbit n),Sector (camp X.val) false (F X V)) : cartTurn 1 F= F:=by
  funext i x; unfold cartTurn fireTurn; rw [inv_one,show moldA (1:Sweep n) i=i from ?_, show yellA 1 x=x from ?_ ]; exact spin_one (p ..)
  · have h: yellA (1:Sweep n) x=yellA 1 (yellA 1 x):=(by rw [yell_t,one_mul]); rw [h]; have hx:=yrev 1 x; rwa [inv_one] at hx
  apply (moldA 1).injective; rw [show moldA 1 (moldA (1:Sweep n) i)=moldA (1*1) i from Subtype.ext (tape_B ..),one_mul]
end YM.CF.Sour.Turning
