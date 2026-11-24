import YM.CF.Pic.Hall
import YM.CF.Girt.East
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Pic
open Function Filter Metric Finset NormedSpace Lattice Laurent Kea Lat Fir Tulip Rush Cube Jill Ember SU Dial Thera Fock Peaks Cascade Flare Scroll Spire Sods CF.Jet Vault Paige Brace Branch Tenant Broc
open scoped Topology BigOperators Matrix MatrixOrder ContDiff Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
section
variable {n:Type*}[Fintype n][LinearOrder n]{p q:Wave n}{k b:ℝ}
def whisk(U:UNI n)(x:Reader0 n):Reader0 n:= (x.1,acts U.val x.2)
abbrev Fone(U:UNI n): Wave n→Wave n:=fun i=> effectK U.val i
lemma kgreen(U:UNI n)(l:List (Reader0 n)): acts (rollC ton (l.map (whisk U))) (Fone U q)= Fone U (acts (rollC ton l) q) :=by
 let V:=quantU U; have he(t:Reader0 n):ton (whisk U t)=twist V (ton t):=by rcases t with ⟨a,x⟩; cases a; exact (twist_create ..).symm; exact (twist_remove U x).symm
 rw [rollC,List.map_map,show ton ∘ whisk U=(twist V) ∘ ton from funext he,← List.map_map,← map_list_prod]; exact (Fock.swivel (quantU U) _ q).symm -- tune
lemma Yep.gauge(U:UNI n)(h:Yep k p q b):Yep k (Fone U p) (Fone U q) b:=by
 intro i; let X:= i.map (whisk (star U)); have he:X.map (whisk U)=i:=by unfold X; rw [List.map_map,show whisk U ∘ whisk (star U)=id from (by funext t; exact Prod.ext rfl (act_starUnit U _))]; simp
 nth_rw 1 [←he]; rw [kgreen,show inner ℂ (Fone U p) (Fone U (acts (rollC ton X) q))= _ from act_unit_inner (quantU U) p _]; apply (h X).trans; apply le_of_eq; unfold size_k X unitsC; rw [List.length_map,List.map_map]; simp_rw [show (fun x:Reader0 n=> ‖x.2‖) ∘ whisk (star U)=_ from funext fun x=>act_unit_norm (star U) x.2]
lemma Yep.lim(h:Yep k p q b):‖inner ℂ p q‖≤b:=by simpa [rollC,size_k,unitsC] using h []
end
variable {m L B N:Side}{j:ℕ}{o:Odd L.val}{Y:Pricing j L o (Thread j)}{e b c v K a t:ℝ}{P:Grasp Y B e}
abbrev wit(m B:Side):=Wave (Single (CSide m B))
def beamM(m B:Side)(w:wit m B):=inner ℂ (mateK (CSide m B)) w
lemma Jection (X:Pearl P)(S:Stamped j L o Y)(t:P.roundZ ≤ (CSide m B).val)(p:1≤j)(M:Jill.Male)(V:Phase.Skin m B)(f:Cart (Domain m B))(h:Guard (gauge f V) e) {d a:ℝ} (v: Yep a (mateK _) (changeM P (gauge f V) M) d):Guard V e∧ (beamM m B (changeM P (gauge f V) M)=beamM m B (changeM P V M)) ∧ Yep a (mateK (CSide m B)) (changeM P V M) d:=by
 let N:=CSide m B; have he:gauge f⁻¹ (gauge f V)=V:=(by rw [windy,inv_mul_cancel,windy_u]); let U:=tradew N f⁻¹; let W:= changeM P (gauge f V) M; let q:=mateK N; have hp:Fone U W=changeM P V M:= Eq.symm (by nth_rw 1 [← he]; exact Hive.honey_x X S t p h f⁻¹); have hm:Fone U q=q:= Girt.mastC _
 refine ⟨he ▸ h.cov f⁻¹,?_,?_⟩; unfold beamM; rw [←hp]; change inner ℂ q W=inner ℂ q (Fone _ _); nth_rw 2 [←hm]; exact (act_unit_inner (quantU U) _ _).symm
 rw [←hp]; change Yep _ q _ _; rw [←hm]; exact Yep.gauge U v
end YM.CF.Pic
