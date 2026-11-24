import YM.CF.Exa.Cry
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 18000
noncomputable section
namespace YM.CF.Exa
open Function Filter Metric Lattice Wilson Laurent Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec Branch NormedSpace Finset
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open Tap Thera Haro -- tune
open Tap Tenant Proa
variable {κ:Type}[TopologicalSpace κ][Nonempty κ](N:Side){e a C:ℝ}
variable {Y:κ→ Core N}(P F:Chin N→ Core N)(a B r:ℝ)(h:0 ≤ r)(t:0≤a)(v:0<C)(d:a≤B)(k:ℝ)
variable (Q:Milli e N (fun i _=>Y i) (C*r) a)(p: Solo a k F e)(w:Solo a C P e)(hk:0 ≤ k)(hp:k ≤ C)(hr:r≤1)(he:C*r ≤ 1/4)(hr':Uni C B*r≤1/4)
abbrev wornP(C B:ℝ):=4*(Real.exp B+C)*(prima C B)*(Real.exp B+C)
abbrev grantsP(C B:ℝ):= 2*wornP C B*((Real.exp B+C)+wornP C B)
include h t v d Q p w hk hp hr he hr'
lemma sat : (∀ t u:Bool,Milli e N (fun i=> don N P F (exp (Y i)) (exp (-(Y i))) (Y i) t u) (wornP C B*r) a) ∧∀ t u:Bool, Milli e N (fun i=>mire N P F (exp (Y i)) (exp (-(Y i))) (Y i) t u) (grantsP C B*r) a:=by
 let T:=Real.exp B+C; have ht:Real.exp a ≤ Real.exp B:=Real.exp_monotone d; let W:=wornP C B
 have hv:0 ≤ W:=by unfold W wornP prima zeta tox budK Uni capW dawH; positivity
 have hu (j:Bool): Milli e N (fun (_:κ) x=> Proa.sprig j (P x)) T a:=by cases j; exact ((Vista.holds (Crown.ident _ _ _)).subtract (Vista.holds w)).tall (add_le_add ht le_rfl); exact Vista.holds (w.books (le_add_of_nonneg_left (Real.exp_pos _|>.le))) -- order
 have hm :∀ l u:Bool,Milli e N (fun i=> don N P F (exp (Y i)) (exp (-(Y i))) (Y i) l u) (wornP C B*r) a:= fun i u=> ((((hu i).mint ((purse N P F a B r h t v d k Q p w hk hp hr he hr').2 u) t).mint (hu u) t).tall (le_of_eq (by unfold wornP T; ring)))
 refine ⟨hm,fun u j=>?_⟩; apply (((sail e N (hm (!u) u)).mint ((hu j).plus ((hm j j).tall (mul_le_of_le_one_right hv hr))) t).tall); unfold T grantsP; apply le_of_eq; ring
variable (K E:ℝ)
structure Flyer (Y:κ→ Core N)(r v w a:ℝ):Prop where
 up:Milli e N (fun i=>flume N P F (exp (Y i))) (v*r) a
 endY:(∀ i x,x ∈ Openc (More N) e → ‖bellP N P F (exp (Y i)) x‖ ≤1/4) ∧ ∀ i, ‖cern (tickA N) (exp (Y i))‖≤ 1/4
 posture(t u:Bool):Milli e N (fun i=> don N P F (exp (Y i)) (exp (-(Y i))) (Y i) t u) (v*r) a
 hug(t u:Bool): Milli e N (fun i=>mire N P F (exp (Y i)) (exp (-(Y i))) (Y i) t u) (v*r) a
 sheer : Milli e N (fun i=> finT N P F (exp (Y i)) (Y i)) w a
abbrev deft(C A:ℝ):=16*budK C A +wornP C A +grantsP C A
lemma climb (z:0 < e)(u:Solo a C (fun _=>tickA N) e) : Flyer N P F (e:=e) Y r (deft C B) (tox C B*(r^2+k*r)) a:=by
 obtain ⟨X,J,L⟩:= properC N P F a B r h t v d k Q p w hk hp hr he hr'
 have hp' := red N a B r h t v d Q hr he hr' u; let Z:=sat N P F a B r h t v d k Q p w hk hp hr he hr'
 let W:=wornP C B; let V:=budK C B; let Y':=grantsP C B
 have hw:0 ≤ W:=by unfold W wornP prima zeta tox budK Uni capW dawH; positivity
 have hh:0 ≤ Y':=by unfold Y' grantsP; positivity
 have hx:0 ≤ V:=by unfold V budK Uni capW dawH; positivity
 refine ⟨(L.subtract hp'.1).tall (show V*r+V*r ≤ (16*V+W+Y')*r by rw [←add_mul]; exact mul_le_mul_of_nonneg_right (by linarith only [hw,hh,hx]) h),⟨fun i x t'=> ((X.stem i).lib.boundOp t ⟨x,t'⟩).trans hr',fun i=>hp'.2 i z⟩,fun i j=> (Z.1 i j).tall (show W*r≤ (16*V+W+Y')*r by exact mul_le_mul_of_nonneg_right (by linarith only [hw,hh,hx]) h),fun i j=> (Z.2 i j).tall (show Y'*r ≤ (16*V+W+Y')*r by exact mul_le_mul_of_nonneg_right (by linarith only [hw,hh,hx]) h),frenzy N P F a B r h t v d k Q p w hk hp hr he hr'⟩
end YM.CF.Exa
