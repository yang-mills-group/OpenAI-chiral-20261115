import YM.CF.Exa.Snow
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
variable {κ:Type}[TopologicalSpace κ][Nonempty κ](N:Side){e a r C:ℝ}
lemma bloom_l (F:κ→ Core N)(p:Milli e N (fun i _=> F i) C a)(v:0≤ C)(h:C ≤1/4)(t:0≤a): Milli e N (fun i _=>exp (F i)-1) (16*Real.exp a*C^2+C) a∧ Milli e N (fun i _=> exp (F i)-1-F i) (16*Real.exp a*C^2) a:=by
 let X:=p.expo v h t; refine ⟨?_,X⟩; have ht:= X.plus p; simp_rw [sub_add_cancel] at ht; exact ht
-- K small MUST reserve; H powers. costs before $Φ.Ap.C. $R^D$.
abbrev dawH(C B:ℝ):= 16*Real.exp B*C^2
abbrev capW(C B:ℝ):= dawH C B+C
abbrev Uni(C A:ℝ):=8*C*capW C A*(Real.exp A+C)*C
abbrev budK(C A:ℝ):= 16*Real.exp A * Uni C A
abbrev tox(C A:ℝ):= (4*(Real.exp A+C)*dawH C A*C +8*(Real.exp A+C)*capW C A*C)+(16*(Real.exp A+C)*capW C A*(Real.exp A+C)*budK C A*C+4*budK C A*C)
variable {Y:κ→ Core N}(P F:Chin N→ Core N)(a B r:ℝ)(h:0 ≤ r)(t:0≤a)(v:0<C)(d:a≤B) -- tune
variable (k:ℝ)
variable (Q:Milli e N (fun i _=>Y i) (C*r) a)(p: Solo a k F e)(w:Solo a C P e)(hk:0 ≤ k)(hp:k ≤ C)(hr:r≤1)(he:C*r ≤ 1/4)(hr':Uni C B*r≤1/4)
local notation "Z"=> (fun i:κ=> exp (Y i))
include h t v d Q he hr
omit P F w p
lemma helm: Milli e N (fun i _=> exp (Y i)-1-Y i) (dawH C B*r^2) a∧ Milli e N (fun i _=> exp (Y i)-1) (capW C B*r) a:=by
 have he':= bloom_l _ Y Q (by positivity) he t; have hl:16*Real.exp a*(C*r)^2≤ dawH C B*r^2:=by unfold dawH; rw [mul_pow,←mul_assoc]; gcongr
 refine ⟨he'.2.tall hl,he'.1.tall ?_⟩; unfold capW; rw [add_mul]; have hp:0 ≤ dawH C B:=by unfold dawH; positivity
 exact add_le_add_left (hl.trans (mul_le_mul_of_nonneg_left (by nlinarith) hp)) _
include P F p w hk hp hr'
lemma properC : Milli e N (fun i=> bellP N P F (exp (Y i))) (Uni C B*r) a∧ Milli e N (fun i=> harpT N P F (exp (Y i))) (budK C B*r) a ∧ Milli e N (fun i x=> Branch.pencil (bellP N P F (exp (Y i)) x)) (budK C B*r) a:=by
 have he':= helm N a B r h t v d Q hr he
 let T:= Real.exp B+C
 have hf: Milli e N (fun (i:κ) x=>1+F x) T a:= ((Vista.holds (Crown.ident _ _ _)).plus (Vista.holds p)).tall (add_le_add (Real.exp_monotone d) hp)
 have hg:= Vista.holds (κ:=κ) w; have hh: Milli e N (fun i=> bellP N P F (Z i)) (Uni C B*r) a:= ((hg.mint (he'.2.mint hf t) t).mint hg t).tall (le_of_eq (by unfold Uni T; ring))
 have hx:0≤ Uni C B:=by unfold Uni capW dawH; positivity
 have hp:16*Real.exp a*(Uni C B*r)≤budK C B*r:=by unfold budK; rw [← mul_assoc]; gcongr
 let X:= hh.icicle (mul_nonneg hx h) hr' t; exact ⟨hh,X.1.tall hp, X.2.tall hp⟩
lemma frenzy: Milli e N (fun i=> finT N P F (exp (Y i)) (Y i)) (tox C B * (r^2+k*r)) a:=by
 obtain ⟨hw,hh,h⟩:= properC N P F a B r h t v d k Q p w hk hp hr he hr'
 have h' := helm N a B r ‹0≤r› t v d Q hr he
 let T:=Real.exp B+C; let G:= Vista.holds (κ:=κ) p; let I:=Vista.holds (κ:=κ) (Crown.ident (badge _) (bail N e) a); let H:=Vista.holds (κ:=κ) w
 have he:Milli e N (fun (_:κ) x=>1-P x) T a:= (I.subtract H).tall (add_le_add (Real.exp_monotone d) le_rfl); have hf: Milli e N (fun (_:κ) x=>1+F x) T a:=(I.plus G).tall (add_le_add (Real.exp_monotone d) hp)
 let X:=hh.mint H t; let A:= (he.mint h'.1 t).mint H t; let D:= he.mint h'.2 t
 apply ((((A.plus ((D.mint G t).mint H t)).plus ((D.mint hf t).mint X t)).plus (G.mint X t)).tall)
 let q₀ := tox C B; let L:=dawH C B; let W:=capW C B; let C':=budK C B
 have hC': 0≤ C':=by unfold C' budK Uni capW dawH; positivity
 have hL:0≤L:=by unfold L dawH; positivity
 have hW:0≤W:=by unfold W capW dawH; positivity
 have ht:0≤T:=by unfold T; positivity
 let U:= 4*T*L*C+16*T*W*T*C'*C; let V:=8*T*W*C+4*C'*C; have hy:U+V=q₀:=by unfold U V T L W C' q₀ tox; ring
 calc
    _ = U*r^2+V*(k*r):=by unfold U V T L W C'; ring
    _ ≤ (U+V)*(r^2+k*r):=by rw [mul_add]; exact add_le_add (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by unfold V; positivity)) (sq_nonneg _)) (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by unfold U; positivity)) (by positivity))
    _=_:=by rw [hy] -- tune
end YM.CF.Exa
