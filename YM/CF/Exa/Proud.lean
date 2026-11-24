import YM.CF.Exa.Gen
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
variable {Y:κ→ Core N}(P F:Chin N→ Core N)(a B r:ℝ)(h:0 ≤ r)(t:0≤a)(v:0<C)(d:a≤B)(k:ℝ)
variable (Q:Milli e N (fun i _=>Y i) (C*r) a)(p: Solo a k F e)(w:Solo a C P e)(hk:0 ≤ k)(hp:k ≤ C)(hr:r≤1)(he:C*r ≤ 1/4)(hr':Uni C B*r≤1/4)
abbrev zeta(C B:ℝ):=tox C B*(1+C) +4*(Real.exp B+C)*C*C
abbrev prima(C B:ℝ):= let K:=Real.exp B+C; 4*zeta C B*(Real.exp B+capW C B)*K +4*K*K*capW C B
include h t v d Q p w hk hp hr he hr'
lemma purse : Milli e N (fun i=>partV N P F (exp (Y i)) (Y i)) (zeta C B*r) a ∧ ∀ u:Bool,Milli e N (fun i=> boldT N P F (exp (Y i)) (exp (-(Y i))) (Y i) u) (prima C B*r) a:=by
 let U:= Real.exp B+C; let I:= Vista.holds (κ:=κ) (Crown.ident (badge _) (bail N e) a); have ht:Real.exp a ≤ Real.exp B:=Real.exp_monotone d
 let G:= Vista.holds (κ:=κ) w; have hf :Milli e N (fun (_:κ) x=>1-P x) U a:=(I.subtract G).tall (add_le_add ht le_rfl)
 let V:= zeta C B*r; let A:=fun i=> partV N P F (exp (Y i)) (Y i); have hv:Milli e N A V a:=by
    have hz:=frenzy N P F a B r h t v d k Q p w hk hp hr he hr'; apply ((((hf.mint Q t).mint G t).plus hz).tall); unfold V zeta; conv_rhs=> rw [add_mul,add_comm] -- tune
    apply add_le_add; apply le_of_eq; unfold U; ring
    rw [mul_assoc]; refine mul_le_mul_of_nonneg_left ?_ (by unfold tox budK Uni capW dawH; positivity); rw [add_mul,one_mul]; exact add_le_add (by nlinarith) (mul_le_mul_of_nonneg_right hp h)
 refine ⟨hv,fun i=> ?_⟩; let B':=capW C B
 have hz:= sail e N (X:=A) hv; have hh: Milli e N (fun (_:κ) x=>1+F x) U a:=(I.plus (Vista.holds p)).tall (add_le_add ht hp)
 have hp': Milli e N (fun (_:κ) x=>1-F x) U a:=(I.subtract (Vista.holds p)).tall (add_le_add ht hp)
 have hj: Milli e N (fun (_:κ) x=>1+pale F x) U a:=(I.plus (Vista.holds (solo_opp p))).tall (add_le_add ht hp)
 have hx: Milli e N (fun (_:κ) x=>1-pale F x) U a:=(I.subtract (Vista.holds (solo_opp p))).tall (add_le_add ht hp)
 let W:=Real.exp B+B'
 have hv'{Z:κ→ Core N}(u:Milli e N (fun i _=>Z i-1) (B'*r) a) : Milli e N (fun i _=>Z i) W a:=by
    have hh:= u.plus I; simp only [sub_add_cancel] at hh; exact hh.tall ((add_le_add (show capW C B*r≤ B' from mul_le_of_le_one_right (by unfold capW dawH; positivity) hr) ht).trans_eq (add_comm ..))
 let Z:= exp ∘ Y; let W'(i:κ):= exp (-(Y i)); have he':= helm N a B r h t v d Q hr he|>.2; have hu := helm N (Y:=-Y) a B r h t v d Q.neg_m hr he|>.2
 cases i; swap; · exact ((((hz.mint (hv' (Z:=W') hu) t).mint hx t).plus ((hj.mint hu t).mint hx t)).tall (le_of_eq (by unfold prima W V U B'; ring))) -- tune hv
 apply ((((hp'.mint he' t).mint hh t).subtract ((hv.mint (hv' (Z:=Z) he') t|>.mint hh t))).tall); unfold V U W prima B'; apply le_of_eq; dsimp only; ring
include h t v d Q hr he hr'
omit p w hk hp F P k
lemma red (hp:Solo a C (fun _=> tickA N) e) : Milli e N (fun (i:κ) _=>charmE (tickA N) (exp (Y i))) (budK C B*r) a ∧ ∀ i:κ, e>0→ ‖cern (tickA N) (exp (Y i))‖≤1/4:=by
 obtain ⟨X,U,H⟩:= properC N (fun _=>tickA N) 0 a B r h t v d 0 Q (show Solo a 0 _ e from Crown.free) hp le_rfl v.le hr he hr'; have hp(v:κ)(x):bellP N (fun _=>tickA N) (fun _=>0) (exp (Y v)) x=cern (tickA N) (exp (Y v)):=by unfold bellP cern; simp only [add_zero, mul_one]; -- tune zero
 change Milli e N (fun i x=>Branch.pencil (bellP N _ _ (exp (Y i)) x)) _ _ at H; change Milli e N (fun i x=>Branch.pencil (bellP N (fun _=>tickA N) (fun _=>0) (exp (Y i)) x)) _ _ at H; simp_rw [hp] at H
 refine ⟨H,fun i p=> ?_⟩; rw [← hp i (1:Chin N)]; exact ((X.stem i).lib.boundOp t ⟨1,vacancy0 _ p⟩).trans hr'
end YM.CF.Exa
