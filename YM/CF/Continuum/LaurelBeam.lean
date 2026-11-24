import YM.CF.Continuum.Aspen
import YM.CF.Continuum.Extensive
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 780000
set_option synthInstance.maxSize 16000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
namespace YM.CF.Graph.Diff
open Function Filter Finset NormedSpace Lattice Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Branch Dial RG Skye Laic
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
variable {n:Side}{p:BudgetPoint}{Q Q':Sweep n→Prop}{a C r v κ w t α:ℝ}
-- exact relative denominator cost in reached through-stove stencils
abbrev ξX (A B:GramM n)(d h:ℝ):Prop:= IncX (fun _=>False) (A.F-B.F) A.p h d ∧ Dark (fun _=>False) (A.K-B.K) A.p h d
lemma latent(p:BudgetPoint)(E F:RegBudget n)(x:Pane n) : exponentL p (E-F) x=exponentL p E x-exponentL p F x:=by
 unfold exponentL numbE; rw [←sum_sub_distrib]; apply sum_congr rfl; intro i h; by_cases t:pingS p.threshold i.val.2 x <;> simp [Set.indicator,t] -- tune
local notation "vol_" a => rankV n a
lemma exponent_p (P:Op (Single n))(hP:IsStarProjection P)(U V:ribbon (Single n))(ht:1≤t)(hw:tier t V.val ≤ v)(hp:tier t (U-V).val ≤ w)(hv:w≤1/2) : ‖tank P (exp U - exp V)‖ ≤ 2*w*Real.exp v:=by
 let T:=Single n; let A:= Pastry.shelf t ht (fun _:Finset Unit=> (univ:Finset (LeanV T))) monotone_const
 let P':= nursery P hP; let B:=P'.cook; obtain ⟨_,k⟩:= Petal.ignition A ∅ (U-V) (fineShape (U-V)) w hp hv
 have ht₁:0≤2*w:= (Pastry.pitch (zero_le_one.trans ht) _).trans (show tier t (exp (U-V)-1).val ≤2*w from k)
 have hq: ‖tank P (exp (U-V)-1)‖ ≤ 2*w:=(billP _ _ hP ht).trans k; have hx: ‖tank P (exp V)‖ ≤ Real.exp v:=by
    rw [tank_eq P (exp V) hP,Poly.rising]; exact (bootC _).trans (Real.exp_monotone ((billP _ _ hP ht).trans hw))
 letI : NormedAlgebra ℚ (ribbon (Single n)):= NormedAlgebra.restrictScalars ℚ ℝ (ribbon _)
 have he:U=U-V+V:=by simp only [sub_add_cancel]

 rw [show exp U-exp V=(exp (U-V)-1)*exp V from (by rw [sub_mul, one_mul,←exp_add, ←he]),tank_eq _ _ hP,map_mul]; exact (norm_mul_le ..).trans (mul_le_mul hq hx (norm_nonneg _) ht₁)
variable (A B:GramM n)(ht:1≤t)
local notation "Vκ" => rankV n κ
local notation "Vv" => rankV n v
local notation "QZ"=> rankV n w
include ht in
lemma fuel_turn (h:A.p=B.p)(hx:A.slip=0)(hk:B.slip=0)(W:Graph.Ledger t v w r C A)(W':Graph.Ledger t v w r C B)(U:Orbit n)(e:ξX A B κ t)(p:Op (Single n))(hP:IsStarProjection p)(tq: Vκ≤1/2)(v0: 0≤ v)(w0:0≤w) : ‖tank p (A.board U)-tank p (B.board U)‖ ≤ Real.exp (Vv+2*QZ)*(3*Vκ):=by

 let V:=A.p; let x:=U.1; let F:= exponentL V A.F x; let G:= exponentL V B.F x; let K:= fueled V A.K U; let K':= fueled V B.K U; let pf:= nursery p hP; let Hp:= zero_le_one.trans ht; have ha:tier t F.val ≤ Vv:= toeE W.reg Hp x; have hh:IncX (fun _=>False) B.F A.p t v:= h.symm ▸ W'.reg; have hg:tier t G.val ≤ Vv:= toeE hh Hp x
 have hfuel:Dark (fun _=>False) B.K A.p t w:= h.symm ▸ W'.force; have hu:tier t (F-G).val ≤ Vκ:= (latent _ _ _ _) ▸ (toeE e.1 Hp x)
 have hp₀:0≤Vκ:= (Pastry.pitch Hp _).trans hu; have hp₁:0≤QZ:=by unfold rankV; positivity
 have hX:tier t K.val ≤ Real.exp QZ:= toeF W.force Hp U; have hL:tier t (K-K').val ≤ Vκ*Real.exp (2*QZ):=by rw [two_mul]; exact fuel_diff ht U W.force hfuel e.2
 have hv: ‖tank p (exp G)‖ ≤ Real.exp Vv:=by rw [tank_eq p (exp G) hP,Poly.rising]; exact (bootC _).trans (Real.exp_monotone ((billP _ _ hP ht).trans hg))
 have he:tier t G.val ≤ Vv:=hg
 have hz:A.board U-B.board U = (exp F-exp G)*K + exp G*(K-K'):=by
    unfold GramM.board; rw [hx,hk,←h]; have hx:exponentL V 0 x=0:=by unfold exponentL; refine sum_eq_zero fun i h=>?_ ; simp [numbE]
    simp_rw [show exponentL A.p 0 U.1= _ from hx,add_zero]; unfold F G x K K' V; ring -- indentation
 simp_rw [show ∀ u,tank p u= pf.cook u from fun i=>tank_eq _ _ hP]; rw [←map_sub,hz,map_add,map_mul,map_mul]; calc
   _ ≤ 2*Vκ*Real.exp Vv * Real.exp (2*QZ)+Real.exp Vv* (Vκ*Real.exp (2*QZ)):= (norm_add_le ..).trans (add_le_add ((norm_mul_le ..).trans (mul_le_mul (exponent_p _ hP F G ht he hu tq) (((billP _ _ hP ht).trans hX).trans (Real.exp_le_exp.mpr (by linarith))) (norm_nonneg _) (by positivity))) ((norm_mul_le ..).trans (mul_le_mul hv ((billP p _ hP ht).trans hL) (norm_nonneg _) (Real.exp_pos _).le))) -- positivity
   _ = _:=(by rw [Real.exp_add]; ring)
open Window
abbrev fare(n:Side)(t c:ℝ):= flagBill n t t c
include ht in
lemma mile_diff(j:ℕ)(e:A.p=B.p)(hv:A.slip=0)(hy:B.slip=0)(ht':A.J=B.J)(W:Ledger t v v r C A)(W':Ledger t v v r C B)(U:Loom n)(x:Orbit n)(htV:ξX A B κ t)(tq:Vκ ≤1/2)(hp:IsStarProjection (spar j A.J.M (U x)))(u:0≤r)(v0:0≤v): ‖mile j A U x-mile j B U x‖ ≤ Real.exp (fare n v C)*(3*Vκ):=by
 let Z:= Real.exp (Vv+2*Vv); let x':= (U x); let K:=Complex.exp (-(Pec.pigment A.J.I x')); let p':= spar j A.J.M x'; let Q:= -(Pec.pigment A.J.I x'); have he: ‖Q‖≤ pittance n 2 C:=by rw [show ‖Q‖= _ from norm_neg _]; exact aurP _ _ W.field.2 (railT _ _ u) (by positivity)
 have hx_: actF j B U x=actF j A U x:=by unfold actF; rw [ht']
 have hV:tier t (exponentL A.p (A.F-B.F) x.1).val ≤ Vκ:= toeE htV.1 (zero_le_one.trans ht) _; have ha:0≤ Vκ:= le_trans (Pastry.pitch (zero_le_one.trans ht) _) hV; have he':0≤ Vv:=by unfold rankV; positivity
 let Z':=Real.exp (pittance n 2 C); have hZ':‖K‖ ≤ Z':= (Complex.norm_exp_le_exp_norm _).trans (Real.exp_monotone he); -- ABI conflict same name fix
 have hu:= thermalCap _ U W x u j hp (by norm_num :(0:ℝ)≤2) (railT _ _ u)
 unfold mile; rw [←(show A.J=B.J from ht'), hx_, ← smul_sub, ←sub_mul] -- sub_smul wrong smul_sub
 refine le_trans (b:=Z'*(Z*(3*Vκ)*Real.exp (doorF n 2 C))) ?_ ?_; swap
 · unfold Z Z' fare flagBill; unfold rankV; rw [show v*( (More n).val : ℝ)^4+ 2*(v*((More n).val : ℝ)^4)=(v+v+v)*((More n).val:ℝ)^4 from (by ring)]; simp_rw [Real.exp_add]; exact le_of_eq (by ring)
 rw [norm_smul]; exact mul_le_mul hZ' ((norm_mul_le ..).trans (mul_le_mul (fuel_turn A B ht e hv hy W W' x htV p' hp tq v0 v0) ((bootC _).trans (Real.exp_monotone hu)) (norm_nonneg _) (by unfold Z; positivity))) (norm_nonneg _) (Real.exp_pos _).le
end YM.CF.Graph.Diff
