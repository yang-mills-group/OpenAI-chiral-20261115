import YM.SU5.Exchange.Pipe.Parch
import YM.SU5.Exchange.Reg.Incidence
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open SU Prism Tap Levier Thera Moto Oath Font Haro
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}
-- raw cell at matter x. Later convolution for telescope at larger tick.
abbrev millQ(x:Site N): Op (Single N):=∑ i:SpinIdx, panel (x,i) (x,i) 1
lemma sumCell : ∑ x:Site N,millQ x=1:=by
 ext ⟨⟨x,i⟩,b⟩ ⟨⟨y,j⟩,c⟩; simp [millQ, panel, Matrix.one_apply, Matrix.sum_apply,ite_and]; by_cases h:x=y <;> by_cases p:i=j <;> simp [*,Ne.symm]

lemma soakCostNN (p:Soak o X a b d): 0 ≤ b:=by obtain ⟨F,W,t,v,h,k⟩:=p; exact (sum_nonneg fun i _=> mul_nonneg (rent_pos _ _).le (sum_nonneg fun j _=>sum_nonneg fun k _=> (t _).nonn _ _)).trans h
abbrev oneMill(a:ℝ):ℝ:=(Fintype.card SpinIdx:ℝ)*(Real.exp a * ((Fintype.card SU.Slot:ℝ)^2))
lemma millBill(x:Site N):Soak (node x) (fun _=> millQ x) a (oneMill a) d:=by
 let p:Sa N:={node x}; let V(i:SpinIdx):=Tulip.reed (x,i) (x,i) ‖(1:Op SU.Slot)‖; let F(i:SpinIdx)(_y:Openc (More N) d):=panel (x,i) (x,i) (1:Op SU.Slot)
 have hx(i:SpinIdx):Suite (badge _) (bail N d) (bail N d) p (V i) (F i):=by
    let Q:=bail N d; refine panel_ticket (s:=Q) (t:=Q) (p:=fun g v=>matter (g (node v.1))) (q:=fun g v=>matter (g (node v.1))) (fun _=>rfl) (fun _=>rfl) (x,i) (x,i) p _ (fun _=>1) (.single _) (fun _=>mem_singleton_self _) (fun _=>mem_singleton_self _) ?_ (norm_nonneg _) ((badge _).base _) continuous_const (fun _=>le_rfl) ?_
    · intro g z; change (1:Op SU.Slot)*_=_*1; rw [one_mul,mul_one]
    intro X Y; rw [sub_self,norm_zero]; exact mul_nonneg (norm_nonneg _) ((forum N d).pos ..)
 refine arm_v (o:=node x) (fun _=>p) F V hx ?_ (by simp [p]) (fun _=>rfl)
 have hu(i:SpinIdx): ledgerV (V i)= (Fintype.card SU.Slot:ℝ)^2:=by
    unfold V ledgerV; rw [box_phi (x,i) (x,i) (x,i)]; simp
 simp_rw [hu]; simp [p,Branch.rent,oneMill]

-- canonical divergence at step one (matter lattice)
-- multiply on RIGHT by W, choose column representative for endpoint of path
abbrev mural (O:Site N → SOp N)(i j z:Site N)(a:Axis)(V:Chin N) : Op (Single N):=(↑(pipeFlow i j z a):ℂ) • ((O i V)*millQ j)
abbrev chute (O:Site N → SOp N) (z:Site N)(a:Axis)(V:Chin N):= ∑ i:Site N,∑ j:Site N, mural O i j z a V
lemma pipeEquation (O:Site N → SOp N) (V:Chin N)(p: (∑ i:Site N,O i V)=0) (x:Site N): O x V= ∑ a: Axis,(chute O x a V - chute O (x-step a) a V):=by
 let J(i j:Site N):= O i V* millQ j
 let D(i j:Site N)(z:Site N)(a:Axis):= mural O i j z a V
 have hp(i j:Site N): (∑ a:Axis,(D i j x a-D i j (x-step a) a))=(if x=i then J i j else 0)-(if x=j then J i j else 0):=by
    let k:=Font.pipeBirth i x j -- order of arguments x z y
    unfold D mural J; simp_rw [←sub_smul,←Complex.ofReal_sub,← Finset.sum_smul,←Complex.ofReal_sum,k]; split_ifs <;> simp
 have ht: (∑ a: Axis,(chute O x a V - chute O (x-step a) a V))= ∑ i:Site N,∑ j:Site N,∑ a:Axis,(D i j x a-D i j (x-step a) a):=by
    unfold chute; simp_rw [←sum_sub_distrib]; rw [sum_comm]; refine sum_congr rfl ?_; intro i _; rw [sum_comm]
 rw [ht]; simp_rw [hp,sum_sub_distrib]
 conv_rhs=> rw [sum_comm (f:=fun i j=> if x=i then J i j else 0)]
 simp [J,← sum_mul,← mul_sum,sumCell,p] -- tune

open Sault Ione
lemma expRoad (h:0 < a): ∃ C:ℝ,0<C ∧∀ (n:Side) (x: Site n),(∑ y:Site n, Real.exp (-a*separation x y)) ≤ C:=by
 obtain ⟨m,hm⟩:= exists_nat_gt (max a⁻¹ 2); have hm': 2 < (m:ℝ):= (le_max_right ..).trans_lt hm
 have ht:((m:ℝ)^2)⁻¹ ≤ a:= by rw [inv_le_comm₀ (pow_pos (by linarith) _) h]; exact (((le_max_left ..).trans hm.le).trans (by nlinarith))
 have hB:2 ≤ m:= by exact_mod_cast hm'.le
 refine ⟨max 1 (taxIns m),lt_of_lt_of_le zero_lt_one (le_max_left ..),fun n x=>?_⟩
 refine le_trans (sum_le_sum (g:=fun y:Site n=> Real.exp (-((m:ℝ)^2)⁻¹/2*separation x y)) (fun y _=> Real.exp_monotone ?_)) ((placeExpense m (by omega) x).trans (le_max_right ..))
 exact mul_le_mul_of_nonneg_right (by linarith : -a ≤ -((m:ℝ)^2)⁻¹/2) (Nat.cast_nonneg _)

-- crude payout allows every matricial stencil, rooted contact.So used at this orientation.
lemma stepOwed (p:0<a)(hb:0≤v) : ∃ U:ℝ,0<U ∧ ∀ {N:Side}(O:Site N→ SOp N),(∀ i,Soak (node i) (O i) (100*a) v d)→∀ (z:Site N)(l:Axis),Soak (node z) (chute O z l) a U d:=by
 obtain ⟨C,hC,W⟩:=expRoad p; let K:= oneMill (100*a); have hv:0 ≤ K:=by unfold K oneMill; positivity
 let D:= 2*(v*K); have hD:0 ≤ D:=by unfold D; positivity
 let A:= 4*a⁻¹*Real.exp a *D; have ha:0≤A:=by unfold A; positivity
 refine ⟨C*C*A+1,by positivity,?_⟩; intro N O pV z l
 let f(x y:Site N):ℝ:= Real.exp (-a*separation x y); let F(i j:Site N):= f z i*(f i j*A)
 have hp(i j:Site N):Soak (node z) (mural O i j z l) a (F i j) d:=by
    let u:ℝ:= pipeFlow i j z l
    by_cases hu:u=0
    · apply lift_U (show Soak (node z) (mural O i j z l) a 0 d from ?_) (show 0 ≤ F i j from (by unfold F f; positivity)); unfold mural; change Soak _ (fun x:Chin N=> (u:ℂ) • _) _ 0 _; simp_rw [hu]; simpa using ring_u (d:=d) (a:=a) (node z)
    let q:ℝ:=99*a; have hh: 100*a-q=a:=by unfold q; ring
    have H:= soak_row (pV i) (millBill (N:=N) j) (by positivity) (g:=show 0 ≤ q by unfold q; positivity) (by linarith)
    rw [hh] at H
    apply lift_U (less_U (o:=node z) (soak_tr H p.le) (u:ℂ))
    let L:ℝ:= separation i j; let B:ℝ:= separation i z
    have hl : B ≤ 4*L:=by unfold B L; exact_mod_cast Font.pipeHome i z j l hu
    have hg : 0≤L:=Nat.cast_nonneg _
    have w: ‖(u:ℂ)‖ ≤ 4*L:= by rw [Complex.norm_real,Real.norm_eq_abs]; exact Font.pipeBill i z j l
    rw [Hove.ζdist,Hove.ζdist]; push_cast -- push Real cast
    have u1:Real.exp (a*(4*(2*B)+1))*Real.exp (-q*(2*L)) ≤ Real.exp a * (Real.exp (-a*B)*Real.exp (-a*L)*Real.exp (-a*L)):=by
       refine le_trans ?_ (le_refl _) ; simp_rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; unfold q; nlinarith [mul_nonneg p.le hg]
    have u2:L*Real.exp (-a*L) ≤ a⁻¹:=by rw [neg_mul,Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _),le_inv_mul_iff₀ p]; linarith only [Real.add_one_le_exp (a*L)]
    unfold F; unfold f; rw [separation_comm z i]
    change ‖(u:ℂ)‖* (Real.exp (a*(4*(2*B)+1))*(Real.exp (-q*(2*L))*D)) ≤ Real.exp (-a*B)*(Real.exp (-a*L)*A)
    let Z:=Real.exp a*Real.exp (-a*B)*Real.exp (-a*L); have hZ:0≤ Z:=by unfold Z; positivity
    calc _ ≤ 4*L*((Real.exp a*(Real.exp (-a*B)*Real.exp (-a*L)*Real.exp (-a*L)))*D):= mul_le_mul w (mul_assoc ..|>.symm.le.trans (mul_le_mul_of_nonneg_right u1 hD)) (by positivity) (by positivity)
         _=4*Z*(L*Real.exp (-a*L))*D:=by unfold Z; ring
         _ ≤4*Z*a⁻¹*D:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left u2 (by positivity)) hD
         _ = _:=by unfold A Z; ring
 have ht:= sun_K univ (fun (i:Site N) x=> ∑ j:Site N,mural O i j z l x) (fun i=> ∑ j:Site N,F i j) (fun i _=> sun_K univ (fun j=>mural O i j z l) (fun j=>F i j) (fun j _=> hp i j))
 apply lift_U ht; refine le_trans ?_ (le_add_of_nonneg_right (by norm_num:(0:ℝ)≤1)) -- issue ?_ choose RHS
 apply le_trans (b:= ∑ i:Site N, (f z i) *(C*A)); · apply sum_le_sum; intro i _; dsimp only [F]; rw [←mul_sum,←sum_mul]; exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (W _ _) ha) (Real.exp_pos _).le
 rw [← sum_mul,mul_assoc]; exact mul_le_mul_of_nonneg_right (W _ z) (by positivity)
end YM.CF.Swell
