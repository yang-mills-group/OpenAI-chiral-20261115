import YM.CF.Tap.Scale
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tap
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
open NormedSpace Matrix Tenant Branch
variable {N:Side}
abbrev CrownX:= Op (Single N)
def plankP(N:Side)(Z:Op Slot):CrownX (N:=N):= headW N (Aop-(1/2:ℂ) • 1) Z
lemma plank_tick (Z:Op Slot):Commute (tickA N) (plankP N Z):=by
 unfold tickA plankP
 rw [plane_diag,show cutM plusHalf=Aop from raising.trans Adef.symm]
 apply (show ∀ a b:Op (Model N), a*b=b*a→Commute (love N a) (love N b) from fun a b h=> by unfold Commute SemiconjBy; rw [←map_mul,h, map_mul])
 unfold Lat.spin
 rw [jump_mul,jump_mul]; congr 1; ext1 i; rw [op_kron_mul,op_kron_mul,one_mul, mul_one,mul_sub,sub_mul,Matrix.mul_smul,Matrix.smul_mul,mul_one,one_mul]
lemma plank_h{Z:Op Slot}(p: star Z=Z):star (plankP N Z)=plankP N Z:=by unfold plankP headW; rw [←map_star, jump_star]; apply congr_arg; simp only [op_star_kron,star_sub,Aadj,star_smul,p,star_one]; norm_num [Equiv.refl_symm] -- tune
lemma soil_tick (a e:ℝ) : Solo (N:=N) a (wingRent Aop a) (fun _=> tickA N) e:=by unfold tickA; rw [plane_diag,show cutM plusHalf=Aop from raising.trans Adef.symm]; have h:=plateV N a e Aop 1 (by simp); rw [norm_one,mul_one] at h; exact h
variable {n: Type*}[LinearOrder n][Fintype n]
def trick(P Z W:Op n) : Op n:= (1-P)*(W-1-Z)*P+(1-P)*(W-1)*((1+cern P W)⁻¹-1)*P
-- Bop at W=exp Z
lemma knot_p (P Z W H:Op n)(p:IsStarProjection P)(q:star H*W=1)(k:‖cern P W‖<1): Bop P W=(1-P)*Z*P + trick P Z W:=by
 let A:=nous P W; have he:P*A=A:=(clan p k q).tray; have hz:(1-P)*A=0:=by nth_rw 1 [←he]; rw [←mul_assoc, show (1-P)*P=0 from (by rw [sub_mul,one_mul,p.isIdempotentElem.eq,sub_self]),zero_mul]
 unfold Bop laneP trick; change (1-P)*W*A=_; rw [mul_assoc ((1-P)*(W-1)) ((1+_)⁻¹-1) P, sub_mul ((1+_)⁻¹),one_mul]; change _= _+ (_+_*(A-P)); simp only [mul_sub,sub_mul,mul_one,hz]; abel
private lemma iota_cost{e a r:ℝ}{P:Chin N→ CrownX (N:=N)}(h: Solo a r P e)(v:0≤a)(p:0≤r)(q:r≤1/4): Solo a (16*Br a*r) (fun x=>(1+P x)⁻¹-1) e ∧ Solo a (16*Br a*r) (fun x=>pencil (P x)) e:=by
 let F(i:ℕ):=Real.exp a*(2*r)*(1/2:ℝ)^i; have hc : Summable F:= (summable_geometric_of_lt_one (show 0 ≤ (1/2:ℝ) by norm_num) (by norm_num)).mul_left _; have hf:∑' i,F i≤ 16*Br a*r:=by unfold F; rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; unfold Br; push_cast; have he:=Real.exp_pos a; nlinarith
 have hx(i:ℕ):Real.exp a*(2*r)^(i+1)≤ F i:=by unfold F; rw [pow_succ', ←mul_assoc (Real.exp a)]; gcongr; linarith -- tune
 constructor
 · unfold Solo; rw [show (fun x:Openc (More N) e=>(1+P x.val)⁻¹-1)=fun x=> ∑' i:ℕ, (-(P x.val))^(i+1) from ?_]; swap
   · funext x; have he:=h.lib.boundOp v x; let U:Op (Single N):= -(P x.val); have hu:‖U‖<1:=by rw [show ‖U‖= _ from norm_neg (P x.val)]; exact he.trans_lt (by linarith)
     rw [←sub_neg_eq_add 1 (P _), ← route_inv hu, ← (summable_geometric_of_norm_lt_one hu).sum_add_tsum_nat_add 1]; simp; rfl
   exact (Crown.tsK F (fun i=>(h.minus.powers v (i+1)).books (hx i)) v hc).books hf
 unfold Solo Branch.pencil; refine (Crown.tsK F (fun i=>?_) v hc).books hf
 have he:= (h.powers v (i+1)).scale (bcoef i:ℂ); rw [Complex.norm_real] at he; simp_rw [Complex.coe_smul] at he; apply he.books; exact (mul_le_of_le_one_left (by positivity) (bc_norm _)).trans (hx i)
lemma starsE (C:ℝ)(hC:0<C)(a:ℝ)(ha:0≤a):∃ δ R:ℝ,0<δ∧0<R∧∀ N:Side,∀ (e z:ℝ),0≤z→z≤δ→∀ (Z:CrownX (N:=N))(F:Chin N→ CrownX (N:=N)), Solo a (C*z) (fun _=> Z) e → Solo a C F e →
 Solo a (R*z) (fun x:Chin N=> charmE (F x) (exp Z)) e ∧
 Solo a (R*z^2) (fun x:Chin N=> trick (F x) Z (exp Z)) e ∧ Solo a (R*z) (fun _:Chin N=>exp Z-1) e ∧ ∀ x∈Openc (More N) e,‖cern (F x) (exp Z)‖ <1:=by
 let Q:=Real.exp a; let y:=16*Q*C^2; let w:=y+C; let u:=4*C^2*w; have hv:0<Q:=Real.exp_pos _; have h:0<w:=add_pos (by unfold y; positivity) hC; have hk:0<u:=by unfold u; positivity
 let m:=16*Q*u; let r:= 4*(Q+C)*y*C + 8*(Q+C)*w*m*C
 have hp:0<m:=by unfold m; positivity
 have hz:0≤y:=by unfold y; positivity
 have hy:0≤r:=by unfold r; positivity
 refine ⟨min 1 (min ((4*C)⁻¹) ((4*u)⁻¹)),r+w+m,lt_min one_pos (lt_min (by positivity) (by positivity)),by positivity,?_⟩
 intro N e z ht v Z F g s; have ha':16*Br a*(C*z)^2=y*z^2:=by unfold y Q Br; ring
 have he:= v.trans (min_le_left ..)
 have hg:C*z≤1/4:=by have hw:z≤(4*C)⁻¹:=v.trans ((min_le_right ..).trans (min_le_left ..)); rw [←one_div,le_div_iff₀ (by positivity)] at hw; linarith
 have hw:u*z≤1/4:=by have hx:z≤(4*u)⁻¹:=v.trans ((min_le_right ..).trans (min_le_right ..)); rw [←one_div,le_div_iff₀ (by positivity)] at hx; linarith
 have HH:=epay N g ha (by positivity) hg; rw [ha'] at HH
 let S:= exp Z; have heP : Solo a (w*z) (fun _:Chin N=> exp Z-1) e:=by have hx := HH.plus g; simp only [sub_add_cancel] at hx; exact hx.books (by unfold w; nlinarith [mul_nonneg hz (show 0≤z-z^2 by nlinarith)])
 have hs:Solo a (u*z) (fun x=> cern (F x) (exp Z)) e:=by unfold cern; have hk:= (s.product heP ha).product s ha; apply hk.books; unfold u; apply le_of_eq; ring
 have hx := iota_cost hs ha (show 0≤u*z by positivity) hw
 refine ⟨hx.2.books (show _≤ _*z by rw [show 16*Br a*(u*z)=m*z by unfold m Q Br; ring]; gcongr; linarith),?_,heP.books (by gcongr; linarith),fun x hx=>?_⟩ -- tune
 · have ht : Solo a (Q+C) (fun x=>1-F x) e:= (Crown.ident ..).sub s; have hk:= ((ht.product HH ha).product s ha).plus ((( (ht.product heP ha).product hx.1 ha)).product s ha); apply hk.books
   calc
    _ =r*z^2:=by unfold r m Q Br; ring
    _ ≤_:=by gcongr; linarith
 exact (hs.lib.boundOp ha ⟨x,hx⟩).trans_lt (by linarith)
end YM.CF.Tap
