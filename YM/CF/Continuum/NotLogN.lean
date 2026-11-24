import YM.CF.Mint.Flit
import Mathlib.Analysis.SpecialFunctions.Stirling

/-! # Uniform bound at all eras on the reference sea normalization
    keep much sharper than the O(Vlog N) lower on its log, crucial in
    pricing pressure for larger GW gauge boxes. Use just ONE coordinate of
    momentum (anticut pricing), but **every** site and flavor. This saves the
    powers of the period on the beam. -/

set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Gall Dial
open Graph Skye RG Laic MeasureTheory PathData Sods Precision Wilson Cascade CF.Paige Vault Nova Emu
open Laurent Next.Free Bloch Fir Jill Ember Kea
open scoped Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators ENNReal
attribute [local instance] opCStarAlgebra
variable {L' B N m:Side}{j n:ℕ}{r a b c d e k y:ℝ}{O:Odd L'.val}{Y:Pricing j L' O (Thread j)}{P:Grasp Y B e}{hP:Pearl P}

private def rail {N:Side}(x: Per N):ℝ:= (x.val+1:ℝ)/N.val * ((N.val-x.val:ℝ)/N.val)
private lemma rail_pos(x:Per N): 0 < rail x:= by
 unfold rail; have h: (x.val:ℝ)<N.val:=by exact_mod_cast ZMod.val_lt x
 have he: (0:ℝ)<(N.val:ℝ)-x.val:=sub_pos.mpr h; positivity
private lemma principal_floor(x:Per N) : rail x * Real.pi ≤ |Lat.principal x|:=by
 let n:ℝ:= N.val; let a:ℝ:=x.val; have hp:0<n:=nPos N; have ha:0≤a:=by unfold a; positivity
 have hx:a+1≤n:=(by norm_cast; exact_mod_cast Nat.succ_le_of_lt (ZMod.val_lt x): (x.val:ℝ)+1≤N.val) -- tune
 have hg:0 ≤ (n-a)/n:=div_nonneg (by linarith) hp.le
 rw [ch_price,payH (N:=N),abs_mul,abs_of_pos (pinch_pos _)]; refine (le_of_eq (mul_assoc _ _ _|>.symm)).trans (mul_le_mul_of_nonneg_right ?_ (pinch_pos _).le)
 unfold chert; change rail x*n≤ |2* _+1|; split_ifs
 · push_cast; refine le_trans ?_ (le_abs_self _); have hu : rail x ≤ (a+1)/n:= mul_le_of_le_one_right (by positivity) ((div_le_one hp).mpr (by linarith))
   refine le_trans (mul_le_mul_of_nonneg_right hu hp.le) ?_; rw [div_mul_cancel₀ _ hp.ne']; change a+1≤2*a+1; linarith
 push_cast; refine le_trans ?_ (neg_le_abs _); have he:rail x ≤ (n-a)/n:= mul_le_of_le_one_left hg ((div_le_one hp).mpr hx); refine le_trans (mul_le_mul_of_nonneg_right he hp.le) ?_; rw [div_mul_cancel₀ _ hp.ne']; change n-a ≤ -(2*(a-n)+1); linarith

private lemma log_start(k:ℕ): ∑ i:Fin k, Real.log (i.val+1:ℝ)= Real.log k.factorial:=by induction k with
| zero=>simp
| succ k t=> rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc,Fin.val_last]; rw [t,Nat.factorial_succ,Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]; push_cast; ring
private def railEquiv(n:Side): Fin n.val ≃ Per n:=
   {toFun:= fun i=> (i.val:Per n)
    invFun:= fun i=> ⟨i.val,ZMod.val_lt _⟩
    left_inv:=fun i=> Fin.ext (ZMod.val_natCast_of_lt i.isLt)
    right_inv:= fun i=> ZMod.natCast_zmod_val i }
private lemma log_uniform(N:Side): -2*(N.val:ℝ) ≤ ∑ i:Per N,Real.log (rail i):=by
 let v:ℝ:=N.val; let c:=Real.log v; have ht:1≤ v:= Nat.one_le_cast.mpr N.property
 let n(i:Fin N.val):=Real.log (i.val+1:ℝ)
 have h(i:Fin N.val): (N.val:ℝ)-(i.val:ℝ)=(i.rev.val:ℝ)+1 := by
   have hp:=i.isLt; rw [sub_eq_iff_eq_add]; exact_mod_cast (show N.val=i.rev.val+1+i.val from (by rw [Fin.val_rev]; omega))
 have he(i:Fin N.val): Real.log (rail (railEquiv N i))= n i+n (Fin.revPerm i)-2*c:= by
   unfold rail; rw [show (railEquiv N i).val=i.val from ZMod.val_natCast_of_lt i.isLt,h]; rw [Real.log_mul (by positivity) (by positivity), Real.log_div (by positivity) (by positivity), Real.log_div (by positivity) (by positivity)]; unfold n c v; rw [Fin.revPerm_apply]; ring
 rw [←Equiv.sum_comp (railEquiv N), sum_congr rfl (fun i (_:i∈univ)=> he i), sum_sub_distrib,sum_add_distrib,sum_const, card_univ,Fintype.card_fin,Equiv.sum_comp Fin.revPerm]; unfold n; rw [log_start,nsmul_eq_mul]; change -2*v≤_+_-v*(2*c)
 have hQ:= Stirling.le_log_factorial_stirling (n:=N.val) (Nat.ne_of_gt N.property); have hv:0 ≤ c:=Real.log_nonneg ht; have hf:= Real.log_nonneg (show 1 ≤ 2*Real.pi by linarith [Real.pi_gt_three]); unfold c v at *; linarith only [hv,hQ,hf]

private def digit : (Site N) ≃ (Per N× (Fin 3→ Per N)) :=
  { toFun:=fun x=>(x 0, fun i:Fin 3=> x i.succ)
    invFun:= fun x (i:Axis)=> Fin.cases x.1 x.2 i
    left_inv _x:=funext fun i:Axis=> Fin.cases rfl (fun _j:Fin 3=>rfl) i
    right_inv _x:=rfl }
private lemma byAxis(f: Per N→ℝ) : ∑ i: Site N, f (i 0)=(N.val:ℝ)^3*∑ i:Per N,f i:=by
  have hx := (Equiv.sum_comp (digit (N:=N)) (fun i:Per N× (Fin 3→ Per N)=>f i.1)); rw [Fintype.sum_prod_type] at hx; refine hx.trans ?_; simp [nsmul_eq_mul,Per,mul_sum]

-- runtime
lemma angel_per_site(D:Pic.Span hP a b c d k r n) : ∃ C:ℝ, 0 < C ∧ ∀ m:Side,n≤ (mid m B).val→∀ F:Jill.Male, Real.exp (-C*(mid m B).val^4) ≤ Kea.angel m P F:=by
 obtain ⟨μ,hM,pμ,t,H⟩:=Jill.zip D.p
 let x := -Real.log μ-2*Real.log Real.pi+4; refine ⟨45*(|x|+1),by positivity,fun m hm F=>?_⟩
 let N:=mid m B; let v:ℝ:=N.val; let a i:=Kea.angle (too N) i; have hx(i:Site N): 0<rail (i 0):=rail_pos ..
 rw [←D.fits _ hm]; let f(i:Stag N):= Jill.cup N j F r (a i); rw [←Real.le_log_iff_exp_le (ice_p _ _ F D.rP)]; change -(45*(|x|+1))*v^4 ≤ Real.log (∏ i:Stag N,f i); rw [Real.log_prod (fun i _=> (cup_p F D.rP _).ne')]
 let G(i:Per N) := Real.log μ+2*Real.log (rail i*Real.pi)
 apply le_trans ?_ (sum_le_sum (f:=fun i:Stag N=>G (i.1 0)) (fun i _=>?_))
 swap
 · have he: μ*(rail (i.1 0)*Real.pi)^2 ≤ f i:=by
     have hv := (H F _ (up_p (too N) (D.plan m hm).2.1 i)).1; refine le_trans (b:= Jill.disk j F (a i)) (le_trans ?_ hv) (le_max_right ..); have ht:= hx i.1
     gcongr; rw [too_u]; exact (principal_floor _).trans (norm_le_pi_norm (pm i.1) 0)
   refine le_trans ?_ (Real.log_le_log (by have he:=hx i.1; positivity) he); exact le_of_eq (by rw [Real.log_mul pμ.ne' (by have he:=hx i.1; positivity),Real.log_pow]; simp only [G,Nat.cast_ofNat]) -- tactic
 rw [Fintype.sum_prod_type]; simp_rw [sum_const,card_univ,slots,nsmul_eq_mul,←mul_sum,byAxis]
 have he(i:Per N): G i=Real.log μ + 2*Real.log (rail i)+2*Real.log Real.pi:=by unfold G; rw [Real.log_mul (rail_pos i).ne' Real.pi_pos.ne']; ring
 simp_rw [he]; rw [sum_add_distrib,sum_add_distrib,sum_const,sum_const,card_univ,ZMod.card, ←mul_sum,nsmul_eq_mul,nsmul_eq_mul]; let B:=∑ i:Per N,Real.log (rail i)
 have hB:B≥ -2*v:=log_uniform N; change -(45* (|x|+1))*v^4≤45*(v^3*(v*Real.log μ+2*B+v*(2*Real.log Real.pi))); have hp:0<v:=nPos _; have hu:-(v*x) ≤ v*Real.log μ+2*B+v*(2*Real.log Real.pi):=by unfold x; linarith
 calc
    -(45* (|x|+1))*v^4 ≤ 45*((v^3)*(-(v*x))) := by nlinarith only [mul_le_mul_of_nonneg_right (show x ≤ |x|+1 by linarith [le_abs_self x]) (show 0≤v^4 by positivity)]
    _ ≤ _ := by gcongr
end YM.CF.Window
