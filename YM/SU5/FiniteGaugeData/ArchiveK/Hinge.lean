import YM.SU5.FiniteGaugeData.ArchiveK.Groove
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
set_option linter.unusedSimpArgs false
namespace Violas
-- Q rank lerh.forge
open LinearMap Submodule Module
variable {X Y Z J:Type*}[Fintype X][Fintype Y][Fintype Z][Fintype J][DecidableEq X][DecidableEq Y][DecidableEq Z][DecidableEq J]
variable {V:PlansM X}{a:ℝ}(M:Ruler Y X)(h:0<a)(p:∀ x∈V,a*‖x‖≤‖ract M x‖)
include h p
lemma heave (n:ℕ)(q:n≤dim V) :∃ S:Ruler X (Fin n),‖S‖≤ a⁻¹ ∧ (M*S)ᴴ*(M*S)=1 ∧ ∀ i: Ket (Fin n), ract S i∈ V:=by
 let f : V→ₗ[ℂ] Ket Y:= (ract M).toLinearMap.comp V.subtype; have hf:Injective f:= by
    rw [← LinearMap.ker_eq_bot]; apply LinearMap.ker_eq_bot'.2; intro x hv; have ht:= p x.val x.property; change ract M x.val=0 at hv; rw [hv,norm_zero] at ht; apply Subtype.ext; exact norm_le_zero_iff.mp ((nonpos_of_mul_nonpos_right ht h)) -- tune
 let U:= LinearMap.range f; let G:V≃ₗ[ℂ]U:=LinearEquiv.ofInjective f hf; obtain ⟨L,v,H⟩:= ward U n (q.trans_eq (LinearEquiv.finrank_eq G)); let A: Ket (Fin n)→ₗ[ℂ] U:= (ract L).toLinearMap.codRestrict U H; let S: Ruler X (Fin n):= ract.symm (V.subtype.comp (G.symm.toLinearMap.comp A)).toContinuousLinearMap; have hS(i:Ket (Fin n)) : ract S i=(G.symm (A i)).val:=by unfold S; rw [LinearEquiv.apply_symm_apply]; rfl
 have he(i:Ket (Fin n)) : ract (M*S) i=ract L i:=by rw [Largo.R_mul,hS]; exact congrArg Subtype.val (G.apply_symm_apply (A i))
 have ht(i:Ket (Fin n)) : ract S i∈ V:= hS i |>.symm ▸ Subtype.property _ -- tune types
 have hp:M*S=L:= ract.injective (ContinuousLinearMap.ext he); rw [←hp] at v; refine ⟨S,?_,v,ht⟩; rw [←R_pay]; refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun i=>?_); have hv:= p _ (ht i); rw [← Largo.R_mul,ract_orth _ v] at hv; exact le_of_mul_le_mul_left (le_trans hv (le_of_eq (mul_inv_cancel_left₀ h.ne' ‖i‖).symm)) h
 -- wrong argument.
#print axioms heave
end Violas
namespace Midway
open LightK Violas Waltz
local notation "Ω"=> plusHalf
local notation "Γ"=> emitX
variable (A B:Finset Cover) (z x:Cover) (u v:SpinIdx)
abbrev fuelR(B:Finset Cover) (x:Cover): Ruler SpinIdx (Beam B):=Matrix.of fun i j=> fpS (x-j.1.val) i j.2
abbrev Xx(A:Finset Cover) : Finset (Beam A):=univ ×ˢ plusHalf
abbrev bowl₀:= cutM plusHalf
lemma keel_p : ‖keel‖ ≤ 1 := keel_cut ▸ cutBud _
lemma zig_Q : bowl₀*(spiral (emitX x)*keel)=spiral (emitX x)*keel:=by unfold bowl₀; rw [←show Aop= _ from Adef.trans raising.symm,←mul_assoc,zig,mul_assoc,keel_song]
lemma zig_p : keel*(spiral (emitX x)* keel)=0:=by rw [←mul_assoc,zig_z, mul_assoc, keel_snow.1,mul_zero]
lemma fp_true(p:u∈plusHalf) : fpS x u v=(spiral (emitX x)*keel) u v:=by
 unfold fpS; rw [Matrix.add_apply]; suffices he:(if x=0 then keel else 0) u v=0 by rw [he,zero_add]
 split; swap; · rfl
 rw [←keel_cut]; by_cases h:u=v; · subst v; simp [cutM,p]
 simp [cutM,Matrix.diagonal_apply,h]
lemma fp_zz(p:u∈(plusHalf)ᶜ)(q:x≠0): fpS x u v=0:=by
 let U:= spiral (emitX x)* keel; have he: keel*U=0:=zig_p _; rw [←keel_cut] at he; unfold fpS; rw [if_neg q,zero_add]; change U u v=0; rw [show U u v=(cutM (plusHalf)ᶜ*U) u v from (by rw [compass, if_pos p]), he]; rfl
lemma pick_feather : cutM (Xx A)*Pick A B=Pick A B:=by
 apply Matrix.ext; intro i j; rw [compass]; let U:=emitX (i.1.val-j.1.val); by_cases p:i∈Xx A; · rw [if_pos p]
 have ht: i.2∉plusHalf:= fun t=>p (mem_product.mpr ⟨mem_univ _,t⟩);
 rw [if_neg p]; have he:cutM plusHalf*(spiral U*keel)=spiral U*keel:= zig_Q _; exact (if_neg ht).symm.trans ((compass ..).symm.trans (congr_fun (congr_fun he _) _)) -- unfold
lemma axiom_bud_fp : ∃ b:ℝ,0<b∧∀ x:Cover, ‖fpS x‖ ≤ b:= by
 let U(i:Axis):= ∫ y:E4,‖ironQ y i‖; let b₀(i):= (gain⁻¹ * U i)* ‖drizzle i‖; let b:= ∑ i:Axis,b₀ i; have hf:0≤b:=Finset.sum_nonneg fun i _=> by have ht:=gain_h; have hh:0≤U i:=integral_nonneg fun _=>norm_nonneg _; unfold b₀; positivity
 have he:‖keel‖ ≤1:= keel_p; refine ⟨1+b,add_pos_of_pos_of_nonneg zero_lt_one hf, fun x=>?_⟩; unfold fpS; refine (norm_add_le ..).trans (add_le_add ?_ (le_trans (norm_mul_le ..) ((mul_le_of_le_one_right (norm_nonneg _) he).trans ?_))); · split; exact he; simp
 unfold spiral; apply (norm_sum_le ..).trans; refine Finset.sum_le_sum (fun i _=>?_); rw [norm_smul, norm_mul,Complex.norm_real,Real.norm_of_nonneg (inv_nonneg.mpr gain_h.le)]; apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sax_budget ..) (inv_nonneg.mpr gain_h.le)) (norm_nonneg _)
section leak
variable {u b r c:ℝ}{j d:ℕ}{X:Type*}[Fintype X][DecidableEq X]
local notation "Χ"=> page X
abbrev Invoice(n:ℕ):= (BddT n) × SpinIdx
local notation "Ψ"=> Beam B
local notation "Σ"=> Invoice j
local notation "V"=> BddT j
def tubeman(n:ℕ): Ruler (Invoice n) (Beam B):= Matrix.of fun i p=> if i.2 = p.2 then arcX n (-emitX p.1.val) i.1.val else 0
local notation "F"=> tubeman B j
include u
omit u -- dummy removals
lemma candle (p:0<r) (t:r≤1) (hex:∀ a∈ B, River r (emitX x) (emitX a)) (Z:x∉ B)(M:Ruler Ψ X)(u:tubeman B j*M=0) : ‖fuelR B x * M‖ ≤ (4 * page (Beam B)*rover*r^j)*‖M‖:=by
 let Y:Ruler SpinIdx (Invoice j):= Matrix.of fun i v=> (spectx v.1.val (Γ x)*keel) i v.2
 let B':tubeman B j*M=0:=u
 have hp: fuelR B x*M=(fuelR B x-Y*tubeman B j)*M:=by rw [Matrix.sub_mul,Matrix.mul_assoc,B', Matrix.mul_zero, sub_zero]
 let H:= Y*tubeman B j; have he (i:SpinIdx)(v:Beam B): H i v=∑ k∈ coon j, (arcX j (-Γ v.1.val) k)*(spectx k (Γ x)*keel) i v.2 := by
    unfold H; rw [Matrix.mul_apply]; unfold Y tubeman; simp_rw [Invoice,Fintype.sum_prod_type,Matrix.of_apply,mul_ite,mul_zero,Finset.sum_ite_eq',mem_univ, if_true]; rw [←Finset.sum_coe_sort (coon j)]; refine sum_congr rfl (fun i _=>mul_comm ..) -- tune sum_ite direction
 let e:=rover*r^j; have hb(i:SpinIdx)(v:Ψ): ‖(fuelR B x-H) i v‖ ≤ e := by
    let A:=v.1.val; let X:= Γ x; let V':=-Γ A; have ha:A∈ B:= v.1.property; have hQ:River r X V':=(by unfold X V'; simpa only [River,norm_neg] using hex A ha);
    let δ:=spiral (X+ V'); rw [Matrix.sub_apply, he]; unfold fuelR fpS; rw [Matrix.of_apply, if_neg (show ¬x-v.1.val= 0 from fun p=>Z ((sub_eq_zero.mp p).symm ▸ ha)),zero_add,emit_sub]; -- rewrite δ. factor
    let J:= δ-∑ k∈ coon j,arcX j V' k • spectx k X; have h0 : ‖J *keel‖ ≤ e:= (norm_mul_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) keel_p).trans (roverPt V' j X p t hQ.1 hQ.2)); refine (le_trans (le_of_eq ?_) ((mTouch (J*keel) i v.2).trans h0)); refine congrArg norm ?_; unfold J; simp_rw [sub_mul,Matrix.sum_mul,Matrix.sub_apply,Matrix.sum_apply,Matrix.smul_mul,Matrix.smul_apply,smul_eq_mul]; unfold spectx; simp_rw [Matrix.sum_mul, Matrix.sum_apply,Matrix.smul_mul,Matrix.smul_apply,smul_eq_mul]; rfl -- precedence
 rw [hp]; apply (Matrix.l2_opNorm_mul ..).trans; apply mul_le_mul_of_nonneg_right _ (norm_nonneg M); apply (jingle _ e (mul_nonneg rover_n (pow_nonneg p.le _)) hb).trans; unfold e page; rw [Fintype.card_fin]; push_cast; ring_nf; exact le_rfl
#print axioms candle
end leak
end Midway
end YM.CF.Window.ArchiveK
