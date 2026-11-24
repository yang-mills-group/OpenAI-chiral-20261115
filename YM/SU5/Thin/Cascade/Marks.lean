import YM.SU5.Thin.Cascade.Devices
import YM.SU5.Velvet.Fronds
set_option autoImplicit false
set_option synthInstance.maxSize 8000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Pannier.Damask
end YM.CF.Pannier.Damask
namespace YM.CF.Pannier.Damask.VelvetC
open Filter Function NormedSpace Lattice Wilson Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Branch Dial Nacre Font Laic Graph Skye
open scoped Pointwise Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
open Py.Rate.Pannier
variable {N:Side}{v t u e C a:ℝ} {A0:Loom N} {r d:ℕ}
open RG
-- explicit ramp. outside a dirty halo.
private lemma floraRow (U:Pane N)(x:Seat N)(t: x∉ Lattice.halo r (flags v U))(e:r ≤ (More N).val) (w:v≥0)(s:0≤a) : RayPrice U x (v+2*Real.exp (-(a*r))) a:=by
 intro j
 let A:= (v+2*Real.exp (-(a*r)))
 have he(j:Pec.Ok N)(h:r ≤ Font.dial x j) : ‖silt x j U‖ ≤ A*Real.exp (a*Font.dial x j):=by
    apply (group.curvature_norm _).trans; apply (group.chord_le_two _) |>.trans; unfold A; rw [add_mul]; refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg w (Real.exp_pos _).le)); rw [mul_assoc, ←Real.exp_add]; apply le_mul_of_one_le_right (by norm_num); apply Real.one_le_exp; linarith [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ).mpr h) s]
 cases j with
 | inl i=>
    by_cases f:r < Font.dial x (Sum.inl i); · exact he _ f.le
    have hy: i.1∉ flags v U:= by intro W; apply t; apply halo_spec.mpr; exact ⟨i.1,W,(separation_comm ..).trans_le (le_of_not_gt f)⟩
    let y:=i.1; let p:Face (Per (More N)):= i; have hh: group.chord (faceValue U p) ≤ v:=by
       by_contra! t; exact hy ((flags_spec ..).mpr ⟨i,Work.E01.base_touched _,t⟩)
    apply (group.curvature_norm _).trans; let T:=shiftH x y; have ht:stop x T=y:=stopH ..; rw [Nacre.boot, travel_append,travel_append,stop_append]; simp_rw [show stop x (shiftH x i.1)=i.1 from ht,square_stop]; rw [show travel U i.1 _= _ from (show travel U y (reverse T)=(travel U x T)⁻¹ from (by nth_rw 1 [←ht]; rw [travel_reverse]))]; rw [group.chord_conj]
    exact hh.trans (le_trans (le_add_of_nonneg_right (by positivity)) (le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by positivity))))
 | inr i=> exact he _ e
variable {m:ℕ}
private def Mawk (S:Finset (Seat N)):Finset (Single N):= univ.filter (fun i=> place_x i ∈ S)
open Tenant
private lemma mawk_budget (S:Finset (Seat N)):(Mawk S).card ≤ S.card*180:=by
 let f(i:Single N) := (place_x i, i.1.2,i.2)
 let X:= S ×ˢ (univ: Finset (SpinIdx × SU.Slot))
 have hx(j : Single N)(p:j∈ Mawk S): f j∈ X:= mem_product.mpr ⟨(mem_filter.mp p).2,mem_univ _⟩
 rw [← card_image_of_injective (Mawk S) (show Injective f from fun ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩ e=> by obtain ⟨v,h,w⟩ : x=y ∧ i=k ∧ j=l:= ⟨needle (congrArg Prod.fst e),congrArg (fun i=> i.2.1) e, congrArg (fun i=> i.2.2) e⟩; rw [v,h,w])]
 apply (card_le_card (image_subset_iff.mpr hx)).trans_eq ?_; unfold X; rw [card_product,card_univ,Fintype.card_prod,SU.slots, show Fintype.card SpinIdx=4 from Fintype.card_fin _]
open Fixed.Extensive
private lemma bolt_focus (U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(T:Toy m N)(p:CardK N m T C a)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e)(i:Signed) :
    absEntries (cavil T (Yg (incX i) (A0 U))) ≤ storm U v e r d C m:=by
 let A:= Yg (incX i) (A0 U); let B:= (Lattice.halo d (flags v A)); let H:= Mawk B; let D:=45*((2:ℝ)^m*C); let E:=45*(e^m*C); let y:=quake r d (flakes v U.1); let f(j:Single N) := ∑ k:Single N, ‖cavil T A j k‖
 have hp : 0≤ v+2*Real.exp (-(a*d)):=by positivity
 have ht:0≤E:=by unfold E; have he:=hp.trans q; positivity
 have he:(∑ j,f j) ≤ ∑ j:Single N,(E+if j∈ H then D else 0):=by
    apply sum_le_sum; intro j _; split
    · exact (Fixed.Extensive.cavilRow T p (A0 U) (railT _ _ s) s (by positivity) i j).trans (le_add_of_nonneg_left ht)
    rename_i V; rw [add_zero]; apply le_trans (cavil_row_reduced T p (A0 U) s hp i j (floraRow A (place_x j) (fun k=>V (mem_filter.mpr ⟨mem_univ _,k⟩)) l w s)); unfold E; gcongr
 have hv:B=(Lattice.halo d (flags v (pull i 0 (A0 U)))):=by unfold B A; rw [Ywin i]
 apply he.trans; rw [sum_add_distrib,sum_ite,sum_const,sum_const,sum_const_zero]; simp_rw [card_univ,nsmul_eq_mul,add_zero]; rw [filter_mem_eq_inter,univ_inter]; unfold storm; gcongr
 have hk:= grease_f g U ℓ d i; rw [←hv] at hk
 have hz:= (mawk_budget B).trans (Nat.mul_le_mul_right 180 hk); have he:(H.card:ℝ)≤ y:= by unfold H y quake flakes; exact (Nat.cast_le.mpr hz).trans (Eq.le (by push_cast; ring))
 exact he
open Rapids
lemma step_tall (a:Shape): Filed ((prepU a (spinX a.s) inert N).val:Op (Single N)) 180 := by
 let T:= prepU a (spinX a.s) inert N; let W:=Tofu a N
 let V:= mealU a (spinX a.s) inert N; intro i
 change (∑ j,‖(T.val:Op (Single N)) j i‖) ≤ 180
 let H:=helix N; let k:= H i; let z:=k.1
 have hx (j:Single N) : T.val j i= (V.val:Op (Model N)) (H j) k:=rfl
 simp_rw [hx]; rw [Equiv.sum_comp H (fun i=>‖(V.val : Op (Model N)) i k‖), Fintype.sum_prod_type]; rw [Finset.sum_eq_single (W.symm z)]
 · refine (sum_le_sum (fun i _=> le_trans (norm_entry (V.val:Op (Model N)) _ _) (CStarRing.norm_of_mem_unitary V.property|>.le))).trans_eq ?_; rw [sum_const,nsmul_eq_mul, card_univ,Fintype.card_prod,Fintype.card_fin,SU.slots]; norm_num
 · intro l h p; refine sum_eq_zero fun j _=>?_ ; change ‖jump _ _ _ _‖=0; rw [jump_apply,if_neg,norm_zero]; exact (mt W.apply_eq_iff_eq_symm_apply.mp p) -- equality e l=k.1, k z rfl
 simp
private lemma tide_foil_sum (F:Signed→ FC (Single N)) (C:ℝ){v:ℝ}(H:∀ s,Gall.Pays v (F s) C): Gall.Pays v ((Fintype.card Signed:ℝ)⁻¹ • ∑ s:Signed,F s) C:=by
 let Q:=Fintype.card Signed; have ht:= (Gall.Pays.sumT univ F (fun _=> C) (fun x _=>H x)).linear ((Q:ℝ)⁻¹:ℝ)
 have he : 0<(Q:ℝ):=by unfold Q; exact_mod_cast Fintype.card_pos
 rw [Complex.norm_real,Real.norm_of_nonneg (by positivity),sum_const,card_univ,nsmul_eq_mul, inv_mul_cancel_left₀ he.ne'] at ht -- syntactic Q issue
 exact ht
private lemma glory_dT {h:ℝ}(hH:0≤h)(U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(T:Toy m N)(p:CardK N m T C a)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e) (P:Op (Single N))(Hp:IsStarProjection P){w₀:ℝ} (hn:Filed P w₀)(w₀n:0 ≤ w₀): Gall.Pays h (dg (Kennel.capT P (colorX T (A0 U)))) ( ((1+w₀)^2 * (180^2 * storm U v e r d C m))*h^2):=by
  let Q:=1-P; let K : Op (Single N) →ₗ[ℝ] FC (Single N):=
    { toFun F:=dg (Q*F*P)
      map_add' i j:=by rw [mul_add,add_mul,dg_add]
      map_smul' c F:=by rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc,dg_scale]; rfl }
  let D(s):= Nacre.foil s (cavil T) (A0 U)
  change Gall.Pays h (K (_ • ∑ s:Signed,D s)) _
  rw [map_smul,map_sum]; apply tide_foil_sum; intro i; let L:= cavil T (Yg (incX i⁻¹) (A0 U))
  change Gall.Pays h (dg (Q* Nacre.foil i (cavil T) (A0 U)*P)) _ ; rw [Nacre.foil,Nacre.zone_c]
  apply (narrator hH _).weigh _ hH; apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  have hS: Filed (1-P) (1+w₀):= Filed.from (fun i=> by
     rw [act_sub,act_one]; exact (pony (basisKet i) _).trans (add_le_add (show Gall.dialZ _ ≤1 from by simp [Gall.dialZ, apply_ite (fun x:ℂ=> ‖x‖)]) (hn.dial i)))
  have hpV:Filed (star P) (1+w₀):= Hp.isSelfAdjoint.star_eq.symm ▸ fun i=>le_trans (hn i) (le_add_of_nonneg_left zero_le_one) -- maybe infer
  apply le_trans (assists_op (show 0≤1+w₀ by positivity) hS hpV _); apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); apply (winter_metric (prepU _ (spinX _) inert N) (detX i) L (show 0 ≤ (180:ℝ) by norm_num) (step_tall (incX i))).trans; exact mul_le_mul_of_nonneg_left (bolt_focus U g ℓ s w l T p c e q i⁻¹) (by norm_num)

lemma preparesG {h β γ D:ℝ}{j:ℕ}(R:GramM N)(L:Ledger D β γ a C R)(hH:0≤h)(U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e)(p:IsStarProjection (spar j R.J.M (A0 U))){w₀:ℝ}(hn:Filed (spar j R.J.M (A0 U)) w₀)(w₀n:0≤w₀): Gall.Pays h (dg (actF j R A0 U)) (((1+w₀)^2 * (180^2 * (storm U v e r d C 1+storm U v e r d C 2)))*h^2):=by
 unfold actF Aim.den; rw [Pi.add_apply]; obtain ⟨A,B⟩:= L.field.1
 rw [show ∀ (x y z:Op (Single N)),Kennel.capT x (y+z)=Kennel.capT x y+Kennel.capT x z from fun _ _ _=>by unfold Kennel.capT; rw [mul_add,add_mul],dg_add,mul_add, mul_add,add_mul]
 exact (glory_dT hH U g ℓ s w l _ A c e q _ p hn w₀n).add (glory_dT hH U g ℓ s w l _ B c e q _ p hn w₀n)
open CF.Py.Rate
lemma polar_pang {d r:ℕ}{C h:ℝ}(c:0≤C) (p:0≤h)(e:ℝ)(U:Orbit N)(v:ℝ) : (storm U v e r d C 1+storm U v e r d C 2)*h^2 ≤ (180*45*C*h^2*(e+e^2))*(((N.val:ℕ):ℝ)^4) + (quake r d 1*(45*6*C)*h^2)*flakes v U.1 := by
 apply le_of_eq; unfold storm quake; rw [Pic.units_t (N:=N)]; ring
private lemma snooze (a X:ℝ)(s:0<a)(l:0<X) : ∃ d:ℕ,2*Real.exp (-(a*d)) ≤ X:=by
 apply Filter.Eventually.exists (f:=atTop); have ht:Tendsto (fun i:ℕ=> 2*Real.exp (-(a*i))) atTop (𝓝 0):=by
    simpa only [mul_zero,Function.comp_apply] using (((Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop.const_mul_atTop s))).const_mul 2))
 exact ht.eventually (ge_mem_nhds l)
open Pec
private lemma centV (U:Pane N)(T:Pride N)(j:Site N)(h:Lac T a C)(g:RayPrice U (node j) v a)(e:0≤v):‖tag (node j) (T j) U‖≤v^2*C:=by
 have ht(x t: Ok N): ‖inner ℝ (silt (node j) x U) (silt (node j) t U)‖ ≤ v^2* nick a (contour (node j) x t):=by
    apply (norm_inner_le_norm ..).trans; apply (mul_le_mul (g x) (g t) (norm_nonneg _) (mul_nonneg e (Real.exp_pos _).le)).trans; rw [mul_mul_mul_comm,← Real.exp_add,←mul_add,←sq]; refine mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le (by linarith [ct_pos (node j) x t])) (by positivity)
 apply (norm_sum_le ..).trans; apply (mul_le_mul_of_nonneg_left (h.pay j) (sq_nonneg v)).trans'; simp_rw [Pec.cents,mul_sum]; refine sum_le_sum fun x _=> (norm_sum_le ..).trans (sum_le_sum fun y _=>?_); rw [norm_smul,←mul_assoc]; exact mul_le_mul_of_nonneg_right (ht x y) (norm_nonneg _)
lemma aur_pin (X:Pane N)(T:Pride N)(h:Lac T a C)(U:Orbit N)(p:X=A0 U)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(c:0≤C) (e:ℝ)(q:v+2*Real.exp (-(a*d))≤e) :‖pigment T X‖≤paintE (r:=r) d U v e C:=by
 subst X; apply sealV; intro i; let Y:= A0 U; let Z:=Yg (incX i) Y; let K:= (Lattice.halo d (flags v Z)); let V:= univ.filter (fun j:Site N=> node j ∈ K)
 have hv: (V.card:ℝ) ≤ quake r d 1 * flakes v U.1:=by
    rw [← card_image_of_injective V (Tenant.needle)]; have hz: (Lattice.halo d (flags v Z))=(Lattice.halo d (flags v (pull i 0 (A0 U)))):=by unfold Z Y; rw [Ywin i];
    have he:= (card_le_card (show V.image node ⊆ K from image_subset_iff.mpr fun j v=>(mem_filter.mp v).2)).trans (show K.card ≤ (((roughness v U.1).card*4*((r+4)*2+1)^4)*(d+d+1)^4) from (by unfold K; rw [hz]; exact grease_f g U ℓ d i)); let n:= (((roughness v U.1).card*4*((r+4)*2+1)^4)*(d+d+1)^4); apply le_trans (Nat.cast_le.mpr he); change (n:ℝ) ≤ quake _ _ 1 * flakes v U.1;
    rw [show quake r d 1 * flakes v U.1=(n:ℝ)*180 from (by unfold quake n flakes; push_cast; ring)]; exact le_mul_of_one_le_right (Nat.cast_nonneg _) (by norm_num) -- need normalizing cast
 let E0:= 2^2*C
 have hE: ∀ t:Site N, ‖tag (node t) (T t) Z‖ ≤ e^2*C+ (if t∈ V then E0 else 0):=by
    intro t; split; next _=> exact (centV Z T t h (fun u=>(railT (A0 U) _ s).fee i _ u) (by norm_num : (0:ℝ)≤2)).trans (le_add_of_nonneg_left (by positivity : 0≤ e^2 *C)) -- scope rfl?
    next p=>
      have hp:v+2*Real.exp (-(a*d))≥0:=by positivity
      rw [add_zero]; exact (centV Z T t h (floraRow Z (node t) (fun v=>p (mem_filter.mpr ⟨mem_univ _,v⟩)) l w s) hp).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp q _) c)
 let F:=zinger T Z; have he:‖F‖ ≤ paintE (r:=r) d U v e C:=by
    apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun t=> e^2*C+(if t∈ V then E0 else 0)) fun j _=>hE j).trans ?_); rw [sum_add_distrib,sum_ite,sum_const_zero,sum_const,sum_const,nsmul_eq_mul,nsmul_eq_mul, add_zero, filter_mem_eq_inter,univ_inter,card_univ,site_card,Nat.cast_pow]
    exact le_trans (add_le_add_right (mul_le_mul_of_nonneg_right hv (show 0≤ E0 by unfold E0; positivity)) _) (Eq.le (by unfold paintE pittance E0; ring))
 rw [complX]; unfold cSignX; split <;> (try rw [norm_star]) <;> exact he

end YM.CF.Pannier.Damask.VelvetC