import YM.SU5.Velvet.Fronds
import Verses.Policy
/-! # Wisp ecost. Adapted from `Exacts` (private tools copied to this namespace), `Graph/Zing` -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
set_option maxHeartbeats 200000
noncomputable section
namespace YM.CF.Pannier.Damask
namespace VelvetC
open Filter Function NormedSpace Lattice Wilson Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Branch Dial Nacre Font Laic Graph Skye
open scoped Pointwise Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
open Py.Rate.Pannier
variable {N:Side}{v t u e C a:ℝ} {A0:Loom N} {r d:ℕ}
open RG
-- explicit ramp. outside a dirty halo.
private lemma leafRow (U:Pane N)(x:Seat N)(t: x∉ Lattice.halo r (flags v U))(e:r ≤ (More N).val) (w:v≥0)(s:0≤a) : RayPrice U x (v+2*Real.exp (-(a*r))) a:=by
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
private def Hawk (S:Finset (Seat N)):Finset (Single N):= univ.filter (fun i=> place_x i ∈ S)
open Tenant
private lemma hawk_budget (S:Finset (Seat N)):(Hawk S).card ≤ S.card*180:=by
 let f(i:Single N) := (place_x i, i.1.2,i.2)
 let X:= S ×ˢ (univ: Finset (SpinIdx × SU.Slot))
 have hx(j : Single N)(p:j∈ Hawk S): f j∈ X:= mem_product.mpr ⟨(mem_filter.mp p).2,mem_univ _⟩
 rw [← card_image_of_injective (Hawk S) (show Injective f from fun ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩ e=> by obtain ⟨v,h,w⟩ : x=y ∧ i=k ∧ j=l:= ⟨needle (congrArg Prod.fst e),congrArg (fun i=> i.2.1) e, congrArg (fun i=> i.2.2) e⟩; rw [v,h,w])]
 apply (card_le_card (image_subset_iff.mpr hx)).trans_eq ?_; unfold X; rw [card_product,card_univ,Fintype.card_prod,SU.slots, show Fintype.card SpinIdx=4 from Fintype.card_fin _]
open Fixed.Extensive
lemma bolt_cleat (U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(T:Toy m N)(p:CardK N m T C a)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e)(i:Signed) :
    absEntries (cavil T (Yg (incX i) (A0 U))) ≤ storm U v e r d C m:=by
 let A:= Yg (incX i) (A0 U); let B:= (Lattice.halo d (flags v A)); let H:= Hawk B; let D:=45*((2:ℝ)^m*C); let E:=45*(e^m*C); let y:=quake r d (flakes v U.1); let f(j:Single N) := ∑ k:Single N, ‖cavil T A j k‖
 have hp : 0≤ v+2*Real.exp (-(a*d)):=by positivity
 have ht:0≤E:=by unfold E; have he:=hp.trans q; positivity
 have he:(∑ j,f j) ≤ ∑ j:Single N,(E+if j∈ H then D else 0):=by
    apply sum_le_sum; intro j _; split
    · exact (Fixed.Extensive.cavilRow T p (A0 U) (railT _ _ s) s (by positivity) i j).trans (le_add_of_nonneg_left ht)
    rename_i V; rw [add_zero]; apply le_trans (cavil_row_reduced T p (A0 U) s hp i j (leafRow A (place_x j) (fun k=>V (mem_filter.mpr ⟨mem_univ _,k⟩)) l w s)); unfold E; gcongr
 have hv:B=(Lattice.halo d (flags v (pull i 0 (A0 U)))):=by unfold B A; rw [Ywin i]
 apply he.trans; rw [sum_add_distrib,sum_ite,sum_const,sum_const,sum_const_zero]; simp_rw [card_univ,nsmul_eq_mul,add_zero]; rw [filter_mem_eq_inter,univ_inter]; unfold storm; gcongr
 have hk:= grease_f g U ℓ d i; rw [←hv] at hk
 have hz:= (hawk_budget B).trans (Nat.mul_le_mul_right 180 hk); have he:(H.card:ℝ)≤ y:= by unfold H y quake flakes; exact (Nat.cast_le.mpr hz).trans (Eq.le (by push_cast; ring))
 exact he
open Graph CF.Papyrus.Franc.Verses CF.Window
lemma loose_sum {α:Type}[Fintype α](F:α→ Op (Single N))(K:α→ℝ)(f:∀ i,entryBudget (F i) ≤ K i) : entryBudget (∑ i,F i) ≤ ∑ i,K i:=by
 unfold entryBudget; simp_rw [Matrix.sum_apply]; refine (sum_le_sum (s:=univ) (fun i hi=>sum_le_sum (s:=univ) (fun j _=>norm_sum_le ..))).trans ?_; rw [←sum_rotate F]; exact sum_le_sum (fun i _=> f i)
where
 sum_rotate (F:α→Op (Single N)): (∑ a:α,entryBudget (F a)) = ∑ i,∑ j,∑ a:α, ‖F a i j‖:=by
    unfold entryBudget; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_comm]
lemma shade_cost (U:Orbit N)(g:Roof N u t r A0)(l:v ≤ u)(s:0≤a)(w:v≥0)(ζ:d≤(More N).val)(T:Toy m N)(p:CardK N m T C a)(c:0≤C)(e:ℝ)(h:v+2*Real.exp (-(a*d))≤e) : entryBudget (colorX T (A0 U)) ≤ 180*180*storm U v e r d C m:=by
 let Y(s:Signed):= Nacre.foil s (cavil T) (A0 U); let z:=storm U v e r d C m; let H:=180*180*z
 have hp (i:Signed) : entryBudget (Y i) ≤ H:=by
    unfold Y Nacre.foil; rw [zone_c]; unfold Thera.jazz; split; swap; · exact (twist_budget i _).trans (mul_le_mul_of_nonneg_left (bolt_cleat U g l s w ζ T p c e h i⁻¹) (by positivity))
    unfold entryBudget; simp_rw [Matrix.neg_apply,norm_neg]; change entryBudget (star _)≤_; rw [entryBudget_adjoint]; exact (twist_budget i _).trans (mul_le_mul_of_nonneg_left (bolt_cleat U g l s w ζ T p c e h i⁻¹) (by positivity))
 let Q:ℝ:=Fintype.card Signed; let L:= ∑ i,Y i; have he:0<Q:= Nat.cast_pos.mpr Fintype.card_pos
 change entryBudget (_ • L)≤ H
 rw [show entryBudget ((Fintype.card Signed:ℝ)⁻¹ • L) = Q⁻¹*entryBudget L from (?_)]
 · refine (mul_le_mul_of_nonneg_left (loose_sum Y _ hp) (inv_pos.mpr he).le).trans_eq ?_; rw [sum_const,card_univ,nsmul_eq_mul]; exact inv_mul_cancel_left₀ he.ne' H
 unfold entryBudget; unfold Q at *; simp_rw [Matrix.smul_apply,norm_smul, Real.norm_of_nonneg (inv_pos.mpr he).le, Finset.mul_sum]
open Pec
abbrev sumPenn (d:ℕ)(U:Orbit N)(v y C:ℝ):ℝ:=pittance N y C+ quake r d 1*4*C*flakes v U.1
private lemma cents_i (U:Pane N)(T:Pride N)(j:Site N)(h:Lac T a C)(g:RayPrice U (node j) v a)(e:0≤v):‖tag (node j) (T j) U‖≤v^2*C:=by
 have ht(x t: Ok N): ‖inner ℝ (silt (node j) x U) (silt (node j) t U)‖ ≤ v^2* nick a (contour (node j) x t):=by
    apply (norm_inner_le_norm ..).trans; apply (mul_le_mul (g x) (g t) (norm_nonneg _) (mul_nonneg e (Real.exp_pos _).le)).trans; rw [mul_mul_mul_comm,← Real.exp_add,←mul_add,←sq]; refine mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le (by linarith [ct_pos (node j) x t])) (by positivity)
 apply (norm_sum_le ..).trans; apply (mul_le_mul_of_nonneg_left (h.pay j) (sq_nonneg v)).trans'; simp_rw [Pec.cents,mul_sum]; refine sum_le_sum fun x _=> (norm_sum_le ..).trans (sum_le_sum fun y _=>?_); rw [norm_smul,←mul_assoc]; exact mul_le_mul_of_nonneg_right (ht x y) (norm_nonneg _)
lemma aurPennant (X:Pane N)(T:Pride N)(h:Lac T a C)(U:Orbit N)(p:X=A0 U)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(c:0≤C) (e:ℝ)(q:v+2*Real.exp (-(a*d))≤e) :‖pigment T X‖≤ sumPenn (r:=r) d U v e C:=by
 subst X; apply sealV; intro i; let Y:= A0 U; let Z:=Yg (incX i) Y; let K:= (Lattice.halo d (flags v Z)); let V:= univ.filter (fun j:Site N=> node j ∈ K)
 have hv: (V.card:ℝ) ≤ quake r d 1 * flakes v U.1:=by
    rw [← card_image_of_injective V (Tenant.needle)]; have hz: (Lattice.halo d (flags v Z))=(Lattice.halo d (flags v (pull i 0 (A0 U)))):=by unfold Z Y; rw [Ywin i];
    have he:= (card_le_card (show V.image node ⊆ K from image_subset_iff.mpr fun j v=>(mem_filter.mp v).2)).trans (show K.card ≤ (((roughness v U.1).card*4*((r+4)*2+1)^4)*(d+d+1)^4) from (by unfold K; rw [hz]; exact grease_f g U ℓ d i)); let n:= (((roughness v U.1).card*4*((r+4)*2+1)^4)*(d+d+1)^4); apply le_trans (Nat.cast_le.mpr he); change (n:ℝ) ≤ quake _ _ 1 * flakes v U.1;
    rw [show quake r d 1 * flakes v U.1=(n:ℝ)*180 from (by unfold quake n flakes; push_cast; ring)]; exact le_mul_of_one_le_right (Nat.cast_nonneg _) (by norm_num) -- need normalizing cast
 let E0:= 2^2*C
 have hE: ∀ t:Site N, ‖tag (node t) (T t) Z‖ ≤ e^2*C+ (if t∈ V then E0 else 0):=by
    intro t; split; next _=> exact (cents_i Z T t h (fun u=>(railT (A0 U) _ s).fee i _ u) (by norm_num : (0:ℝ)≤2)).trans (le_add_of_nonneg_left (by positivity : 0≤ e^2 *C)) -- scope rfl?
    next p=>
      have hp:v+2*Real.exp (-(a*d))≥0:=by positivity
      rw [add_zero]; exact (cents_i Z T t h (leafRow Z (node t) (fun v=>p (mem_filter.mpr ⟨mem_univ _,v⟩)) l w s) hp).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp q _) c)
 let F:=zinger T Z; have he:‖F‖ ≤ sumPenn (r:=r) d U v e C:=by
    apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun t=> e^2*C+(if t∈ V then E0 else 0)) fun j _=>hE j).trans ?_); rw [sum_add_distrib,sum_ite,sum_const_zero,sum_const,sum_const,nsmul_eq_mul,nsmul_eq_mul, add_zero, filter_mem_eq_inter,univ_inter,card_univ,site_card,Nat.cast_pow]
    exact le_trans (add_le_add_right (mul_le_mul_of_nonneg_right hv (show 0≤ E0 by unfold E0; positivity)) _) (Eq.le (by unfold sumPenn pittance E0; ring))
 rw [complX]; unfold cSignX; split <;> (try rw [norm_star]) <;> exact he

variable {γ ψ₁ ψ₂ :ℝ}
lemma renewal_mini (U:Orbit N)(R: GramM N)(L: Ledger γ ψ₁ ψ₂ a C R)(g:Roof N u t r A0) (l:v ≤ u)(s:0≤a)(w:v≥0)(ζ:d≤(More N).val)(c:0≤C)(e:ℝ)(h:v+2*Real.exp (-(a*d))≤e): entryBudget (R.J.P.den (A0 U)) ≤ 180*180*(storm U v e r d C 1+storm U v e r d C 2) ∧ ‖Pec.pigment R.J.I (A0 U)‖≤VelvetC.paintE (r:=r) d U v e C :=by
 obtain ⟨⟨hf,hv⟩,hm⟩:= L.field
 refine ⟨?_,aurPennant _ _ hm U rfl g l s w ζ c e h⟩
 unfold Aim.den; rw [Pi.add_apply]; -- tune
 apply le_trans _ ((add_le_add (shade_cost U g l s w ζ _ hf c e h) (shade_cost U g l s w ζ _ hv c e h)).trans_eq ((mul_add ..).symm))
 unfold entryBudget; rw [←sum_add_distrib]; apply sum_le_sum; intro i _; rw [←sum_add_distrib]; exact sum_le_sum (fun _ _=> norm_add_le ..)
end VelvetC
end YM.CF.Pannier.Damask
