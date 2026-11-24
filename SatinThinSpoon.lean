import YM.SU5.Relativistic.Roscoe

/-! expose fine cost before summability weighting, for payment at new outer threshold.
 Retain proof essentially from Roscoe for these bills. -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Pannier.Damask
open Filter Function NormedSpace Lattice Wilson Finset Cube SU Fock Lat Spire Scroll Peaks Drapes Rush Tulip Pastry Scree Girt Branch Dial Nacre Font Laic Graph Skye
open scoped Pointwise Topology ContDiff Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Classical
attribute [local instance] opCStarAlgebra
open Py.Rate.Pannier
variable {N:Side}{v t u e C a:ℝ} {A0:Loom N} {r d:ℕ}
open RG
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
lemma flak_budget (S:Finset (Seat N)):(Hawk S).card ≤ S.card*180:=by
 let f(i:Single N) := (place_x i, i.1.2,i.2)
 let X:= S ×ˢ (univ: Finset (SpinIdx × SU.Slot))
 have hx(j : Single N)(p:j∈ Hawk S): f j∈ X:= mem_product.mpr ⟨(mem_filter.mp p).2,mem_univ _⟩
 rw [← card_image_of_injective (Hawk S) (show Injective f from fun ⟨⟨x,i⟩,j⟩ ⟨⟨y,k⟩,l⟩ e=> by obtain ⟨v,h,w⟩ : x=y ∧ i=k ∧ j=l:= ⟨needle (congrArg Prod.fst e),congrArg (fun i=> i.2.1) e, congrArg (fun i=> i.2.2) e⟩; rw [v,h,w])]
 apply (card_le_card (image_subset_iff.mpr hx)).trans_eq ?_; unfold X; rw [card_product,card_univ,Fintype.card_prod,SU.slots, show Fintype.card SpinIdx=4 from Fintype.card_fin _]
open Fixed.Extensive
lemma bolt_law (U:Orbit N)(g:Roof N u t r A0)(ℓ:v ≤ u)(s:0≤a)(w:v≥0)(l:d≤(More N).val)(T:Toy m N)(p:CardK N m T C a)(c:0 ≤ C)(e:ℝ)(q:v+2*Real.exp (-(a*d))≤e)(i:Signed) :
    absEntries (cavil T (Yg (Nacre.incX i) (A0 U))) ≤ storm U v e r d C m:=by
 let A:= Yg (Nacre.incX i) (A0 U); let B:= (Lattice.halo d (flags v A)); let H:= Hawk B; let D:=45*((2:ℝ)^m*C); let E:=45*(e^m*C); let y:=quake r d (flakes v U.1); let f(j:Single N) := ∑ k:Single N, ‖cavil T A j k‖
 have hp : 0≤ v+2*Real.exp (-(a*d)):=by positivity
 have ht:0≤E:=by unfold E; have he:=hp.trans q; positivity
 have he:(∑ j,f j) ≤ ∑ j:Single N,(E+if j∈ H then D else 0):=by
    apply sum_le_sum; intro j _; split
    · exact (Fixed.Extensive.cavilRow T p (A0 U) (railT _ _ s) s (by positivity) i j).trans (le_add_of_nonneg_left ht)
    rename_i V; rw [add_zero]; apply le_trans (cavil_row_reduced T p (A0 U) s hp i j (leafRow A (place_x j) (fun k=>V (mem_filter.mpr ⟨mem_univ _,k⟩)) l w s)); unfold E; gcongr
 have hv:B=(Lattice.halo d (flags v (pull i 0 (A0 U)))):=by unfold B A; rw [Ywin i]
 apply he.trans; rw [sum_add_distrib,sum_ite,sum_const,sum_const,sum_const_zero]; simp_rw [card_univ,nsmul_eq_mul,add_zero]; rw [filter_mem_eq_inter,univ_inter]; unfold storm; gcongr
 have hk:= grease_f g U ℓ d i; rw [←hv] at hk
 have hz:= (flak_budget B).trans (Nat.mul_le_mul_right 180 hk); have he:(H.card:ℝ)≤ y:= by unfold H y quake flakes; exact (Nat.cast_le.mpr hz).trans (Eq.le (by push_cast; ring))
 exact he

def rimedR(r d:ℕ)(η:ℝ):=4*η*(((r+4)*2+1:ℕ)^4:ℕ)*((d+d+1:ℕ)^4:ℕ)
lemma pigment_petite (p:Pec.Pride N)(v':Pec.Lac p a C)(U:Orbit N)(g:Roof N u t r A0)(ℓ:v≤ u) (x:0≤v)(y:0≤a)(w:0≤ C)(l:d ≤(More N).val)(e:ℝ)(q:v+2*Real.exp (-(a*d)) ≤ e) : ‖Pec.pigment p (A0 U)‖ ≤ (N.val:ℝ)^4*(C*e^2)+rimedR r d (flakes v U.1)*(C*4):=by
 apply sealV; intro i; let V:=Yg (Nacre.incX i) (A0 U); let B:= Lattice.halo d (RG.flags v V); let S:= (univ:Finset (Site N)).filter fun i=> node i∈ B; have he:S.card ≤ B.card:=by rw [←card_image_of_injective S Tenant.needle]; exact card_le_card (image_subset_iff.mpr fun _ x=> (mem_filter.mp x).2)
 have hp:(B.card:ℝ)≤ rimedR r d (flakes v U.1):=by have ht:= grease_f g U ℓ d i; unfold B V; rw [Ywin]; exact (Nat.cast_le.mpr ht).trans_eq (by unfold rimedR flakes; push_cast; ring)
 have hz (e:ℝ)(x:Site N)(z:0 ≤ e)(w:RayPrice V (node x) e a) : ‖Pec.tag (node x) (p x) V‖ ≤ C*e^2:=by
    let n:= node x
    have ht(i j:Pec.Ok N): ‖inner ℝ (silt n i V) (silt n j V)‖≤ e^2* nick a (contour n i j):=by
       apply (norm_inner_le_norm ..).trans; apply (mul_le_mul (w i) (w j) (norm_nonneg _) (mul_nonneg z (Real.exp_pos _).le)).trans; rw [mul_mul_mul_comm,← Real.exp_add,←mul_add,←sq]; refine mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (Real.exp_pos _).le (by linarith [ct_pos (node x) i j])) (by positivity)
    apply (norm_sum_le ..).trans; apply le_trans (b:= Pec.cents n (p x) a *e^2) _ (mul_le_mul_of_nonneg_right (v'.pay x) (sq_nonneg _)); unfold Pec.cents; simp_rw [sum_mul]; refine sum_le_sum fun i _=> ?_; apply (norm_sum_le ..).trans; refine sum_le_sum fun j _=>?_ ; rw [norm_smul]; exact (mul_le_mul_of_nonneg_right (ht i j) (norm_nonneg _)).trans_eq (by ring)
 rw [Pec.complX]; have hq(j): ‖cSignX (detX i) j‖= ‖j‖:=by unfold cSignX; split; simp; rfl
 rw [hq]; change ‖Pec.zinger p V‖≤_; apply (norm_sum_le ..).trans
 have hh:=show 0≤ v+2*Real.exp (-(a*d)) from by positivity
 let f(x:Site N):=C*e^2+if x∈S then C*4 else 0
 refine (sum_le_sum (g:=f) ?_).trans ?_
 · intro j g; change ‖Pec.tag (node j) (p j) V‖≤ f j; unfold f; split
   next h=>
      refine (hz 2 _ zero_le_two (fun s=> (railT (A0 U) a y|>.fee i (node j) s))).trans (by have ht:=mul_nonneg w (sq_nonneg e); linarith)
   next h=>
      obtain ht:= leafRow V (node j) (fun g=>h (mem_filter.mpr ⟨mem_univ _,g⟩)) l x y
      rw [add_zero]; exact (hz _ j hh ht).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hh q _) w)
 unfold f; rw [sum_add_distrib,sum_const, ← sum_filter]; simp only [filter_mem_eq_inter, univ_inter,sum_const,card_univ,site_card,nsmul_eq_mul,Nat.cast_pow]; exact add_le_add_right (mul_le_mul_of_nonneg_right ((Nat.cast_le.mpr he).trans hp) (by positivity)) _


end YM.CF.Pannier.Damask
