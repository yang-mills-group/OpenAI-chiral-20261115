import Anomaly.PitchMark
/-! Variation with only menu distance on the still-original P/U mask costs. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Skye Jet Scroll Finset
open RG MeasureTheory Salt Metric Drapes Tulip Lat Branch Cube Tenant Rill
open Buffered StressExchange
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Moto Oath Font Haro Spire Dial
variable {N : Side}
local notation "Ω" => Single N
local notation "T"=>More N
abbrev levΦ (k:ℕ)(d:ℝ)(i:ℝ):= (k:ℝ)*(Fintype.card Axis:ℝ)*i/|d|
variable {d a v e u c:ℝ}{b r k:ℕ}
lemma leg_bound (S: Support T)(h:S.card ≤ k): (Tenant.leaks S).card ≤ k*Fintype.card Axis:=by
 refine (Finset.card_le_card (show leaks S ⊆ S ×ˢ (univ:Finset Axis) from ?_)).trans (?_); swap; · rw [card_product,card_univ]; exact Nat.mul_le_mul_right _ h
 intro i t; exact mem_product.mpr ⟨(mem_filter.mp t).2.1,mem_univ _⟩
variable {o:Site N}{F:SOp N}{P:BudgetPoint}{K:Scree.Loom N}
variable (h: Roof N e d r K)(l:0<d)(g:Trunk (node o) F k a v d) (p:P.threshold ≤ e) (t:k+r+10 ≤ P.B)(ha:0 ≤ a)
local notation "Φ"=>pinMatrix P K (node o) F
include h g p l t ha
lemma billed_menu (X Y:Pane N)(Hx:pingS P.threshold (offsetMask P.B o) X)(Hy:pingS P.threshold (offsetMask P.B o) Y)(u0:0 ≤ u)(H:∀ i∈leaks (offsetMask k o),‖Tulip.profile X i-Tulip.profile Y i‖≤u):
 (∑ i:Ω,∑ j:Ω,‖(pinMatrix P K (node o) F X-pinMatrix P K (node o) F Y) i j‖) ≤ levΦ k d u * v := by
 let x:Orbit N:=(X,Classical.arbitrary _); let y:Orbit N:=(Y,Classical.arbitrary _)
 let px:=roller l h x; let py:=roller l h y
 obtain ⟨W,C,c,b,L,Z⟩:=g.home
 have he : Φ X=∑ i,W i px:= (pinMatrix_active h l g p t x Hx).trans (Z px)
 have hh : Φ Y=∑ i,W i py:= (pinMatrix_active h l g p t y Hy).trans (Z py)
 let X0:=offsetMask k o; let D:= levΦ k d u
 have hv(S:Support T)(q:C S≠0): (forum N d).eval S px py≤ D:=by
    change Tulip.fare S (profile _) (profile _)/ _ ≤ _
    let Z : Vow.Aura N := ⟨halo P.B {node o},node o,halo_subset P.B _ (mem_singleton_self _)⟩
    have hw:= footprintGeodesic (f_then (c S) q) (b S q).1 (b S q).2.le
    have hf : halo (r+10) S ⊆ Z.val:=by intro i hi; obtain ⟨j,t',V⟩:=halo_spec.mp hi; obtain ⟨q,u,e⟩:=halo_spec.mp (hw t'); exact halo_spec.mpr ⟨q,u,(separation_triangle _ j _).trans (by omega)⟩
    have h0 (X:Orbit N)(Y:pingS P.threshold (offsetMask P.B o) X.1) : Agrees S (K X) X.1:= by
       have hh:X.1 ∈ σX P Z ∅:=⟨by rw [sdiff_empty]; exact Y,empty_subset _⟩; exact fun i hi _=> fern h p S hf X.1 hh i hi rfl X.2
    apply div_le_div_of_nonneg_right _ (abs_nonneg _); unfold fare
    refine le_trans (b:=∑ i∈ leaks S,u) (sum_le_sum (fun i z=>?_)) (?_)
    · have he: ∀ (X : Orbit N), pingS P.threshold (offsetMask P.B o) X.1 → Tulip.profile (K X) i=profile X.1 i:= fun X p=> by funext k; unfold profile; rw [h0 X p i (mem_filter.mp z).2.1 (mem_filter.mp z).2.2]
      show ‖Tulip.profile (K x) i-Tulip.profile (K y) i‖ ≤ _; rw [he x Hx,he y Hy]; exact H i (mem_filter.mpr ⟨mem_univ _,hw (mem_filter.mp z).2.1,hw (mem_filter.mp z).2.2⟩)
    rw [sum_const,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (by exact_mod_cast leg_bound S (b S q).2.le) u0
 have hd:0 ≤ D:=by unfold D levΦ; positivity
 rw [he,hh,←sum_sub_distrib]; simp_rw [Matrix.sum_apply]; have hk (S:Support T)(i j:Ω) : ‖(W S px-W S py) i j‖ ≤ D*(rent a S*C S i j):=by
    have hp:= (c S|>.expo i j).variation px py; have hi:0≤ C S i j:= (c S).nonn i j
    by_cases m:C S=0; · simpa [m,Matrix.sub_apply] using hp
    refine hp.trans (le_trans (mul_le_mul_of_nonneg_left (hv S m) hi) ?_); rw [mul_comm (C S i j) D]; apply mul_le_mul_of_nonneg_left _ hd; exact le_mul_of_one_le_left hi (rent_one ha S)
 refine le_trans (sum_le_sum (fun i _=> sum_le_sum (fun j _=> (norm_sum_le ..).trans (sum_le_sum (fun S _=> hk _ _ _))))) ?_
 simp_rw [sum_comm (f:=fun (j:Ω)(S:Sa N)=> D*(rent a S*C S _ j))]; rw [sum_comm]; simp_rw [←mul_sum]; exact mul_le_mul_of_nonneg_left L hd
omit h g p l t ha
theorem menu_trace (U:Op Ω)(h:(∑ i,∑ j,‖U i j‖) ≤ c) : ‖Matrix.trace U‖≤ c:= (norm_sum_le ..).trans ((sum_le_sum (fun i (_:i∈(univ:Finset Ω))=> Finset.single_le_sum (f:=fun j=> ‖U i j‖) (fun j _=> norm_nonneg _) (mem_univ i))).trans h)
theorem menu_spin (U:Op Ω)(h:(∑ i,∑ j,‖U i j‖) ≤ c) : ‖preJ (tickA N) U‖≤ c+c:=by
 let hA:= Cascade.plus_P N; let A:= tickA N; let M:=Matrix.trace (A*U)
 refine (norm_add_le (M • (1:FC Ω)) _).trans (add_le_add ?_ ((Fixed.Extensive.dgN U _ _ (hA.norm_le _) (hA.one_sub.norm_le _)).trans h))
 unfold M A; rw [norm_smul,norm_one,mul_one, touchP,Matrix.trace]; refine (norm_sum_le ..).trans ((sum_le_sum ?_).trans h)
 intro i hi; change ‖(cutM (Tset N)*U) i i‖ ≤ _; rw [cutM,Matrix.diagonal_mul]; split_ifs; rw [one_mul]; exact single_le_sum (fun i _=> norm_nonneg _) (mem_univ _)
 rw [zero_mul,norm_zero]; exact sum_nonneg fun j _=> norm_nonneg _
lemma menu_Δspin (U V:Op Ω)(h:(∑ i,∑ j,‖(U-V) i j‖)≤ c) : ‖preJ (tickA N) U-preJ (tickA N) V‖≤ c+c:=by
 have hx:= menu_spin (U-V) h; apply le_trans (le_of_eq (congrArg (‖·‖) ?_)) hx
 have hP(X Y:Op Ω): dg (X-Y)=dg X-dg Y:=(by rw [sub_eq_add_neg, dg_add,dg_neg,←sub_eq_add_neg]); unfold preJ; rw [mul_sub (tickA N),Matrix.trace_sub,sub_smul,sub_mul,hP]; abel
end YM.CF.Swell
