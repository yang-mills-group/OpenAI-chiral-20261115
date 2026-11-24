import YM.SU5.May.LunarGram
import YM.SU5.Relativistic.Ghats
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.Lunar
open Function Filter Finset Lattice Laurent Next.Free Bloch Fir Real Complex MeasureTheory WithLp
open scoped Topology BigOperators ContDiff Matrix InnerProductSpace ENNReal ComplexOrder Classical Matrix.Norms.L2Operator
open Lat Onyx Flare Fock Buffered.Lifted Buffered.Afterglow.Tower Buffered.Afterglow.Tower.Tilted Window.ArchiveK Window.Largo
open SU Tulip Hygrometry Personality Rush Dial Cube Kea Emu Tilted May.Floe
attribute [local instance] opCStarAlgebra
variable (N:Side)(P:Ramp)(p q:E4)(i:Title P)(x y:Cover)(b:Bool) (v w:Ket SpinIdx) (x':ℝ) (a:Slot)
local notation "T"=>rimB N
local notation "δ"=> tagE P i
local notation "G" => chord N P i
local notation "η" => ‖chord N P i‖
noncomputable def grain (P:Ramp) (i:Title P):ℝ:=2*π*halfer* ‖canon P i‖
lemma therm: ‖chord N P i‖* rimB N= grain P i:=by rw [chord,norm_smul,Real.norm_of_nonneg (tune_p N).le]; unfold grain tune rimB; field_simp
lemma half_bill : 1/2 < halfer := by nlinarith only [halfLegal,halfSquare]
lemma grain_floor : 1 ≤ grain P i:=by
 unfold grain; refine le_trans ?_ (mul_le_mul (mul_le_mul_of_nonneg_left half_bill.le (by positivity:(0:ℝ)≤2*π)) (salaried P i) (by norm_num:(0:ℝ)≤1/2) (mul_nonneg (by positivity) halfLegal.le)); linarith only [Real.pi_gt_three]
open Crest.Sleet (spangle spangle_sum spangle_pos)
local notation "τ" => grain P i
private lemma preEarning(j:Axis):((i.val j).natAbs:ℝ) ≤2*‖canon P i‖:=by
 -- a b; other.
 by_cases x:j=P.a; · subst j; rw [i.property]; simp; -- nonneg!
 rw [show ((i.val j).natAbs:ℝ)=|(i.val j:ℝ)| from ?_]; swap; · rw [← Int.cast_natCast (R:=ℝ),Int.natCast_natAbs,Int.cast_abs] -- check
 by_cases h:j=P.b; · subst j; have he:= arm_abs (canon P i) P.b; rw [b_loc,abs_div] at he; norm_num at he; linarith only [he]
 have he:=arm_abs (canon P i) j; rw [z_loc P _ _ x h] at he; rw [abs_le]; have hg:= abs_le.mp he; have ht:=salaried P i; constructor <;> linarith [hg.1,hg.2]
noncomputable def rime (P:Ramp)(i:Title P):= Real.exp (-(grain P i)/4)
lemma rime_p : 0<rime P i := Real.exp_pos _
private lemma tonic {x:ℝ}(p:0<x): Summable (fun y:Cover=>∏ i:Axis, spangle x (y i)):=by
 let f:=spangle x; let B:=∑' i:ℤ,f i; have ht: Summable f:=spangle_sum p; apply summable_of_sum_le _ (c:=B^4); swap -- syntax
 · intro i; exact Finset.prod_nonneg (fun j _=>(spangle_pos ..).le)
 intro s; let V(k:Axis):=s.image (fun i=> i k); have he:s ⊆ Fintype.piFinset V:= fun i h=> Fintype.mem_piFinset.mpr fun k=> mem_image_of_mem _ h; refine (sum_le_sum_of_subset_of_nonneg he (fun i _ _=> Finset.prod_nonneg (s:=@univ Axis _) (fun j _=>(spangle_pos ..).le))).trans ?_; rw [← Finset.prod_univ_sum (κ:=fun _=>ℤ) V (fun _=>spangle x)]; simpa only [prod_const,card_univ, Axis,Fintype.card_fin] using (Finset.prod_le_prod (s:=@univ Axis _) (f:=fun i=> ∑ j∈ V i,f j) (g:=fun _=>B) (fun i _=>sum_nonneg (fun j _=>(spangle_pos ..).le)) (fun i _=> ht.sum_le_tsum _ (fun j _=>(spangle_pos ..).le))) -- tune
noncomputable def cessR (P:Ramp):=∑' i:Title P,rime P i
lemma rime_sum : Summable (rime P):=by
 let a:ℝ:= (1/100); apply Summable.of_nonneg_of_le (fun i=> (rime_p P i).le) _ ((tonic (show 0<a by norm_num [a])).comp_injective (i:=fun t:Title P=>t.val) Subtype.val_injective); intro t; simp only [Function.comp_apply,spangle,←Real.exp_sum,rime]; apply Real.exp_monotone; rw [← Finset.mul_sum]; have hp:(∑ i:Axis, (((t.val i).natAbs:ℕ):ℝ)) ≤ 4*(2*‖canon P t‖):=(sum_le_sum (s:=@univ Axis _) (fun i _=> preEarning P t i)).trans_eq (by rw [sum_const,card_univ, Fintype.card_fin]; norm_num)
 have ht: 3/2*(‖canon P t‖)≤ grain P t:= by
    unfold grain; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _); nlinarith only [half_bill,Real.pi_gt_three]
 unfold a; linarith only [hp, ht,norm_nonneg (canon P t)]
lemma cess_p : 0 ≤ cessR P := tsum_nonneg (fun i=> (rime_p P i).le)
noncomputable def tacit:= 1-Real.exp (-1:ℝ)
lemma tacit_p : 0 <tacit:= sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))
lemma bolt : tacit ≤ earning T ‖chord N P i‖ (tagE P i)∧ earning (rimB N) ‖chord N P i‖ (tagE P i) ≤ 2:=by
 unfold earning; rw [neg_mul, therm]; let u:= Real.exp (-grain P i); have hx:(δ)*u ≤ u:=mul_le_of_le_one_left (Real.exp_nonneg _) (tagguard P i).2.1; have h'u:u ≤ Real.exp (-1):=Real.exp_monotone (neg_le_neg (grain_floor P i)); have ht:-u≤(δ)*u:=by rw [←neg_one_mul u]; apply mul_le_mul_of_nonneg_right (tagguard P i).2.2 (Real.exp_nonneg _);
 unfold tacit; change 1-Real.exp _ ≤ 1-(δ)*u ∧ _ ; constructor; linarith only [hx,h'u]; change 1-(δ)*u ≤ 2; linarith only [ht,h'u, tacit_p,show tacit=1-Real.exp (-1) from rfl]
local notation "A"=> stip P N i
noncomputable def loanP:= halfer/2/tacit
noncomputable def meal:= halfer/2/2/2 -- lower using 1/2
lemma loan_p: 0<loanP:=by unfold loanP; have he:=tacit_p; have hp:=halfLegal; positivity
lemma meal_p: 0 < meal:=by unfold meal; have he:= halfLegal; positivity
lemma stip_n: 0 ≤ stip P N i :=by have hp:= (bolt N P i).1; have he:= tacit_p.trans_le hp; exact div_nonneg (mul_nonneg (half_pos halfLegal).le (wallet_n P (chord N P i) (η))) he.le
lemma no_rebound : |reelT P N i| ≤ Real.exp (-grain P i) := by unfold reelT; rw [neg_mul,therm,abs_mul,abs_of_nonneg (Real.exp_nonneg _)]; apply mul_le_of_le_one_left (Real.exp_nonneg _); exact abs_le.mpr ⟨(tagguard ..).2.2,(tagguard ..).2.1⟩
lemma arc_l (t:80 ≤ rimB N) : stip P N i ≤ loanP*Real.exp (grain P i/4):=by
 let A0:= chord N P i; unfold stip; unfold loanP; rw [div_mul_eq_mul_div _ tacit]; have hx:0≤ halfer/2*windowW P (chord N P i):= mul_nonneg (half_pos halfLegal).le (wallet_n P _ _); refine (div_le_div_of_nonneg_left hx tacit_p (bolt N P i).1).trans ?_; apply div_le_div_of_nonneg_right _ tacit_p.le; apply mul_le_mul_of_nonneg_left _ (half_pos halfLegal).le
 unfold windowW; apply (wallet_bound P (chord N P i) (η) (duet N P i)).trans; simp only [abs_of_nonneg (norm_nonneg _)]; apply Real.exp_monotone; rw [← therm N]; nlinarith only [mul_le_mul_of_nonneg_left t (norm_nonneg A0)]
lemma ceil_back (t:80≤rimB N): stip P N i * |reelT P N i|≤ loanP*Real.exp (-(3/4:ℝ)*grain P i):= (mul_le_mul (arc_l N P i t) (no_rebound N P i) (abs_nonneg _) (mul_nonneg loan_p.le (Real.exp_nonneg _))).trans_eq (by rw [mul_assoc,←Real.exp_add]; ring_nf)
#print axioms arc_l
lemma meal_to_stip (u:1/2 ≤ windowW P (chord N P i)) : meal ≤ stip P N i:=by
 rw [stip,le_div_iff₀ (tacit_p.trans_le (bolt N P i).1)]; apply le_trans (mul_le_mul_of_nonneg_left (bolt N P i).2 meal_p.le); apply le_trans _ (mul_le_mul_of_nonneg_left u (half_pos halfLegal).le); unfold meal; apply le_of_eq; ring
noncomputable def hazySize (D:ℕ)(N:Side):ℝ:=rimB N/(D:ℝ)^10 -- choose T instead N for convenience.
#print axioms cess_p
#print axioms rime_sum
end YM.CF.May.Lunar
