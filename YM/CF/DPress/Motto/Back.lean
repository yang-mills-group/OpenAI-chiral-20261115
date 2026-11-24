import YM.CF.DPress.Motto.Loyal
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Py.Kay
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open DPress.Plaque Larch Ione Taxi Bake Salt
namespace WagesC.Blend
variable {n:Side}{k L:ℕ}(P:BudgetPoint){a h b:ℝ}
local notation "Sx"=> Point n
variable (B:Blend n k) (w: Wings k P a n)(t:1≤h)(z:ℝ)
abbrev η(v w:Point n)(r:Support (More n)):= flick (τ₀ w) (oV (fund w)) r-flick (τ₀ v) (oV (fund v)) r
private lemma Ψcost {v:ℝ}(x:Sx×Sx): (v • (stroke (τ₀ x.2) (τ₀ x.1) (coinP x) (oV (fund x.2)) (oV (fund x.1)))) = chasmR (coinP x) (fun r=> v • η x.1 x.2 r):=by
 funext i r; by_cases h:i=coinP x; · rw [h,Pi.smul_apply,Pi.smul_apply]; unfold stroke chasmR η; rw [Pi.single_eq_same,Pi.single_eq_same]
 rw [Pi.smul_apply,Pi.smul_apply]; unfold stroke chasmR; rw [Pi.single_eq_of_ne h,Pi.single_eq_of_ne h]; exact smul_zero _
variable (i:Point n × Point n) -- warning macro
abbrev Aa(P:BudgetPoint)(k:ℕ)(a:ℝ) := chi_f P.order*(grade P k a*P.threshold^2)
local notation "Κ"=>Aa P k a
include t w
lemma Qcoin (i:Point n): Vow.Medal P (τ₀ i).val ∅ (oV (fund i)) h (Aa P k a):= Vow.rimR (budgetPump P w i (hup i) (Subset.refl _) (separation_self i|>.trans_le (Nat.zero_le k))) (zero_le_one.trans t)
lemma positiveA: 0 ≤ Aa P k a := (Qcoin P w t 0).wage (zero_le_one.trans t)
abbrev κS (P:BudgetPoint)(a:ℝ)(k:ℕ)(z:ℝ):= |z| *(Aa P k a+Aa P k a)
lemma shapeP(x:Sx×Sx)(D:Support (More n)): Vow.Medal P (coinP x).val D ((z*φΩ B x) • η x.1 x.2 D) h (φΩ B x * κS P a k z):=by
 let N:= coinP x; have ht:0 ≤ h:=zero_le_one.trans t; apply Medal.big (((capM P h _ _ t).sub (flick_M (τ₀ x.2) N subset_union_right ht (Qcoin P w t _) D) (flick_M (τ₀ x.1) N subset_union_left ht (Qcoin P w t _) D) |>.rum (z*φΩ B x))); change ‖z*φΩ B x‖ * _ ≤ _; rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (weight ..)]; unfold κS; exact le_of_eq (by ring)
local notation "K'"=> coinP i
abbrev ζP(P:BudgetPoint)(a:ℝ)(k:ℕ):= (2*(k+2)+1:ℕ)^4 * (Real.exp (P.supportExponent+1+1)*(chi_f P.order*grade P k a*2)) -- casts beware nat ^ binds cast op
abbrev δκ (X:Aura n):=∑ i∈ κN n k, if coinP i=X then φΩ B i* κS P a k z else 0
lemma rentQ : Anuk (B.Zα z) (δκ P (a:=a) B z) P h:=by
 refine ⟨fun X =>sum_nonneg (fun i _=>ite_nonneg (mul_nonneg (weight ..) (mul_nonneg (abs_nonneg _) (add_nonneg (positiveA P w t) (positiveA P w t)))) le_rfl),fun X D u q=> ?_⟩
 unfold Zα; simp_rw [Ψcost]; exact Vow.migrate _ _ _ _ u (fun i _ k d q=>shapeP P B w t z i k) X q -- tune
local notation "ιP"=> P.supportExponent+1+1
omit t w
private lemma zone {x:Point n × Point n}(j:x∈κN n k){X:Sx}(h:X∈(coinP x).val): x.1∈ halo (k+2) {X}:=by
 have hz:= (mem_filter.mp j).2; apply halo_spec.mpr; refine ⟨X,mem_singleton_self _,(separation_comm X _).trans_le (?_)⟩; obtain a|a:= mem_union.mp h <;> obtain ⟨d,f,t⟩:= halo_spec.mp a <;> rw [mem_singleton.mp f] at t; omega; exact (separation_triangle ..).trans (Nat.add_le_add hz t)
include t w
lemma Ωbig (o:Point n): tallB (δκ P (a:=a) B z) P.B (P.supportExponent+1+1) o≤ ζP P a k *|z| * P.threshold^2:=by
 let V:= (κN n k).filter fun i=>o∈(coinP i).val; let f(i:Sx×Sx) := φΩ B i*κS P a k z; let D'(i:Sx×Sx):= f i*currency P.B ιP (coinP i).val
 have he: (∑ i∈ V,D' i)= tallB (δκ P (a:=a) B z) P.B ιP o:=by
    unfold tallB δκ; simp_rw [sum_mul]; unfold V; rw [sum_comm (s:= (univ:Finset (Aura n)).filter fun i=>o∈ i.val),sum_filter (s:=κN n k)]; apply sum_congr rfl; intro i u
    symm; by_cases h:o∈(coinP i).val; swap
    · rw [if_neg h]; refine sum_eq_zero fun i' p=> ?_; rw [if_neg (fun (y:coinP i=i')=>h (y.symm ▸ (mem_filter.mp p).2)),zero_mul]
    rw [if_pos h,sum_eq_single (coinP i),if_pos rfl]
    · intro i' p v; rw [if_neg v.symm,zero_mul]
    exact (fun p=>(p (mem_filter.mpr ⟨mem_univ _,h⟩)).elim)
 have hp:= positiveA P w t; let U:= halo (k+2) {o}; let F':= (κN n k).filter fun i=> i.1∈ U; let S:= κS P a k z*Real.exp ιP
 have hu:0 ≤ κS P a k z:= mul_nonneg (abs_nonneg _) (add_nonneg hp hp); have hh:0≤ S:=mul_nonneg hu (Real.exp_pos _).le
 have hx: (∑ i∈F',φΩ B i*S)=(U.card:ℝ)*S:=by
    rw [←sum_fiberwise_of_maps_to (g:=fun i:Sx×Sx=>i.1) (t:=U) (s:=F') (fun x u=>(mem_filter.mp u).2)]; refine Eq.trans (sum_congr (g:=fun i:Sx=>S) rfl fun i v=>?_) ?_; swap; · simp
    rw [show (F'.filter (fun x=>x.1=i))= (κN n k).filter fun x=>x.1=i from by ext j; simp only [F',mem_filter]; exact ⟨fun i=>⟨i.1.1,i.2⟩,fun p=>⟨⟨p.1,p.2.symm ▸ v⟩,p.2⟩⟩,←sum_mul,B.money,one_mul]
 rw [←he]; refine (le_trans (sum_le_sum (g:=fun k:Sx×Sx=>φΩ B k*S) ?_) ((sum_le_sum_of_subset_of_nonneg (t:=F') ?_ (fun i _ _=>mul_nonneg (weight ..) hh)).trans ?_))
 · intro i p; let v':= P.supportExponent+1+1; have hp0:currency P.B v' (coinP i).val ≤ Real.exp v':=by
       have hx:= (wraps P w i.1 i.2 (mem_filter.mp (mem_filter.mp p).1).2); apply Real.exp_monotone; apply mul_le_of_le_one_right (add_nonneg (add_nonneg P.exponent_pos.le zero_le_one) zero_le_one); exact_mod_cast hx -- coinP defeq
   refine (mul_le_mul_of_nonneg_left hp0 (mul_nonneg (weight B i) hu)).trans_eq (mul_assoc ..) -- hx orientation
 · intro i p; exact mem_filter.mpr ⟨(mem_filter.mp p).1,zone (mem_filter.mp p).1 (mem_filter.mp p).2⟩
 rw [hx]; have hz: (U.card:ℝ)≤(((2*(k+2)+1)^4:ℕ):ℝ):= by exact_mod_cast BPress.Wealth.halo_size (s:=More n) o (k+2)
 refine (mul_le_mul_of_nonneg_right hz hh).trans_eq ?_; unfold S κS Aa ζP; push_cast; ring

end WagesC.Blend
end YM.CF.Py.Kay
