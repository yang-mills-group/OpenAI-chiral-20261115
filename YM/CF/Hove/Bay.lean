import YM.CF.Haro.Chord
import YM.CF.Scree.Brief
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

-- constant and *separate* rooted differences at local probe
abbrev Kt:= SpinIdx×Slot
variable {c f:Side}(o:Site f)
def baseF(b:Bool): Op Kt:= if b then 1-bins Slot else bins Slot
def ditF(b:Bool)(i:Axis): Op Kt:=(-Complex.I) • (if b then boom i else -boom i)
def moonB(b:Bool)(i:Axis)(x:Cover): Op Kt:= (x i:ℂ) • baseF b + ditF b i
lemma archFee(x:Cover): Laurent.size (x+0)=Laurent.size x:=by rw [add_zero]
lemma route_H(x y:Cover): Rush.wind o (x+y)=Rush.wind o x*Rush.wind (o+wrap f x) y:=by
 let X:=o+wrap f x; let Y:=X+wrap f y; let K:Site f:=0; let P:=frequency K
 have hx:= freq_advance K o (x+y); rw [map_add,←add_assoc,mode_shift] at hx
 apply mul_right_cancel₀ (show P Y ≠ 0 from (fun h=>by have ht:star (P Y)*P Y=1:=frequency_unit ..; rw [h,mul_zero] at ht; exact zero_ne_one ht))
 rw [hx, mul_assoc,show Rush.wind _ _ * P Y=_ from (freq_advance K X y)]; rw [←mul_assoc (Rush.wind o x), show Rush.wind o x* frequency K X=_ from (freq_advance ..),mul_assoc] -- tune small rhs
variable{E:Type*}[Fintype E][DecidableEq E](V:E→ℝ){n j m:ℕ}
variable{F:Cover→ℂ}{C A B:ℝ} (p:Cp m F C)
omit o
lemma p_posts {ι:Type*}[DecidableEq ι](v:0 ≤ V)(S:Finset ι)(f:ι→E→ℂ): paidX V (∑ i∈S,f i) ≤ ∑ i∈S,paidX V (f i):=by
 induction S using Finset.induction_on with
 | empty=> simp [paidX]
 | @insert i s hi h=>rw [sum_insert hi,sum_insert hi]; exact (p_sum v _ _).trans (add_le_add (le_refl _) h)
def ratioY (B:ℝ)(n:ℕ)(x:Cover):= (1+ (Laurent.size x:ℝ)/B)^n
lemma ray_m (H:1≤B)(x y:Cover): ratioY B m (x+y)≤ ratioY B m x * tweight m y:=by
 let a:ℝ:= Laurent.size x; let b:ℝ:=Laurent.size y; have ha:0≤a:=Nat.cast_nonneg _; have hb:0≤b:=Nat.cast_nonneg _; have he:0<B:=lt_of_lt_of_le zero_lt_one H
 have ht:(Laurent.size (x+y):ℝ)≤ a+b:=by unfold a b; exact_mod_cast Laurent.size_add ..
 unfold tweight ratioY; rw [←mul_pow]; refine pow_le_pow_left₀ (by positivity) ?_ _; change _≤ (1+a/B)*(1+b); have hk:b/B ≤ b:= div_le_self hb H
 have hx := div_le_div_of_nonneg_right ht he.le; rw [add_div] at hx; nlinarith only [hx,hk,mul_nonneg (div_nonneg ha he.le) hb]
include p
open Classical in
lemma paid_l(v:∀ i,1 ≤ V i)(T:Cover→E→ℂ)(h:∀ x, paidX V (T x)≤ A*tweight m x)(hu:0≤A) : (∀ y:E,Summable (fun x:Cover=> F x * T x y)) ∧ paidX V (fun i=>∑' x,F x*T x i)≤A*C:=by
 let P(x:Cover):= A*(tweight m x*‖F x‖); have hp: Summable P:=p.2.1.mul_left _
 let G(x:Cover)(i:E):=F x * T x i; have hY(x):paidX V (G x)≤ P x:=by
    change paidX V (F x • T x)≤ _; rw [p_smul]; exact (mul_le_mul_of_nonneg_left (h x) (norm_nonneg _)).trans_eq (by unfold P; ring)
 let K(x:Cover)(i:E):= V i * ‖G x i‖; have hV:0 ≤ V:=fun i=>zero_le_one.trans (v i); have hs(x i):0 ≤ K x i:=mul_nonneg (hV _) (norm_nonneg _)
 have hh(x i): K x i≤ P x:=(single_le_sum (fun i _=> hs x i) (mem_univ i)).trans (hY x)
 have hz(x i):‖G x i‖≤ K x i:= le_mul_of_one_le_left (norm_nonneg _) (v i)
 have ht(i):Summable fun x:Cover=>‖G x i‖:=hp.of_nonneg_of_le (fun x=>norm_nonneg _) (fun x=>(hz x i).trans (hh x i))
 have ha(i): Summable fun x:Cover=> K x i:= (ht i).mul_left _
 refine ⟨fun i=>(ht i).of_norm,?_⟩
 calc
   _ ≤ ∑ i:E, ∑' x:Cover, K x i:=by
      unfold paidX; apply sum_le_sum; intro i _; unfold K; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm (ht i)) (hV i)
   _ ≤ ∑' x:Cover,P x:=by rw [← Summable.tsum_finsetSum (fun i _=>ha i)]; exact (summable_sum fun i _=>ha i).tsum_le_tsum hY hp
   _ ≤ _:=by unfold P; rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left p.2.2 hu
section PAW
omit p
variable (b:Bool)(M:Male)(h:1≤j)
local notation "P"=> Paw j M b
include h
lemma mox (r s:Kt): (∑' x:Cover,P x r s)=baseF b r s:=by
 let A:= if b then boot j M 0 else 1-boot j M 0
 have hx: (∑' x:Cover,P x r s)= A r s:=by have he:=(hel_pawn _ h M b).readK 0 (by simpa [bout_zero] using bout_h 0 0 (by norm_num)) r s; simpa only [Laurent.read, mode_constant,one_smul] using he
 rw [hx,show A = baseF b from ?_]; unfold A baseF; rw [boot_o,sub_sub_cancel]
lemma mixY (i:Axis)(r s:Kt): (∑' x:Cover,(x i:ℂ)*P x r s)= ditF b i r s:=by
 let d:= if b then boom i else -boom i; let H (x:ℝ):Op Kt:= if b then boot j M (bout i x) else 1-boot j M (bout i x)
 have ht: HasDerivAt H d 0:=by cases b; exact (barox j h M i).const_sub _; exact barox j h M i
 obtain ⟨C,h',p⟩:= pawn_p j 1 h b; have he:= (moments (p M r s) (by omega) i).2
 have hv := (he.congr_of_eventuallyEq (show (fun x=>H x r s)=ᶠ[𝓝 0] _ from (by filter_upwards [bout_v i] with x u; exact ((hel_pawn _ h M b).readK (bout i x) u r s).symm))).unique (op_deriv.mp ht r s)
 change _ = -Complex.I * (d r s); rw [←hv,←mul_assoc]; simp
end PAW
end YM.CF.Hove
#print axioms YM.CF.Hove.mixY
