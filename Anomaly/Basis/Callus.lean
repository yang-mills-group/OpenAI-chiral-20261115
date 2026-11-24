import Anomaly.Basis.Glade
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell.Porticus
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
variable {N:Side}{Y:SOp N}{S:Sa N}{B:BudgetPoint}{a s t d f h q' x₀:ℝ}{k q:ℕ}{K:Scree.Loom N}
local notation "I"=> Single N
local notation "θ"=> More N
open Buffered
variable {V:SOp N}{o: Seat N}
private lemma φledger (A:Op I): ‖A‖≤ ∑ i:I,∑ j:I,‖A i j‖:=by
 apply schur _ A _ (sum_nonneg fun i _=>sum_nonneg fun j _=>norm_nonneg _) (fun i j=>le_refl _); swap; · intro i; rw [sum_comm]; exact single_le_sum (f:=fun i:I=>∑ j,‖A j i‖) (fun i _=>sum_nonneg (fun j _=> norm_nonneg (A _ _))) (mem_univ i) -- tune rewrite
 intro i; exact single_le_sum (f:=fun i:I=>∑ j,‖A i j‖) (fun i _=>sum_nonneg (fun j _=> norm_nonneg (A _ _))) (mem_univ i)
variable {α μ:ℝ}
local notation "Φ"=>tangD N
lemma diff_bill (v:Trunk o V k a μ d) (s:0≤a) (K:Sonar.mintQ α f d B.order)(p:0<d)(x:Φ)(g:‖x‖ < α): let U:=increment 1 x; (∑ i:I, ∑ j:I, ‖V (profile U) i j-V (profile 1) i j‖) ≤ f*μ* ‖x‖:=by
 obtain ⟨F,C,r,w,u,J⟩:=v.home; intro U; let W(i:Φ):= V (profile (increment 1 i)); have hθ: Guard U d := K.2.2.2.1 _ g; let P(S:Sa N)(y:Φ):=Sonar.lens p (F S) (increment 1 y); have hc:0<f:= K.2.2.1; let Z₁:Pane N:=1
 have ht₀:increment Z₁ (0:Φ)=1:=by funext i; simp [increment, Z₁]
 have hf(i:Φ)(g:‖i‖<α): W i=∑ S:Sa N,P S i:=by
    rw [show W i= _ from J ⟨_,Sonar.insideQ ⟨_,K.2.2.2.1 _ g⟩ p⟩]; apply sum_congr rfl; intro j t; unfold P Sonar.lens; rw [dif_pos (show Guard _ _ from K.2.2.2.1 i g)]
 have hv₀:‖(0:Φ)‖<α := norm_zero.trans_lt K.1
 have hx: V (profile 1)= W 0:= (congrArg (fun Q:Pane N=> V (profile Q)) ht₀).symm
 let H(S:Sa N)(i j:I)(z:Φ):ℂ:=P S z i j
 have hz(S:Sa N)(i j:I) : ‖H S i j x-H S i j 0‖≤ f*C S i j * ‖x‖:=by
    have hu: 1≤ B.order:= (by decide:1≤6)|>.trans B.order_ge
    have he(t:Φ)(g':‖t‖<α): Allows B.order (H S i j) t (f*C S i j):=K.2.2.2.2 (F S) _ (r S) (Sonar.lens p (F S)) (fun W p=> dif_pos W.property) _ g' _ _
    refine ((convex_ball (0:Φ) α).norm_image_sub_le_of_norm_fderiv_le (f:=H S i j) (fun v t=> (he _ (mem_ball_zero_iff.mp t)).smooth.differentiableAt (by exact_mod_cast (show B.order≠0 from Nat.ne_of_gt hu))) (fun v t=>?_) (mem_ball_self K.1) (mem_ball_zero_iff.mpr g)).trans_eq (by rw [sub_zero]); rw [← norm_iteratedFDeriv_one]; exact (he _ (mem_ball_zero_iff.mp t)).norm_le 1 hu
 let D(S:Sa N)(i j:I):= f*C S i j *‖x‖
 rw [show V (profile U)= _ from hf x g,hx,hf 0 hv₀]; simp_rw [Matrix.sum_apply, ←sum_sub_distrib]; apply le_trans _ (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left u hc.le) (norm_nonneg x))
 calc
   _ ≤ ∑ i:I,∑ j:I,∑ S:Sa N,D S i j:= sum_le_sum fun i _=>sum_le_sum fun j _=> (norm_sum_le ..).trans (sum_le_sum fun S _=>hz S i j)
   _ = f*(∑ S:Sa N,ledgerV (C S))* ‖x‖:=by simp_rw [sum_comm (f:=fun j (S:Sa N)=> D S _ j)]; rw [sum_comm]; simp_rw [D,ledgerV,mul_sum,sum_mul]
   _ ≤ _:=by refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sum_le_sum fun i _=> le_mul_of_one_le_left ?_ (rent_one s _)) hc.le) (norm_nonneg _); exact sum_nonneg fun j _=>sum_nonneg fun k _=> (r i).nonn _ _
-- finance up to known gauge. No gauge-fixing used in density; only temporary in this bound. cref Anomaly.Ward.
lemma underCore (v:Trunk o V k a μ d)(p:Roof N t d q K)(g:0<d)(b:B.threshold≤t)(x:Orbit N)(e:pingS B.threshold (halo B.B {o}) x.1)(h:k+q+10 ≤ B.B)(W:Sonar.mintQ α f d B.order)(R: Next.Rank.Spindle.Rules SU.group)(L:4*(k:ℝ)*B.threshold≤R.c)(c:2*(k+1)<(More N).val)(hv:8*(k:ℝ)*B.threshold < α): ∃ y:tangD N,∃ A:Seat N→ SU.E, ‖y‖ ≤ 8*(k:ℝ)*B.threshold ∧ twist (tradew N A) (V (profile (K x)))= V (profile (increment 1 y)) :=by
 let H:=halo k {o}; let Z:Vow.Aura N:=⟨halo B.B {o},o,halo_subset _ _ (mem_singleton_self o)⟩; have hz:pingS B.threshold H x.1:= grow_b (Corona.halo_mono (by omega:k≤ B.B) le_rfl) e
 obtain ⟨y,l,j⟩:= Next.Rank.Spindle.LampP.treeCost o R B.threshold_pos L c (ping_le hz)
 let T:= increment (1:Pane N) y; let A:=Next.Rank.Spindle.fingers x.1 o; let X':Orbit N:=(gauge A x.1,threadG A x.2); have hf: X'.1∈Sour.σX B Z ∅:=⟨by rw [sdiff_empty]; exact (pingB x.1 A).mpr e,empty_subset _⟩
 have hS:Agrees H (K X') T:=by
    intro i m n; rw [show K X' i=X'.1 i from fern p b H ?_ X'.1 hf i m rfl X'.2]; exact (j i m n).symm
    intro i t; obtain ⟨z,V,w⟩:=halo_spec.mp t; obtain ⟨s,m,q⟩:=halo_spec.mp V; exact halo_spec.mpr ⟨_,m,(separation_triangle s z i).trans (by omega)⟩
 refine ⟨y,A,l,?_⟩; rw [←v.rev p g x A]; obtain ⟨F,Q,r,k,t',u⟩:= v.home; rw [show V (profile _)= _ from (show V (profile (K X'))=∑ S:Sa N,F S (roller g p X') from u (roller g p X')), show V (profile T)=_ from u ⟨_,Sonar.insideQ ⟨_,W.2.2.2.1 y (l.trans_lt hv)⟩ g⟩] -- shadow k
 apply sum_congr rfl; intro i _; by_cases s:Q i=0
 · have ht(i':Openc (More N) d): F i i'=0:= Matrix.ext fun j k'=> norm_le_zero_iff.mp (((r i).expo j k'|>.bounded _).trans_eq (by rw [s]; rfl)); rw [ht,ht]
 have hu:= footprintGeodesic (f_then (r i) s) (k i s).1 (k i s).2.le; have hh: ∀ (U:Sonar.fenceP N d),Sonar.lens g (F i) U.val=F i ⟨_,Sonar.insideQ U g⟩:=fun U=>dif_pos U.property; exact (hh ⟨_,p.paid X'⟩).symm.trans ((Sonar.coinLocal g (r i) (agrees_mono hS (coe_subset.mpr hu))).trans (hh ⟨_,W.2.2.2.1 _ (l.trans_lt hv)⟩))
variable (v:Trunk o V k a μ d)(w:0≤a)(p:Roof N t d q K)(g:0<d)(b:B.threshold≤t)(x:Orbit N)(e:pingS B.threshold (halo B.B {o}) x.1)(l:k+q+10 ≤ B.B)(W:Sonar.mintQ α f d B.order)(R: Next.Rank.Spindle.Rules SU.group)(L:4*(k:ℝ)*B.threshold≤R.c)(c:2*(k+1)<(More N).val)(hv:8*(k:ℝ)*B.threshold < α)
local notation "T"=> f*μ*(8*(k:ℝ)*B.threshold)
local notation "Kx"=> profile (K x)
include v w p g b x e l W R L c hv
lemma flareMatrix : ‖V Kx‖ ≤ ‖V (profile 1)‖+T:=by
 obtain ⟨y,A,j,h⟩:=underCore v p g b x e l W R L c hv; rw [←twist_norm (tradew N A),h]
 let Q':=profile (increment 1 y); have hx :‖V Q'-V (profile 1)‖ ≤ T:= (φledger (V Q' - V (profile 1))).trans ((show _ from diff_bill v w W g y (j.trans_lt hv)).trans (mul_le_mul_of_nonneg_left j (mul_nonneg W.2.2.1.le (soakCostNN v.pay))))
 exact (norm_le_norm_sub_add (V Q') (V (profile 1))).trans ((add_le_add_left hx _).trans_eq (add_comm ..))
lemma flareTrace (z:ℂ): ‖Matrix.trace (V Kx)-z‖ ≤ ‖Matrix.trace (V (profile 1))-z‖+T:=by
 obtain ⟨y,A,j,h⟩:=underCore v p g b x e l W R L c hv
 let Q':=profile (increment 1 y); let S:= V Q'; let R':= V (profile 1); let G:= S-R'
 have hy:Matrix.trace (V Kx)= S.trace:=by rw [← show twist _ (V Kx)=S from h,twist_formula,Matrix.trace_mul_cycle,(tradew N A).property.1,one_mul]
 have hx: ‖G.trace‖≤T :=by
    apply le_trans (norm_sum_le ..); refine le_trans ?_ ((show _ from diff_bill v w W g y (j.trans_lt hv)).trans (mul_le_mul_of_nonneg_left j (mul_nonneg W.2.2.1.le (soakCostNN v.pay))))
    exact sum_le_sum fun i _=> single_le_sum (f:=fun j:I=> ‖S i j - R' i j‖) (fun j _=>norm_nonneg _) (mem_univ i)
 rw [hy,show S.trace-z=R'.trace-z+G.trace from (by unfold G; rw [Matrix.trace_sub]; abel)]; exact (norm_add_le ..).trans (add_le_add_right hx _) -- check add_le_add_left API flipped?
end YM.CF.Swell.Porticus
