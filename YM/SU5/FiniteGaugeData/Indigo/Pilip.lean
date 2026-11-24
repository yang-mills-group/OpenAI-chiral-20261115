import YM.SU5.FiniteGaugeData.Indigo.Anthea
set_option autoImplicit false
set_option synthInstance.maxSize 18000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 300000
set_option linter.flexible false
noncomputable section
namespace YM.CF
namespace Indigo
open SU Filter Function NormedSpace Thera Fock RG Finset Metric MeasureTheory Asymptotics
open Buffered.Afterglow.Hierarchy.LyraBill.Chiffon.Sesame.FlakeNight.Succulent
open scoped Matrix Topology InnerProductSpace MatrixOrder BigOperators ContDiff ComplexOrder Kronecker
open Cascade
local notation "V"=> SU.group.Color
open AntiS
open Next.Rank.Spindle
abbrev tender_E (U:E)(x:V):ℂ:= CashNotch U-1+(↑(colorG*‖x‖^2):ℂ) -- sign
local notation "G_"=> SU.group
local notation "τ₀"=> SU.group.chord
local notation "L"=> SU.group.curvature
variable {t d c C κ r y ε:ℝ}
open Next.Fluctuations
lemma cupY(e:0<ε):∃ t:ℝ,0<t∧∀ U:E, SU.group.chord U≤t→ ‖tender_E U (SU.group.curvature U)‖ ≤ ε* SU.group.chord U^2:=by
 obtain ⟨W⟩:= charts (G_) -- replace rules.C
 obtain ⟨T,hT,J⟩:= Metric.nhds_basis_closedBall.eventually_iff.mp (crystallized.bound (show 0 < ε/4 from by positivity)); refine ⟨min W.c (T/2), lt_min W.radius (half_pos hT), fun U p=>?_⟩; let X:= SU.group.plog (SU.group.mat U); have hh:=W.sleeve U (p.trans (min_le_left ..)); have h:X ∈ closedBall 0 T:= mem_closedBall.mpr (by rw [dist_zero_right]; linarith only [hh,p.trans (min_le_right ..)]); have ht:= J h; rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at ht; unfold cruxS at ht; rw [show SU.group.lieExp X=U from W.records U (p.trans (min_le_left ..))] at ht; apply ht.trans; apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg X) hh 2) (by positivity: 0 ≤ ε/4)).trans_eq; ring
-- global scaling
lemma cardigan_U : ∃ D:ℝ,0<D∧∀ i:E,‖CashNotch i-1‖ ≤ D*SU.group.chord i^2:=by
 obtain ⟨t,v,p⟩:=cupY (by norm_num:(0:ℝ)<1); obtain ⟨D,vD,hD⟩: ∃ C:ℝ,0 ≤ C∧∀ i:E,‖CashNotch i-1‖ ≤ C:=by
    let F(i:E):= ‖CashNotch i-1‖; obtain ⟨u,x,Q⟩:= isCompact_univ.exists_isMaxOn Set.univ_nonempty ((careful.sub continuous_const).norm.continuousOn); exact ⟨F u,norm_nonneg _,fun _=>Q (Set.mem_univ _)⟩
 let T:= max (1+colorG) (D/(t^2)); have h₀:= cg0; refine ⟨T,(show 0<1+colorG from by positivity).trans_le (le_max_left ..),fun i=> ?_⟩; let u:= τ₀ i; let A:=CashNotch i-1; let x:= L i; let H:ℝ:= colorG*‖x‖^2; by_cases e:u≤ t
 · have hx: ‖(↑H:ℂ)‖ ≤ colorG*u^2:= by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0≤ H from by unfold H; positivity)]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (SU.group.curvature_norm i) 2) h₀.le
   have hz: ‖A+ ↑H‖ ≤ 1*u^2:= p i e; change ‖A‖ ≤_; rw [show A= (A+(↑H:ℂ))-↑H from (add_sub_cancel_right ..).symm]; exact (norm_sub_le ..).trans ((add_le_add hz hx).trans (le_trans (add_mul ..).symm.le (mul_le_mul_of_nonneg_right (le_max_left ..) (sq_nonneg _))))
 have hx:= (lt_of_not_ge e).le; apply (hD i).trans; refine (le_trans ((div_mul_cancel₀ D (pow_pos v 2).ne').symm.le) (mul_le_mul (le_max_right ..) (pow_le_pow_left₀ v.le hx 2) (sq_nonneg _) ((by unfold T; exact (show 0 ≤ 1+colorG from by positivity).trans (le_max_left ..)): 0≤ T)))
-- lists; integer budget n; use ANY support count etc
abbrev choirQ (U:List E):= (U.map (L)).sum
abbrev shades(U:List E)(t:ℝ) : Prop:= ∀ u∈U,SU.group.chord u≤t
abbrev penG :ℝ:= SU.group.colorScale
lemma chordD {U:List E}(h:shades U t): SU.group.chord U.prod≤ U.length*t := by
 induction U with
 | nil => simp
 | cons u v ih=> let p:=(h u (List.mem_cons_self ..)); let q:=ih (fun w z=>h w (List.mem_cons_of_mem _ z)); rw [List.prod_cons]; apply (SU.group.chord_triangle u v.prod).trans; apply (add_le_add p q).trans_eq; rw [List.length_cons]; push_cast; ring
lemma normD {U: List E}(h:shades U t) : ‖choirQ U‖ ≤ U.length*t:=by
 induction U with
 | nil=> simp [choirQ]
 | cons u v ih=> let p:= (SU.group.curvature_norm u).trans (h u (List.mem_cons_self ..)); let q:=ih (fun w z=>h w (List.mem_cons_of_mem _ z)); change ‖L u + _‖≤_; apply (norm_add_le ..).trans; apply (add_le_add p q).trans_eq; rw [List.length_cons]; push_cast; ring
lemma trillEF {U:List E}(p:0≤t)(h:shades U t): ‖SU.group.curvature U.prod-choirQ U‖ ≤ penG * (U.length:ℝ)^2 * t^2:=by
 induction U with
 | nil=> simp [choirQ]
 | cons u v ih=>
    let Z:= L (u*v.prod) -((L u)+(L v.prod)); let n:ℝ:=v.length; have h0:=SU.group.colorScale_pos.le; have h1:= SU.group.chord_nonneg v.prod; let p₁:=h u (List.mem_cons_self ..); let h':= show shades v t from fun w z=> h w (List.mem_cons_of_mem _ z); have hZ:‖Z‖≤ penG*t*(n*t):=(weave u v.prod).trans (mul_le_mul (mul_le_mul_of_nonneg_left p₁ h0) (chordD h') h1 (mul_nonneg h0 p))
    change ‖L (u*v.prod)-(L u+ choirQ v)‖ ≤_; rw [show L (u*v.prod)-(L u+choirQ v)=Z+(L v.prod-choirQ v) from (by unfold Z; abel)]; apply (norm_add_le ..).trans; apply (add_le_add hZ (ih h')).trans; have hp : 0 ≤ penG * t^2:= mul_nonneg h0 (sq_nonneg _); rw [List.length_cons]; push_cast; unfold n; have hv: 0 ≤ (v.length:ℝ):= Nat.cast_nonneg _; nlinarith only [hp, mul_nonneg hp hv]
-- assembly
lemma tutelary (k:ℕ)(p:0 < ε):∃ T:ℝ, 0<T∧ ∀ U:List E, U.length≤ k → ∀ t:ℝ, 0≤t→ t≤ T→ shades U t →‖tender_E U.prod (choirQ U)‖ ≤ ε*t^2:=by
 let Y:ℝ:= k+1; have hY:0< Y:=by unfold Y; positivity; -- sem newline
 let κ:= 2*Y*penG*Y^2 * colorG; have hP:0<penG:=SU.group.colorScale_pos; have h₀:=cg0; have hκ:0< κ:=by unfold κ; positivity
 obtain ⟨X,hX,v⟩:= cupY (show 0 < ε/(2*Y^2) from by positivity); refine ⟨min (X/Y) (ε/(2*κ)),lt_min (div_pos hX hY) (by positivity),fun U z t h₁ h₂ c=>?_⟩; let u:= U.prod; let Q:= choirQ U; let x:= L u
 have hB:(U.length:ℝ) ≤ Y:=(Nat.cast_le.mpr z).trans (le_add_of_nonneg_right zero_le_one); have hc:SU.group.chord u≤ Y*t:=(chordD c).trans (mul_le_mul_of_nonneg_right hB h₁); have hw:‖Q‖≤ Y*t:= (normD c).trans (mul_le_mul_of_nonneg_right hB h₁); have he: ‖x‖≤ Y*t:=(SU.group.curvature_norm _).trans hc; have hh:t*κ≤ ε/2:=(le_div_iff₀ hκ).1 (by rw [div_div]; exact h₂.trans (min_le_right ..)); have hz:=SU.group.chord_nonneg u
 have hx:‖x-Q‖ ≤ penG * Y^2 * t^2:= (trillEF h₁ c).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hB 2) hP.le) (sq_nonneg _))
 let A:= (colorG*(‖Q‖^2-‖x‖^2)); have hee:‖tender_E u x‖≤ (ε/2)*t^2:= (v u (by rw [mul_comm] at hc; exact hc.trans ((le_div_iff₀ hY).mp (h₂.trans (min_le_left ..))))).trans ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hc 2) (by positivity: 0≤ ε/(2*Y^2))).trans_eq (by field_simp)) -- rewrite hc mutated local
 have hv:‖(↑A:ℂ)‖≤ (ε/2)*t^2:=by
    have hp: |‖Q‖-‖x‖| ≤ penG*Y^2*t^2 := (abs_norm_sub_norm_le ..).trans ( (norm_sub_rev ..).trans_le hx); unfold A; rw [Complex.norm_real,Real.norm_eq_abs,sq_sub_sq, abs_mul,abs_mul (‖Q‖+‖x‖), abs_of_pos cg0, abs_of_nonneg (show (0:ℝ)≤ ‖Q‖+‖x‖ from by positivity)]; -- order sq_sub_sq = (a+b)*(a-b) tune
    apply le_trans _ (mul_le_mul_of_nonneg_right hh (sq_nonneg t)); unfold κ; convert mul_le_mul_of_nonneg_left (mul_le_mul (add_le_add hw he) hp (abs_nonneg _) (by positivity : 0≤ Y*t+Y*t)) h₀.le using 1 <;> ring -- tune
 rw [show tender_E U.prod (choirQ U)= tender_E u x+ ↑A from (by unfold tender_E A u Q; push_cast; ring)]; exact (norm_add_le ..).trans ((add_le_add hee hv).trans_eq (by ring))
#print axioms tutelary
#print axioms cardigan_U
end Indigo
end YM.CF
