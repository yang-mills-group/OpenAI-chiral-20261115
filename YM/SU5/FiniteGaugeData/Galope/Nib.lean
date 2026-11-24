import YM.SU5.FiniteGaugeData.Galope.Brass
import YM.SU5.FiniteGaugeData.Drachma.Lima
import YM.Next.FLUCTUATIONS.Locality
import YM.Next.FLUCTUATIONS.Slots
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Multiplier
import YM.CF.Graph.Dash
/-! # Local affine comparison on active pledges and conditioned tangent purchase
 Note one may combine stamps from all disjoint tiles into ONE direction so that linearization reads *all* terms of xLin, including tortuous paths leaving stamp etc. Use existing uniform chart estimate for these globally small links. Include cost of actual long transporter rows in actual gauge read by absolute tail. -/
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 600000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Galope
open Function Finset Filter MeasureTheory Matrix Lattice Wilson RG Next.Rank Spindle Avenue
open Pressure Precision Exterior Laurent Bloch Next.Fluctuations Work.E03
open Drachma Drachma.Toffee
open scoped Topology InnerProductSpace Matrix ContDiff BigOperators Classical Kronecker Matrix.Norms.Frobenius
variable {n:Side}{G:Gauge} {s:Stage}{R:PathData G}{P:Bed}{M k w v:ℕ}{A:Finset (Cell n)}{Z:Finset (Site n)}{o:Site n}{C r x Λ α τ u a h:ℝ}
namespace Wrist
open Press
local notation "℘" x:max i:max => Spindle.patch x i
local notation "φ₀" => s.clip
structure Arms (G:Gauge)(s:Stage) where
 C:ℝ
 r:ℝ
 pos : 0<C
 realR : 0<r
 paid {n:Side}{P:PathData G} {Λ:ℝ} (z:P.Bounds s.clip s.width s.paths Λ) (a:LogField G n)(w:ℕ) (h:ℝ)(u:‖a‖≤ h)(y:h≤r)(i:Pressure.Twin n): ‖plotted P s.clip w 1 (represent a) i - xLin s.clip P a i‖ ≤ C*h*widen w h s.width
 allowance : Spindle.Rules G
lemma negotiates(G:Gauge)(s:Stage): Nonempty (Arms G s):=by
 obtain ⟨f,r,hf,hr,hu⟩:=x_chart_cost G s 1 zero_lt_one; obtain ⟨D⟩:= charts G; exact ⟨⟨f,r,hf,hr,fun z a w h u y i=> by simpa only [Nat.cast_one,div_one] using (hu _ _ _ z w a h u y i).2,D⟩⟩
private lemma base_Gauge (F:Clip)(σ C Λ:ℝ)(p:BudgetPoint)(U:Config G n)(z:R.Bounds F σ C Λ)(g:Site n→G.El)(i:Cell n) : R.baseTerm F p (gauge g U) i=R.baseTerm F p U i:=by simp only [PathData.baseTerm, PathData.kept, face_gauge,G.chord_conj,Work.F05.ell_gauge z, G.norm_adjoint]; split <;> rename_i h <;> simp only [*,if_true,if_false]

abbrev roomCard(k w:ℕ):= k+w+4
abbrev debit(k w:ℕ):= roomCard k w+w+4+2 -- $M≥debit$. +2 safety reading source.
def billsC(k w:ℕ)(Z:Finset (Site n)): Finset (Cell n) := (Z.biUnion (fun i=>℘ (roomCard k w) i)) ×ˢ univ
lemma inBooks{p:Cell n}: p∈ billsC k w Z ↔ ∃ o∈ Z,p.1∈Spindle.patch (roomCard k w) o:=by rw [billsC,mem_product,mem_biUnion]; simp only [mem_univ,and_true]
def RoomsM(M:ℕ)(Z:Finset (Site n)):= Z.biUnion (fun i=>Spindle.Room i M)
lemma buying(u:k<M): buy Z k ⊆ RoomsM M Z:= by
 intro i hi; obtain ⟨p,z,t⟩:=mem_biUnion.mp (show i∈buy Z k from hi); exact mem_biUnion.mpr ⟨p,z,inRoom t u⟩
lemma arms_fit{y:Cell n}(hc:y∈ billsC k w Z)(i:Bond n)(u:separation y.1 i.1≤ w+4)(p:debit k w≤M): i∈ RoomsM M Z:=by
 obtain ⟨o,h,hv⟩:=inBooks.mp hc; have H:= Avenue.extend o y.1 i.1 u hv; exact mem_biUnion.mpr ⟨o,h,mem_filter.mpr ⟨mem_univ _,patch_includes _ _ ((show roomCard k w + (w+4)≤debit k w by unfold debit; omega).trans p) _ H,patch_includes _ _ ((show roomCard k w+(w+4)+1≤debit k w by unfold debit; omega).trans p) _ (Avenue.extend o _ _ (sep_step i.1 i.2) H)⟩⟩
def LiftKit (X:Directions G n): LogField G n:= X ∘ (portfolio n).symm
lemma liftKit_on(X:Directions G n)(i:Bond n): LiftKit X (markZ n i) = X i:= by simp only [LiftKit,Function.comp_apply,markZ,Equiv.symm_apply_apply]
abbrev shipX(U:Config G n)(Z:Finset (Site n))(M:ℕ)(i:Bond n):G.Color:= if i∈RoomsM M Z then G.plog (G.mat (U i)) else 0
def assetX(U:Config G n)(Z:Finset (Site n))(M:ℕ): LogField G n:=LiftKit (shipX U Z M)
lemma boundedX(F:Arms G s)(V:Config G n)(p:0≤x)(hx:x≤ F.allowance.c)(z:∀ i∈RoomsM M Z,G.chord (V i)≤x) : let g:=assetX V Z M; ‖g‖≤ 2*x ∧ ∀ i∈RoomsM M Z, V i=represent g i:=by
 intro g; constructor
 · apply (pi_norm_le_iff_of_nonneg (show (0:ℝ)≤2*x by positivity)).2; intro i; let j:Bond n:= (portfolio n).symm i; change ‖shipX V Z M j‖≤_; unfold shipX; split; next h=> exact (F.allowance.sleeve _ ((z j h).trans hx)).trans (mul_le_mul_of_nonneg_left (z j h) (by norm_num))
   next h=> rw [norm_zero]; positivity
 intro i h; change V i=G.lieExp (LiftKit _ (markZ n i)) *1; rw [liftKit_on, shipX,if_pos h,mul_one,F.allowance.records _ ((z i h).trans hx)] -- tune
variable (F:Arms G s)
lemma posK (p:BudgetPoint){i:Cell n}(hz:i∈billsC k w Z) (V:Config G n)(v: ∀ i∈ Z,∀ y∈Spindle.patch M i, ∀ j:PlaqAxes,G.chord (faceValue V (y,j)) ≤ p.threshold) (b:debit k w≤M)(u:2≤p.threshold*Real.exp ((w:ℝ)/s.clip.relaxation)) : PathData.kept φ₀ p.threshold i.1 V ∧ G.chord (faceValue V i)≤p.threshold:=by
 obtain ⟨o,t,h⟩:=inBooks.mp hz; have he(y:Cell n)(q:separation i.1 y.1 ≤ w): G.chord (faceValue V y) ≤ p.threshold:= v o t y.1 (patch_includes _ _ ((show roomCard k w+w≤ debit k w by unfold debit; omega).trans b) _ (Avenue.extend _ _ _ q h)) y.2 -- syntax
 refine ⟨?_,he i (by rw [separation_self]; omega)⟩; intro y; by_cases h: separation i.1 y.1 ≤ w
 · exact (he y h).trans (le_mul_of_one_le_right p.threshold_pos.le (Real.one_le_exp (by have h':=s.clip.radius_pos; positivity)))
 refine ((G.chord_le_two _).trans u).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (div_le_div_of_nonneg_right (by exact_mod_cast (Nat.le_of_not_ge h)) s.clip.radius_pos.le)) p.threshold_pos.le) -- tune

abbrev priceP (w:ℕ)(h:ℝ) := F.C*h*widen w h s.width+2*s.paths*tar s.width w
lemma priceP_nn (u:0≤h):0≤priceP F w h:=by have hh:= F.pos; have hu:=s.paths_pos; exact add_nonneg (mul_nonneg (mul_nonneg hh.le u) (widen_nonneg w u)) (by unfold tar; positivity)
def fare(U:Config G n)(A:Clip)(P:PathData G)(i:Pressure.Twin n): G.Color:= if i.2 then P.ell U i.1 else shoot A U i.1
lemma active_chart{p:Cell n}(hz:p∈ billsC k w Z)(V:Config G n)(g:LogField G n)(W:R.Bounds φ₀ s.width s.paths Λ)(z:∀ i∈ RoomsM M Z, V i=represent g i)(hp:‖g‖ ≤ h)(hb:h ≤ F.r)(b:debit k w≤M)(t:Bool): ‖fare V φ₀ R (p,t) - xLin φ₀ R g (p,t)‖≤ priceP F w h:=by
 let u:= plotted R φ₀ w 1 V (p,t); have hY:u=plotted R φ₀ w 1 (represent g) (p,t):= plotted_near (@id (Site n)) (fun i y=>sep_step i y) _ _ _ _ _ 1 (p,t) le_rfl (fun i p=>z i (arms_fit hz i p b))
 unfold priceP; rw [add_comm]; apply (norm_sub_le_norm_sub_add_norm_sub _ u _).trans; apply add_le_add _ (le_trans ?_ le_rfl); swap; · rw [hY]; exact F.paid W g w h hp hb (p,t)
 unfold u; cases t
 · unfold fare plotted; simp only [Bool.false_eq_true,↓reduceIte, sub_self,norm_zero]; have hh:=s.paths_pos; unfold tar; positivity
 simpa only [fare, plotted,if_true, tar,Nat.cast_one,div_one] using! (SectorNext.Remainder.fine_cut_pay W p V 1 w (by omega)).2.2 -- tune
private lemma two_cost(y x:ℝ)(u:0<α): (1-α)*(y+x)^2≤ y^2+x^2/α:=by
 apply sub_le_iff_le_add'.1; apply (le_div_iff₀ u).2; nlinarith only [mul_nonneg u.le (sq_nonneg x), sq_nonneg (α*y-(1-α)*x)]
lemma base_f (p:BudgetPoint) (V:Config G n)(g:LogField G n)(W:R.Bounds φ₀ s.width s.paths Λ)(z:∀ i∈ RoomsM M Z,V i=represent g i)(u: ∀ i∈ Z,∀ y∈Spindle.patch M i,∀ j:PlaqAxes,G.chord (faceValue V (y,j))≤p.threshold)(hp:‖g‖ ≤ h)(hb:h≤ F.r)(hw:2≤p.threshold*Real.exp ((w:ℝ)/s.clip.relaxation))(b:debit k w≤M)(i:Cell n)(hz:i∈ billsC k w Z)(ht:0<α)(he:α≤1):
 (1-α)/2 *∑ t:Bool, ‖xLin φ₀ R g (i,t)‖^2 ≤ R.baseTerm φ₀ p V i+ (priceP F w h)^2/α:=by
 let Δ:= priceP F w h; let P(t:Bool):= ‖fare V φ₀ R (i,t)‖; have hh(t:Bool) : (1-α)* ‖xLin φ₀ R g (i,t)‖^2 ≤ P t ^2+Δ^2/α := by
    let B:= xLin φ₀ R g (i,t); apply le_trans (_root_.mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg (xLin φ₀ R g (i,t))) (show ‖xLin φ₀ R g (i,t)‖≤ P t+Δ from ?_) 2) (sub_nonneg.mpr he)) ?_
    · apply (norm_le_norm_add_norm_sub (fare V s.clip R (i,t)) (xLin φ₀ R g (i,t))).trans;exact add_le_add_right (active_chart F hz V g W z hp hb b t) _ -- tune args
    exact two_cost _ _ ht
 obtain ⟨h1,h2⟩:=posK p hz V u b hw; unfold PathData.baseTerm; rw [if_pos h1,PathData.clipped,if_pos h2,Fintype.sum_bool]; have h0:P false^2≤ s.clip.direct*G.chord (faceValue V i)^2:=by
    change ‖Real.sqrt s.clip.direct • G.curvature _‖^2≤_
    rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,Real.sq_sqrt s.clip.quadratic_pos.le]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (G.curvature_norm (faceValue V i)) 2) s.clip.quadratic_pos.le
 rw [show ‖R.ell V i‖=P true from rfl]
 linarith only [hh true,hh false,h0]
-- tally & exponent ledger with existing atom payment
open PathData
def accepts (s:Stage)(P:PathData G)(Y: Finset (Cell n))(X:LogField G n):ℝ:=∑ i∈Y,∑ t:Bool,‖xLin s.clip P X (i,t)‖^2
variable {δ β:ℝ}
theorem weights (p:BudgetPoint) (V Y:Config G n)(s₁:Site n→G.El)(e:Y=gauge s₁ V)(g:LogField G n)(W:R.Bounds φ₀ s.width s.paths Λ)(z:∀ i∈ RoomsM M Z,Y i=represent g i)(u:Z⊆ glow A M)(hi:∀ i:Cell n,i∈ A ↔ p.threshold < G.chord (faceValue V i))(hb:2≤p.threshold*Real.exp ((w:ℝ)/s.clip.relaxation))(b:debit k w≤M)(hk:‖g‖≤h)(hs:h≤F.r)(hp:0≤β)(ht:0<α)(he:α≤1) :
 ((1-α)*β/2)* accepts s R (billsC k w Z) g+β*(A.card*(s.clip.linear*p.threshold^2)) ≤ R.principal φ₀ p β V+ β*(((Fintype.card (Cell n)):ℝ)*((priceP F w h)^2/α))+CF.Graph.taxY n β p.threshold s.paths Λ:=by
 have hy(i:Site n)(t:i∈Z)(y:Site n)(y':y∈Spindle.patch M i)(j:PlaqAxes): G.chord (faceValue Y (y,j)) ≤ p.threshold:=by rw [e,face_gauge,G.chord_conj]; exact le_of_not_gt fun z'=> uprise (u t) y j ‹_› ((hi _).2 z') -- tune
 let U(i:Cell n):= R.baseTerm φ₀ p V i; let ξ:= s.clip.linear * p.threshold^2; have hB(i:Cell n)(z:i∈ A): ξ ≤ U i:=by
    unfold U baseTerm; let v:= G.chord (faceValue V i); have hz:p.threshold < v:= (hi i).1 z; apply le_trans _ (le_add_of_nonneg_right ?_); swap; · split<;> positivity
    rw [clipped,if_neg hz.not_ge]; unfold ξ; rw [sq,←mul_assoc]; exact mul_le_mul_of_nonneg_left hz.le (mul_nonneg s.clip.tail_pos.le p.threshold_pos.le)
 let q:= (priceP F w h)^2/α; let B:=billsC k w Z; have hX(i:Cell n)(p0:i∈B): (1-α)/2 *∑ t:Bool,‖xLin φ₀ R g (i,t)‖^2 - q ≤ U i:= by
    refine sub_le_iff_le_add.mpr ((base_f F p Y g W z hy hk hs hb b i p0 ht he).trans_eq ?_); rw [e, base_Gauge _ _ _ _ _ _ W]
 have hm:0≤q:=div_nonneg (sq_nonneg _) ht.le
 have ha:(1-α)/2 * accepts s R B g-(Fintype.card (Cell n):ℝ)*q +A.card*ξ ≤ ∑ i,U i:= calc
   _ ≤ (1-α)/2 * accepts s R B g-B.card*q +A.card*ξ := add_le_add (sub_le_sub_left (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_univ B)) hm) _) le_rfl
   _ ≤ (∑ i ∈ B,U i)+(∑ i∈ A,U i):= by
      apply add_le_add _ ((sum_le_sum (fun i p=>hB i p)).trans' (Eq.le (by simp))) -- tune
      unfold accepts; rw [mul_sum]; exact (sum_le_sum (fun i p=>hX i p)).trans' (le_of_eq (by rw [sum_sub_distrib,sum_const,nsmul_eq_mul]))
   _ ≤ ∑ i,U i:= by
     rw [←sum_union]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>R.base_nonneg ..);
     apply Finset.disjoint_left.mpr; intro i v q; obtain ⟨f,hh,t⟩:= inBooks.mp (show i ∈ B from v); exact uprise (u hh) _ _ (patch_includes _ _ ((show roomCard k w≤ debit k w by unfold debit; omega).trans b) _ t) (show (i.1,i.2)∈ A from q)
 obtain ⟨A,Bt⟩:=CF.Graph.oath W p V; have h₁:= neg_le_of_abs_le (show |∑ i:Site n,(atomSeries R.cubic p V i +atomSeries R.quartic p V i)|≤_ from A); have h₂:=neg_le_of_abs_le (show |∑ i:Site n,atomSeries R.loop p V i|≤_ from Bt); unfold PathData.principal CF.Graph.taxY; unfold U ξ B q at ha; linarith only [mul_le_mul_of_nonneg_left (add_le_add ha h₁) hp, h₂]
end Wrist
end YM.SU5.FiniteGaugeData.Galope
