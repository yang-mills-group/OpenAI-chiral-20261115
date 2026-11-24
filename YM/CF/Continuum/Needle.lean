import YM.CF.Continuum.Current
import YM.CF.Kea.Cool
import YM.CF.Sods.City

/-! # A tuned holonomy test on ¯5 production

All 4 cycles. Lattice anti-cut of the FiniteGaugeData probe construction. Inside *open*
gap for all three families; singular low mode dominates. Estimates explicitly
in side cost, so can use on the stopping lattice. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.Window
open Filter Function NormedSpace Lattice Finset Cube SU Fock Lat Spire Scroll Tulip Phase
open Laurent Next.Free Bloch Fir Ember Jill Kea Sods
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {L' B N m:Side}{j n:ℕ}
abbrev topColor (g:Fin 3):Slot:=(g, Sum.inr 0)
private lemma siteP (N:Side) : 1 ≤ (N.val:ℝ):=by exact_mod_cast N.property
def jitter (N:Side):ℝ:= ((N.val:ℝ)^8)⁻¹
def toneScale(N:Side):ℝ:= pinch N*(1-jitter N)/2
private def style (N:Side)(i:SU.F):= if i=0 then toneScale N else -toneScale N/4
def needles (N:Side): Candle:=fun _=>⟨style N,by
  unfold style; simp [SU.F,Fin.sum_univ_succ]; ring⟩
lemma jitter_prop(N:Side): 0<jitter N ∧ jitter N≤1:=by
 unfold jitter; constructor; positivity; exact inv_le_one_of_one_le₀ (one_le_pow₀ (siteP N))
lemma tones(N:Side): 0 ≤ toneScale N ∧ 2*toneScale N ≤ pinch N:=by
 let u:=jitter_prop N; have p:=pinch_pos N; have he:0≤1-jitter N:= sub_nonneg.mpr u.2; unfold toneScale; constructor; positivity; nlinarith [u.1]
lemma shift_top(N:Side)(s: Fin 3)(i:Axis) : Kea.rise (needles N) (topColor s) i= -(2*toneScale N):= by unfold Kea.rise; simp [topColor,Kea.pulse, freqD, needles,style]; ring
lemma shift_others (N:Side)(s:Slot)(h:s≠topColor s.1)(i:Axis): |Kea.rise (needles N) s i|≤ 3/2*toneScale N:=by
 have ht:= (tones N).1; obtain ⟨k,p|b⟩:=s
 · obtain ⟨⟨j,q⟩,h0⟩:=p; change j<q at h0; have e:q≠0:= by intro t; subst q; simp at h0
   by_cases p:j=0<;>simp [Kea.rise,Kea.pulse, freqD,needles,style,p,e,abs_le] <;> (constructor <;> linarith)
 have hb:b≠0:= fun v=>h (by subst b;rfl); simp [Kea.rise,Kea.pulse,freqD,needles,style,hb,abs_le]; constructor <;> linarith
lemma shift_bound (N:Side) (s:Slot)(i:Axis) : |Kea.rise (needles N) s i| ≤ 2*toneScale N:=by
 have ht:=(tones N).1; by_cases h:s=topColor s.1
 · nth_rw 1 [h]; rw [shift_top,abs_neg,abs_of_nonneg]; positivity
 exact (shift_others N s h i).trans (by linarith)

def needlesView(N:Side): Slide N (needles N) where
 u x:=⟨Kea.rise (needles N) x, (pi_norm_le_iff_of_nonneg (pinch_pos _).le).mpr fun i=> le_trans (shift_bound N x i) (tones N).2⟩
 z _:= 0
 f x:=by funext i; simp

def tinyMode(N:Side)(g:Fin 3):Stag N:=(0,topColor g)
lemma needlesValue(t:Stag N): Kea.angle (needlesView N) t=pm t.1 + Kea.rise (needles N) t.2:=by simp [Kea.angle,needlesView]
lemma principal_start(N:Side) : Lat.principal (0:Per N)=pinch N:=by
   unfold Lat.principal; rw [Ember.tone]; simp only [ZMod.val_zero, Nat.cast_zero,mul_zero,zero_add,one_mul]; rw [if_pos]; unfold pinch; exact div_le_self Real.pi_pos.le (siteP N)
lemma tiny_value(N:Side)(g:Fin 3) : ‖Kea.angle (needlesView N) (tinyMode N g)‖=pinch N*jitter N:=by
 let i:=tinyMode N g; have he(a:Axis):Kea.angle (needlesView N) i a=pinch N * jitter N:=by rw [needlesValue]; change Lat.principal (0:Per N) + Kea.rise (needles N) (topColor g) a=_; rw [shift_top,principal_start]; unfold toneScale; ring
 refine le_antisymm ((pi_norm_le_iff_of_nonneg ((mul_pos (pinch_pos N) (jitter_prop N).1).le)).mpr ?_) ?_
 · intro a; rw [show Kea.angle _ _ a=_ from he a]; rw [Real.norm_of_nonneg ((mul_pos (pinch_pos N) (jitter_prop N).1).le)]
 apply le_trans ?_ (norm_le_pi_norm (Kea.angle (needlesView N) i) 0); rw [he,Real.norm_of_nonneg ((mul_pos (pinch_pos _) (jitter_prop _).1).le)]
lemma other_mode {s:Stag N}(p:s≠tinyMode N s.2.1): pinch N/4 ≤ ‖Kea.angle (needlesView N) s‖:=by
 have hp:=pinch_pos N; rw [needlesValue]; by_cases h:s.2=topColor s.2.1
 · have h0: s.1 ≠0:= fun u=> p (Prod.ext u h); obtain ⟨i,e⟩:= Function.ne_iff.mp h0; apply le_trans ?_ (norm_le_pi_norm _ i); rw [Pi.add_apply]; nth_rw 1 [h]; rw [shift_top,Real.norm_eq_abs]; change pinch N/4 ≤ |Lat.principal (s.1 i)+_|; rw [ch_price]; let j:=chert (s.1 i)
   have he:j≠0:=by intro h; apply e; change s.1 i=0; rw [←chert_cast (s.1 i)]; rw [show chert _=0 from h]; simp
   change pinch N/4 ≤ |(2*(j:ℝ)+1)*pinch N+ -(2*toneScale N)|; by_cases h1:1 ≤ j
   · refine le_trans ?_ (le_abs_self _); have ht:(1:ℝ) ≤ j:=(by exact_mod_cast h1); nlinarith [(tones N).2]
   have ht:(j:ℝ) ≤ -1:=(by exact_mod_cast (show j≤ -1 by omega)); apply le_trans ?_ (neg_le_abs _); nlinarith [(tones N).1]
 apply le_trans ?_ (norm_le_pi_norm _ 0); rw [Pi.add_apply]; let u:= pm s.1 0; let v:= Kea.rise (needles N) s.2 0; change _ ≤|u+v|; have hg:= shift_others N s.2 h 0; change |v|≤_ at hg; have he: |u+v|≥|u|-|v|:=(by simpa only [sub_neg_eq_add,abs_neg] using (abs_sub_abs_le_abs_sub u (-v))); have hh: pinch N≤|u|:=cohere _; linarith [(tones N).2]
lemma every_mode(s:Stag N) : pinch N*jitter N/4 ≤ ‖Kea.angle (needlesView N) s‖:=by
 have hp:=pinch_pos N; by_cases h:s=tinyMode N s.2.1
 · nth_rw 1 [h]; rw [tiny_value]; nlinarith [(jitter_prop N).1]
 exact le_trans (by nlinarith [(jitter_prop N).2]) (other_mode h)
lemma needlesSlow(N:Side):speedB (needles N) (More N):=by
 intro i k; have h:= tones N; have hp:= (nPos N); change |style N k|≤ _; apply _root_.le_trans (b:=toneScale N); · unfold style; split; rw [abs_of_nonneg h.1]; rw [abs_le]; constructor <;> linarith [h.1]
 have he:=h.2; rw [show Real.pi=N.val*pinch N from payH]; rw [show ((More N).val:ℝ)=(N.val:ℝ)*2 by unfold More; push_cast; rfl]; rw [le_div_iff₀ (by positivity)]; nlinarith [pinch_pos N]
end YM.CF.Window
