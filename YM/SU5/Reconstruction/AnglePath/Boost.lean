import YM.SU5.Reconstruction.AnglePath.Energy
/-!
# Phase budgets passed via Friedrichs comparison (the second Clasp). Generic.
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CrossedFrame.Cardio
open Function Set Filter MeasureTheory Spectral Analysis Metric
open scoped Topology NNReal ENNReal ComplexOrder InnerProductSpace
variable {K J H D:Hilbert} {X:Type}
open Clasp

namespace Organ
variable [AddCommGroup X][Module ℂ X](A:Organ X H D){G:Clasp K H H}
open Multiplier Chirp OS Semigroup Boundary Probe Picket
variable (C:Clasp J H D) {a b:Axis}(S:OS.Semigroup H a)
local notation "Π" => S.ℚmeasure
-- token for purchasing at an identified kernel alignment with this rotation.NOTE: euc.Str `G` both faces in same HA after literal rotation.
structure Tanning (a':Axis) (G:Clasp K H H): Prop where
 pre: A.Pre G
 mid: A.Core C
 paces: Paces a' S
 tide (e:ℝ)(v:e=1∨e=-1): Tide G (Picket.ticket a a' e) (ticket a a' e) e (S.ℚmeasure) (S.ℚmeasure)
 background (x:E4)(v:x a=0)(w:x a'=0): G.Pass (Picket.trans S x) (Picket.trans S x)
local notation "V"=> Picket.trans S
abbrev Pilot (t:ℝ) : H.Op:=Picket.boost C (2*t)
variable (r:b≠a) (P:Tanning A C S b G)
include P in
lemma pilotItem (u e t:ℝ)(c:e=1∨e=-1): Pilot C u * Picket.trans S (t • Picket.head a b e) = Picket.trans S ((t*Real.exp (e*u)) • Picket.head a b e) * Pilot C u := by
 let v:= -(2*u)/Real.pi; let h:= ticket a b e; let k:= Real.exp (e*u)
 have hz:0<Real.pi:=Real.pi_pos
 have ht:lengthen e (v/2)= Real.exp (e*u):= by unfold lengthen v; congr 1; field_simp
 rw [←shift b e _ S P.paces c,← shift b e _ S P.paces c]
 have he: concern Π h (t*k) = order Π (sound t ∘ (fun x=> lengthen e (v/2)*h x)) := by
   unfold concern; congr 1; rw [ht]; unfold k; funext x; unfold comp sound; push_cast; ring_nf
 change C.cLeft v * _= concern Π h (t*k)* _; rw [he]; exact A.around G P.pre C P.mid e c Π h (ticket_cont ..|>.measurable) (Picket.positive b e) (P.tide e c) _ (pure t) v
include P in
lemma drumCenter (u:ℝ){x:E4}(v:x a=0)(w:x b=0): Commute (C.cLeft u) (Picket.trans S x):=by
 have e:G.ScalePass 0 0 (V x) (V x) 1:=by
    refine ⟨IsStarProjection.zero _,IsStarProjection.zero _,?_,zero_lt_one,mobile ..,mobile ..,Commute.zero_right _, Commute.zero_right _,?_,?_⟩
    · simpa using G.one.sub G.one
    · rw [Mint.at_base,mul_one]; exact P.background x v w
    rw [inv_one,Mint.at_base,one_mul, Picket.trans_star]; exact P.background _ (by simp [v]) (by simp [w])
 obtain ⟨P',T,g⟩:= A.fundRibbon G P.pre C P.mid e zero_lt_one (by rw [one_mul]); let t:= C.cLeft u; have hg:t * V x * star t=V x:=by simpa using C.passage g u
 rw [commute_iff_eq]; nth_rw 2 [←hg]; rw [mul_assoc (t * V x), (show star t * C.cLeft u=1 from (C.left_credentials u).2.2.1),mul_one]
include P r in
lemma pilotCharge (u:ℝ)(x:E4) : Pilot C u * Picket.trans S x=Picket.trans S (Picket.move a b u x) * Pilot C u:=by
 nth_rw 1 [← heft a b x]; unfold Picket.move; rw [trans_sum S,trans_sum S,trans_sum S,trans_sum S]
 have he:= pilotItem A C S P u 1 (rise a b x 1) (by simp); have hp:= pilotItem A C S P u (-1) (rise a b x (-1)) (by simp); simp only [one_mul,neg_mul] at he hp; rcases lees r x with ⟨v,h⟩
 rw [←mul_assoc,←mul_assoc,he,mul_assoc _ (Pilot C u), hp,mul_assoc, mul_assoc, mul_assoc, (show Pilot C u * V (lee a b x)=V (lee a b x) * Pilot C u from (drumCenter A C S P _ v h).eq)] -- underscore ambiguity
 simp only [mul_assoc]

include P in
lemma columnTurn (e u:ℝ)(z:ℂ)(w:e=1∨e=-1)(c:0≤ z.re): C.cLeft u * column S b e z= column S b e (z* (lengthen e (u/2):ℝ))* C.cLeft u:=by
 have q: Tag (maker z):= by -- Dusk
    refine ⟨by unfold maker; fun_prop,1,zero_le_one,fun x=>?_⟩; simp only [maker,Complex.norm_exp,Complex.mul_re,Complex.neg_re,Real.exp_le_one_iff, Complex.ofReal_im,Complex.ofReal_re,mul_zero,sub_zero]; exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr c) (le_max_left ..)
 let L:=ticket a b e; let k:=lengthen e (u/2); have hp:k≥0:=(Real.exp_pos _).le
 have he: column S b e z = order Π (maker z ∘ L):=by unfold column; congr 1; funext x; unfold comp maker slopeRay; rw [max_eq_right (Picket.positive b e x)]; simp only [neg_mul,one_mul] -- tune
 have hx: column S b e (z*k) = order Π (maker z ∘ (fun x=> lengthen e (u/2) * L x)):=by unfold column; congr 1; funext x; unfold comp maker slopeRay; rw [max_eq_right (show 0≤ k*L x from mul_nonneg hp (Picket.positive b e _))]; unfold k L; push_cast; ring_nf
 rw [he,hx]; exact A.around G P.pre C P.mid e w Π L (ticket_cont ..|>.measurable) (Picket.positive b e) (P.tide e w) (maker z) q u
end Organ
end YM.CrossedFrame.Cardio
