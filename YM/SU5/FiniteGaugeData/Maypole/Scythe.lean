import YM.SU5.FiniteGaugeData.Maypole.Rayon
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp.Luft
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex Poin Flute
open scoped Topology ContDiff NNReal InnerProductSpace
variable {H:Hilbert}{n:ℕ}(S: OS.Semigroup H timeAxis)(Ω:H)(p:∀ x:E4, M S x Ω=Ω)
variable (G F:Fin n→ H.Op)(ν:Fin n→ℕ)(T:General)(e:Mink.Ray)
local notation "a"=>timeAxis
variable (A:Shelf S (reduced (magnet e)))(t s:Fin n→ℝ)(Y:Fin n→Cross timeAxis)(r:ℝ)(x:Points n)(h:StrictMono s)
local notation "b"=>reduced (magnet e)
local notation "J"=> rise S (reduced (magnet e)) A (soaked s) 0 ν
-- unspin clock.Meta.Down.
variable (L:Mink.Lorentz)(p':Pin L)(U:Pavilion S Ω G F ν L.val)
lemma z_banked (h:StrictMono s) : Radial (soaked s) 0 := by
 rw [show (0:Fin n→ℂ)= soaked 0 from funext fun i=>by simp [soaked]]; exact (wet 0 _).mpr h
lemma pluz(t:ℝ)(y:Cross a): board (reduced (magnet e)) t 0 y=y.val+t • basis a:=by simp [board]
lemma poleU (x:E4) : board (reduced (magnet e)) (x a) 0 (SEP a x)=x:=by rw [pluz]; exact sub_add_cancel x _ -- unused u
include p h
lemma Villing : Mell S Ω (reduced (magnet e)) A (initβ t s I) 0 Y G ν=inner ℂ Ω (pitch S G J (shape (reduced (magnet e)) t 0 Y) Ω):=by
 have h':=stunts S Ω b A (soaked s) 0 Y G ν t 0 p (z_banked s h); rw [show spur 0 0=(0:Fin n→ℂ) from funext fun _=>by simp [spur]] at h'; rw [show I=imaginary 1 from Eq.symm (by simp [imaginary]) , init_n, one_smul]; exact h' -- cast tune goal.
lemma furious (Y':Fin n→ Cross timeAxis) (e₁:∀ k, StrictMono k → TopG S Ω G ν (shape (reduced (magnet e)) k 0 Y)=TopG S Ω F ν (shape (reduced (magnet e)) k 0 Y')):
 inner ℂ Ω (pitch S G (J) (shape (reduced (magnet e)) t 0 Y) Ω) = inner ℂ Ω (pitch S F (J) (shape (reduced (magnet e)) t 0 Y') Ω):=by
 rw [←Villing S Ω p G ν e A t s Y h,←Villing S Ω p F ν e A t s Y' h]; let f(z:ℂ):=initβ t s z; let Z(B:Fin n→Cross a)(G:Fin n→H.Op)(z:ℂ):= Mell S Ω b A (f z) 0 B G ν
 have he(Y:Fin n→Cross a)(G:Fin n→H.Op)(i:ℝ): AnalyticAt ℂ (Z Y G) (imaginary i):=mellA S Ω b A Y ν f (fun _=>0) (fun _=>G) (imaginary i) ?_ (fun i=>initA ..) (fun _=>analyticAt_const) (fun _=>analyticAt_const)
 swap; · have u0:= (opal t s (0:Fin n→ℝ) i 0 h).1; change Radial (initβ t s (imaginary i)) _; exact (show soaked 0=(0:Fin n→ℂ) from funext fun _=>by simp [soaked]) ▸ u0
 apply starship (f:=Z Y G) (g:=Z Y' F) (he Y G) (he Y' F); filter_upwards [pear t s (0:Fin n→ℝ) 0 h] with i z; unfold Z f; rw [realβ]; have e':= e₁ _ z.1; -- uses name.E proof change
 have H(Q:Fin n→ Cross a)(V:Fin n→ H.Op):=meanR S Ω b A Q V ν (strumβ t s i) 0 p z.1; rwa [H Y G,H Y' F,show soaked 0=(0:Fin n→ℂ) from funext fun _=>by simp [soaked]] at e'
include p' U
lemma pondU : inner ℂ Ω (pitch S G (J) x Ω)=inner ℂ Ω (pitch S F (J) (turnO L.val x) Ω):=by
 let Y(i:Fin n):= SEP a (x i); let X:= turnO L.val x; let Z(i:Fin n):=SEP a (X i); let t:=clockV a x
 have ht(i:Fin n): (X i) a=t i := (pin_iff L).1 p' (x i); have he(i:Fin n)(k:ℝ): L.act (board b k 0 (Y i))=board b k 0 (Z i):= by rw [pluz, pluz, map_add,map_smul, show act L (basis a)=basis a from p']; exact congrArg (·+ k • basis a) ( Eq.symm (Subtype.ext_iff.mp (PinSep (x i) L p'))) -- arg order e? p
 have hx: shape b t 0 Y=x:= PiLp.ext fun i=> poleU e (x i); have hX:shape b t 0 Z=X:= PiLp.ext fun i=> by change board b _ 0 (Z i)=X i; rw [← ht]; exact poleU e (X i)
 rw [show turnO L.val x=_ from hX.symm]; nth_rw 1 [← hx]; apply furious S Ω p G F ν e A t s Y h Z ?_
 intro k z; let B:=shape b k 0 Y; let V:=shape b k 0 Z; have hf: turnO L.val B=V:= PiLp.ext fun i=> he i _; change TopG S Ω G ν B = TopG S Ω F ν V; rw [← hf]; apply U.share B; show StrictMono (clockV a (shape b k 0 Y)); rw [Vclock]; exact z; show StrictMono (clockV a (turnO L.val B)); rw [hf]; unfold V; rw [Vclock]; exact z
#print axioms pondU
-- Γ chant for small rapidities
local notation "Jr" s:max r:max=> rise S (b) A (θδ r s) (γH (ηδ r s)) ν
omit p h p' U
variable (g:Permit r) (w:ℝ)
abbrev paidV(s:ℕ)(r:ℝ): Bin n H.Op := Jr (hymns n s) r
lemma paid_idle(s:ℕ): paidV S ν e A s 0= rise S b A (soaked (hymns n s)) 0 ν:=by
 unfold paidV; congr 1; · funext i; simp [θδ,soaked]; -- tune lex
 funext i; simp [γH,ηδ]
include g
lemma chantV : Solution S ν (fun i=> paidV S ν e A i r):= by
 apply rise_g
 · exact fun i=> ψcharge _ r g (hymnsP ..)
 · intro i; simpa only [Function.comp_def,θδ,soaked,mul_zero,ofReal_zero] using (continuous_ofReal.continuousAt.tendsto (x:=Real.cosh r*0)).comp ((hymnsL n i).const_mul (Real.cosh r))
 intro i; simpa only [γH, Function.comp_def,ηδ, ofReal_zero, zero_mul, mul_zero] using (((continuous_ofReal.continuousAt.tendsto.comp (hymnsL n i)).const_mul (Real.sinh r:ℂ)).mul_const I |>.const_mul (speed:ℂ))
omit g
open Boundary Probe
variable (B:Bench S)(hΩ:∀ x:E4,M S x B.val=B.val) (P: Fin n→ Test4) -- tune namespace
include hΩ p' U A
lemma roomV (u:Ω=B.val): WaveC S B G ν P= WaveC S B F ν (active (Mink.Poincare.motion L) P):=by
 apply transport S B G F ν L P (rlock S B.val hΩ) _ _ (chantV S ν e A 0 permit_0) (chantV S ν e A 0 permit_0); intro i x; rw [paid_idle]; exact u ▸ pondU S Ω (u ▸ hΩ) G F ν e A (hymns n i) x (hymnsP n i) L p' U -- orientation u.B.val
omit p' U
variable (Q : ℂ→ Fin n→ H.Op)(T':∀ i:Fin n,∀ x:ℂ,AnalyticAt ℂ (fun y=> Q y i) x)(H':∀ x:ℝ,Pavilion S B.val G (Q x) ν (moveB e x).val)(Te:Q (imaginary r)=F) (W:Sleeps r)
include T' H' Te W
lemma spit : WaveC S B G ν P= WaveC S B F ν (active (Mink.Poincare.motion (e.boost r)) P) :=by
 have Hu:Permit r:= by simpa only [mul_one] using W 1 (by simp)
 apply transport S B G F ν (e.boost r) P (rlock S B.val hΩ) _ _ (chantV S ν e A 0 permit_0) (chantV S ν e A r Hu); intro i x; rw [paid_idle]; let t(v:Fin n):= time (x v); let y(v:Fin n):=Ray.along e (x v); let f(v:Fin n):= fsp e (x v); suffices he: shape (magnet e) t y f=x by simpa only [he] using chevalV S e B.val hΩ G F f A ν (fun k=> nez e (x k)) t (hymns n i) y r Q T' H' Te (hymnsP ..) W
 exact PiLp.ext (fun i=>attend e (x i))
#print axioms roomV
#print axioms spit
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp.Luft
