import YM.SU5.FiniteGaugeData.Poin.Porting
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex Flute
open scoped Topology ContDiff NNReal InnerProductSpace
variable {H:Hilbert}{n:ℕ}(S: OS.Semigroup H timeAxis)(Ω:H)(p:∀ x:E4, M S x Ω=Ω)
variable (G F:Fin n→ H.Op)(ν:Fin n→ℕ)(T:General)(e:Mink.Ray)
local notation "a"=>timeAxis
variable (A:Shelf S (magnet e))(t s:Fin n→ℝ)(Y:Fin n→Cross timeAxis)(r:ℝ)(x:Points n)(h:StrictMono s)
local notation "b"=>magnet e
local notation "J"=> rise S (magnet e) A (soaked s) 0 ν
-- unspin clock.Meta.Down.
variable (L:Mink.Lorentz)(p':Pin L)(U:Pavilion S Ω G F ν L.val)
lemma zbank (h:StrictMono s) : Radial (soaked s) 0 := by
 rw [show (0:Fin n→ℂ)= soaked 0 from funext fun i=>by simp [soaked]]; exact (wet 0 _).mpr h
lemma plz(t:ℝ)(y:Cross a): board (magnet e) t 0 y=y.val+t • basis a:=by simp [board]
lemma poleA (x:E4) : board (magnet e) (x a) 0 (SEP a x)=x:=by rw [plz]; exact sub_add_cancel x _ -- unused u
include p h
lemma Rilling : Mell S Ω (magnet e) A (initβ t s I) 0 Y G ν=inner ℂ Ω (pitch S G J (shape (magnet e) t 0 Y) Ω):=by
 have h':=stunts S Ω b A (soaked s) 0 Y G ν t 0 p (zbank s h); rw [show spur 0 0=(0:Fin n→ℂ) from funext fun _=>by simp [spur]] at h'; rw [show I=imaginary 1 from Eq.symm (by simp [imaginary]) , init_n, one_smul]; exact h' -- cast tune goal.
lemma flooring (Y':Fin n→ Cross timeAxis) (e₁:∀ k, StrictMono k → TopG S Ω G ν (shape (magnet e) k 0 Y)=TopG S Ω F ν (shape (magnet e) k 0 Y')):
 inner ℂ Ω (pitch S G (J) (shape (magnet e) t 0 Y) Ω) = inner ℂ Ω (pitch S F (J) (shape (magnet e) t 0 Y') Ω):=by
 rw [←Rilling S Ω p G ν e A t s Y h,←Rilling S Ω p F ν e A t s Y' h]; let f(z:ℂ):=initβ t s z; let Z(B:Fin n→Cross a)(G:Fin n→H.Op)(z:ℂ):= Mell S Ω b A (f z) 0 B G ν
 have he(Y:Fin n→Cross a)(G:Fin n→H.Op)(i:ℝ): AnalyticAt ℂ (Z Y G) (imaginary i):=mellA S Ω b A Y ν f (fun _=>0) (fun _=>G) (imaginary i) ?_ (fun i=>initA ..) (fun _=>analyticAt_const) (fun _=>analyticAt_const)
 swap; · have u0:= (opal t s (0:Fin n→ℝ) i 0 h).1; change Radial (initβ t s (imaginary i)) _; exact (show soaked 0=(0:Fin n→ℂ) from funext fun _=>by simp [soaked]) ▸ u0
 apply starship (f:=Z Y G) (g:=Z Y' F) (he Y G) (he Y' F); filter_upwards [pear t s (0:Fin n→ℝ) 0 h] with i z; unfold Z f; rw [realβ]; have e':= e₁ _ z.1; -- uses name.E proof change
 have H(Q:Fin n→ Cross a)(V:Fin n→ H.Op):=meanR S Ω b A Q V ν (strumβ t s i) 0 p z.1; rwa [H Y G,H Y' F,show soaked 0=(0:Fin n→ℂ) from funext fun _=>by simp [soaked]] at e'
include p' U
lemma digs : inner ℂ Ω (pitch S G (J) x Ω)=inner ℂ Ω (pitch S F (J) (turnO L.val x) Ω):=by
 let Y(i:Fin n):= SEP a (x i); let X:= turnO L.val x; let Z(i:Fin n):=SEP a (X i); let t:=clockV a x
 have ht(i:Fin n): (X i) a=t i := (pin_iff L).1 p' (x i); have he(i:Fin n)(k:ℝ): L.act (board b k 0 (Y i))=board b k 0 (Z i):= by rw [plz, plz, map_add,map_smul, show act L (basis a)=basis a from p']; exact congrArg (·+ k • basis a) ( Eq.symm (Subtype.ext_iff.mp (PinSep (x i) L p'))) -- arg order e? p
 have hx: shape b t 0 Y=x:= PiLp.ext fun i=> poleA e (x i); have hX:shape b t 0 Z=X:= PiLp.ext fun i=> by change board b _ 0 (Z i)=X i; rw [← ht]; exact poleA e (X i)
 rw [show turnO L.val x=_ from hX.symm]; nth_rw 1 [← hx]; apply flooring S Ω p G F ν e A t s Y h Z ?_
 intro k z; let B:=shape b k 0 Y; let V:=shape b k 0 Z; have hf: turnO L.val B=V:= PiLp.ext fun i=> he i _; change TopG S Ω G ν B = TopG S Ω F ν V; rw [← hf]; apply U.share B; show StrictMono (clockV a (shape b k 0 Y)); rw [Vclock]; exact z; show StrictMono (clockV a (turnO L.val B)); rw [hf]; unfold V; rw [Vclock]; exact z
#print axioms digs
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
