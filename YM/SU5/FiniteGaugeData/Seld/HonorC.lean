import YM.SU5.FiniteGaugeData.Seld.NewMoon
import YM.SU5.FiniteGaugeData.Seld.ShadeTree
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
open Function Filter Metric Complex Set MeasureTheory Lattice Mist Celeritas Land OS OS.Semigroup
open scoped Topology BigOperators NNReal ENNReal InnerProductSpace ComplexOrder ContDiff
variable {K:Axis→Hilbert}(W:∀ a:Axis, OS.Semigroup (K a) a)(Ω:(i:Axis)→(K i).space) {H:Hilbert} {a:Axis}
namespace Breve
variable (a b:Axis)(L A B R:Shrine K) (m n:ℕ) (o y x z:E4)(t:ℝ)
local notation "Sb"=> W b
local notation "Sa"=> W a
variable (U:Set (Shrine K))
structure Pace :Prop where
 app : b≠a
 first : Modicum W Ω a b U
 Ωa(z:E4): (W a).unit.translation z (Ω a)=Ω a
 coneP : Cinema (W a)
 coneF : Cinema (W b)
 spanning(k:Bool): Seance W Ω U a k
structure Stake : Prop where
 A₁: A ∈ Magic W U m
 A₂: B ∈ Magic W U n
 L0: A.t a=0
 R0: B.t a=0
abbrev Trace(O T:Shrine K→ℝ)(p:Bool):Set (K a).space := {v|∃ L:Shrine K,L∈U∧∃ x:E4,Want a b p (T L) (O L) x∧ v=soup W Ω a L p x}
variable (HX: Pace W Ω a b U) (H0:Stake W a A B m n U)
include HX
lemma LinearK (p:Bool)(O T:Shrine K→ℝ): Annihilated (W a) (Trace W Ω a b U O T p):= fun x t=> spatial_s W Ω U a b p HX.Ωa HX.app HX.coneP O T (HX.spanning p) x (fun L p y v=> t _ ⟨L,p,y,v,rfl⟩)
open Boundary Probe
variable (g h:Test4) (s δ:ℝ≥0)(u:0<s)(u':0<δ)(X X':Bench (W a))
-- Precaution field on both timelines may have width b>0 (gauge arrays). wind cost terms as user.
-- K.L define Land pricing noncompact.S.
omit HX
abbrev Shave :Prop:= ∀ y∈ tsupport g, |y a-o a|<(s:ℝ) ∧ (s:ℝ)+(δ:ℝ)≤ y b-(B.t b)-(o b+A.t b)
abbrev Shaving :Prop := ∀ o∈tsupport h, Shave a b A B o g s δ
variable (V':ℝ) (ht:∀ y∈tsupport g,y b≤ V') (Hh: Shave a b A B o g s δ)
include H0 HX V' ht u u' Hh
lemma highD (o0:o a=0): DotComm (Sa) (A.f a) (B.f a) o g m n X X':=by
 let O(L: Shrine K):= o a-2-L.t a; let O'(R: Shrine K):= o a+2+R.t a; let D(L:Shrine K):= -(o b-A.t b)+L.t b; let D'(R: Shrine K):= (s:ℝ)+ (δ:ℝ)+R.t b+(V'+B.t b)
 apply arriere (W a) (A.f a) (B.f a) o g m n X X' (Trace W Ω a b U O D true) (Trace W Ω a b U O' D' false) (LinearK W Ω a b U HX true O D) (LinearK W Ω a b U HX false O' D') ?_
 rintro _ ⟨L,x',x,v,rfl⟩ _ ⟨R,z',z,w,rfl⟩; let p:Line2 a L A B R o o x z:= ⟨H0.L0,H0.R0,rfl,by rw [v.1]; unfold O; ring,by rw [w.1]; unfold O'; ring⟩; have q(y:E4)(g':y∈tsupport g) : |y a| < (s:ℝ) ∧ WaveK b L A B R o y x z (s+δ):= by
    obtain ⟨hc,bh⟩:= Hh y g'; rw [o0,sub_zero] at hc; refine ⟨hc,?_,bh,?_⟩
    · linarith only [show -(o b-A.t b)+L.t b < -(x b) from v.2]
    · linarith only [show (s:ℝ)+(δ:ℝ)+R.t b+(V'+B.t b)< z b from w.2, ht y g']
 exact avail W Ω a b L A B R m n o x z HX.app HX.coneF s δ U HX.first ⟨x',z',H0.A₁,H0.A₂⟩ p o0 u u' g q
-- any point.Key shift by whole point (not just time) makes ground spectator at 0, simplify. bounds.A.
lemma highD' : DotComm (Sa) (A.f a) (B.f a) o g m n X X':=by
 apply yank _ _ _ _ _ _ _ X X' o; rw [sub_self]
 let f:= ahead (-o) g; have he(y:E4)(p:y∈ tsupport f): y+o∈ tsupport g:= by simpa using route (-o) g p
 have hz:∀ y∈ tsupport f,y b≤ V'-o b:=fun y p=>by have hv:=ht _ (he y p); change y b+o b≤ _ at hv; linarith
 have hp:Shave a b A B 0 f s δ:=by intro y t; obtain ⟨q,r⟩:= Hh (y+o) (he y t); change |y a+o a-o a|< _ at q; rw [add_sub_cancel_right] at q; refine ⟨by simpa,?_⟩; change _≤ y b+o b-_-_ at r; simp only [PiLp.zero_apply,zero_add]; linarith
 exact fun x y=> highD W Ω a b A B m n 0 U HX H0 f s δ u u' x y (V'-o b) hz hp rfl -- check args
#print axioms highD'
omit Hh
lemma esteem (z: Shaving a b A B g h s δ): (ℑ (W a) (A.f a) h m).comp (ℑ (W a) (B.f a) g n) = (ℑ (W a) (B.f a) g n).comp (ℑ (W a) (A.f a) h m) := Eff (W a) _ _ g h m n (fun p h x y=> highD' W Ω a b A B m n p U HX H0 g s δ u u' x y V' ht (z p h))
#print axioms esteem
end Breve
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Leal
