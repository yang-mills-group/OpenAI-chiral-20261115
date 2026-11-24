
import SatinPP.Exhibit
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
open Quays
open Function Filter Metric Set OS OS.Semigroup Hierarchy.Seld Complex MeasureTheory
open Spectral Boundary Probe
open scoped Topology BigOperators NNReal InnerProductSpace

variable {H:Hilbert} {a:Axis}

structure Spool (H:Hilbert) where
  d:ℕ
  cell:H.Op
namespace Spool
variable (p:Spool H)
def dual:Spool H:=⟨p.d,star p.cell⟩
variable (S:OS.Semigroup H a)
abbrev Token (A:Stamp H):Prop:=Role S p.d A p.cell

abbrev Mink (g:Test4):Bench S→ₗ[ℂ]Bench S:=ℑ S p.cell g p.d
abbrev WickPath (g:Test4)(l u:ℝ) (z:ℂ):Bench S→ₗ[ℂ]Bench S:=
   Wick S l u p.cell g p.d z
end Spool

variable {S:OS.Semigroup H a}{l u:ℝ}{g:Test4}
lemma Band.reduced (v:Band a l u g){b:ℝ}(h:0<b):
 Band a (b*l) (b*u) (rev a h g):=by
 constructor
 · change IsCompact (tsupport _)
   rw [rev_place]
   exact v.wide.image (earlyT a h).continuous
 intro p t
 rw [rev_place] at t
 rcases t with ⟨p,t,rfl⟩
 rw [reelT_self]
 exact ⟨mul_lt_mul_of_pos_left (v.snug p t).1 h,mul_lt_mul_of_pos_left (v.snug p t).2 h⟩


section Pose

variable (S) (B:H.Op)
lemma coat_reduce {b:ℝ}(h:0<b):
 coat S l u B g b= coat S (b*l) (b*u) B (rev a h g) 1:=by
 let f:=reelT a b
 have e(p:E4):entry S l u B b p=entry S (b*l) (b*u) B 1 (reelT a b p):=by
   have α : infer b (fore a l p)=infer 1 (fore a (b*l) (f p)):=by
      unfold infer fore f;rw [reelT_self];push_cast;ring
   have β : infer b (aft a u p)=infer 1 (aft a (b*u) (f p)):=by
      unfold infer aft f;rw [reelT_self];push_cast;ring
   unfold entry Q; rw [α,β,map_neg,map_neg,reelT_cross]
 ext1 x; simp_rw [coat_val,e]
 exact rev_integral a h g (fun p=>entry S (b*l) (b*u) B 1 p x)
variable {B}{b:ℝ}
lemma Wick_reduce (h:0<b) (v:Band a l u g) (d:ℕ):
 Wick S l u B g d b= Wick S (b*l) (b*u) B (rev a h g) d 1:=by
 ext1 y; apply Subtype.ext; apply cache_I S d
 rw [wPaid S _ _ B v d _ _ (inside_subset_sheath (a:=(b:ℂ)) h),
    wPaid S _ _ B (v.reduced h) d _ _ (inside_subset_sheath eu),
    coat_reduce S B h]


variable {S}
lemma heat_spool (P:Spool H){A:Stamp H}(T:∃ m c,Paid S m c A)
 (e:P.Token S A) (v:Band a l u g)(h:0<b)(Y:Bench S):
 (P.WickPath S g l u b Y).val=
 voyage S A (b*l) (b*u) 1 (rev a h g) Y.val:=by
 obtain ⟨_,_,c⟩:=T
 rw [Spool.WickPath,Wick_reduce S h v]
 exact opens c (v.reduced h) eu e Y
end Pose

/-- Vacuum of program. -/
structure Sleeper (S:OS.Semigroup H a) where
  y:Bench S
  core(t:ℝ≥0): S.E t y.val=y.val

variable (S)
lemma sleeperV (w:Sleeper S)(t:ℝ):S.edge t w.y.val=w.y.val:=by

 exact (SelectionAnalysis.lamp_fixed S _).mpr w.core t

/- Two panels, early and late. gap positive. Orientations not rotated. -/
variable (w:Sleeper S)(l u L U:ℝ)(g f:Test4)(P Q:Spool H)

-- solo centered read = onepoint
def solo (P:Spool H)(g:Test4)(l u:ℝ)(z:ℂ):ℂ:=
 inner ℂ w.y.val (P.WickPath S g l u z w.y).val
/-- Analytical two-point read with true product. -/
def pair (P:Spool H)(g:Test4)(l u:ℝ)(Q:Spool H)(f:Test4)
    (L U:ℝ)(z:ℂ):ℂ:=
 inner ℂ w.y.val (P.WickPath S g l u z
           (shutter S (L-u) z (Q.WickPath S f L U z w.y))).val
lemma solo_harbor (r:Band a l u g):Harbor (solo S w P g l u):=
 ((Wick_harbor S l u P.cell r P.d (road_const S w.y)).under).pass (innerSL ℂ w.y.val)
lemma pair_harbor (r:Band a l u g)(s:Band a L U f)(h:u<L):
  Harbor (pair S w P g l u Q f L U):=
 ((Wick_harbor S l u P.cell r P.d (shutter_harbor S _ (sub_pos.mpr h)
   (Wick_harbor S L U Q.cell s Q.d (road_const S w.y)))).under).pass (innerSL ℂ w.y.val)


lemma w_border(t:ℝ): border S t w.y = w.y:=Subtype.ext ((border_val ..).trans (sleeperV S w t))
lemma border_vac (t:ℝ)(X:Bench S):
 inner ℂ w.y.val (border S t X).val= inner ℂ w.y.val X.val:=by
 rw [border_val,←timeslot,tboth]
 conv_lhs => rw [←neg_smul,timeslot,sleeperV]
lemma solo_mink (r:Band a l u g){b:ℝ}(h:0<b):
 solo S w P g l u (sideways b)=inner ℂ w.y.val (P.Mink S (rev a h g) w.y).val:=by
 unfold solo Spool.WickPath
 rw [Wick_edge S l u P.cell r P.d h,
   LinearMap.comp_apply,LinearMap.comp_apply,border_vac,w_border]
lemma pair_mink (r:Band a l u g)(s:Band a L U f){b:ℝ}(h:0<b):
 pair S w P g l u Q f L U (sideways b)=
   inner ℂ w.y.val (P.Mink S (rev a h g) (Q.Mink S (rev a h f) w.y)).val:=by
 unfold pair Spool.WickPath
 simp only [Wick_edge S l u P.cell r P.d h,Wick_edge S L U Q.cell s Q.d h,LinearMap.comp_apply,border_vac,w_border,shutter_edge]
 rw [border_march,border_march,show u*b+(L-u)*b+ -L*b=0 by ring]
 simp only [border,zero_smul,uh_zero]


variable {b:ℝ}
lemma shutter_move (b c d :ℝ):shutter S (d-c) b=shutter S (b*d-b*c) 1:=by
 ext1 Y
 apply Subtype.ext
 change tide S (infer b _) Y.val=tide S (infer 1 _) Y.val
 congr 2; unfold infer;push_cast;ring
lemma solo_reduce (r:Band a l u g)(h:0<b):solo S w P g l u b=
    solo S w P (rev a h g) (b*l) (b*u) 1:=by
 unfold solo Spool.WickPath;rw [Wick_reduce S h r]
lemma pair_reduce (r:Band a l u g)(s:Band a L U f)(h:0<b):pair S w P g l u Q f L U b=
    pair S w P (rev a h g) (b*l) (b*u) Q (rev a h f) (b*L) (b*U) 1:=by
 unfold pair Spool.WickPath;rw [Wick_reduce S h r,Wick_reduce S h s,shutter_move]
variable {A D:Stamp H}
lemma shutter_heat (t:ℝ)(Y:Bench S):
    (shutter S t 1 Y).val=S.E t.toNNReal Y.val:=by
 change tide S (infer (1:ℂ) t) Y.val=_
 simp [infer,tide,S.birth] -- check


variable (T:∃ m c,Paid S m c A)(C:∃ m c,Paid S m c D)(x:P.Token S A)(y:Q.Token S D)
include x T
lemma solo_eu (r:Band a l u g):
 solo S w P g l u 1=inner ℂ w.y.val (voyage S A l u 1 g w.y.val):=by
 unfold solo Spool.WickPath;obtain ⟨_,_,c⟩:=T
 rw [opens c r eu x]

include C y in
lemma pair_eu (r:Band a l u g)(s:Band a L U f):
 pair S w P g l u Q f L U 1=
    inner ℂ w.y.val (voyage S A l u 1 g (S.E (L-u).toNNReal (voyage S D L U 1 f w.y.val))):=by
 unfold pair Spool.WickPath;obtain ⟨_,_,c⟩:=T; obtain ⟨_,_,d⟩:=C
 rw [opens c r eu x,shutter_heat,opens d s eu y]

#print axioms heat_spool
#print axioms pair_harbor
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Silk
