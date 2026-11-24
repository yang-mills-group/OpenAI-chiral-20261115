import Compass.Needle
import Compass.Sloop
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Compass
open Function Filter Metric Fock Lattice Wilson Laurent Lat Rush Cube Skye Spire Scroll
open Pec Moto
open scoped Matrix Polynomial
open StressFlux AnalyticBridge.VerifiedReset
-- coherent shape tests at single root. det group argument s inverse doesn't change det
def SkateGlyph (S:Signed)(c:Bool): Bool:= c.xor (detX S)
def HasCrystal(S:Skate): Prop:= ∀ s:Signed, ∀ q:Bool, Anchored s → ∀ j l,
     (if tariffX s then (-1:ℝ) else 1) • (S (PlaqAxes.rotate s j) (PlaqAxes.rotate s l)) = (dirS s j*dirS s l) • Scroll.cSignX (SkateGlyph s q) (S j l)
abbrev p01:PlaqAxes:=⟨(0,1),by decide⟩
abbrev p02:PlaqAxes:=⟨(0,2),by decide⟩
abbrev p03:PlaqAxes:=⟨(0,3),by decide⟩
abbrev p12:PlaqAxes:=⟨(1,2),by decide⟩
abbrev p13:PlaqAxes:=⟨(1,3),by decide⟩
abbrev p23:PlaqAxes:=⟨(2,3),by decide⟩
def paintS(S:ℂ):Skate:=fun i j=> if i≠ j then 0 else if i=p02∨i=p13 then S else if i=p03∨i=p12 then -S else 0
lemma plaqlist:∀ a:PlaqAxes, a=p01∨ a=p02∨a=p03∨a=p12∨a=p13∨a=p23:=by decide
lemma rotplain(s:Signed)(h:s.perm=Equiv.refl Axis)(q:PlaqAxes): PlaqAxes.rotate s q=q:=by
 cases q with| mk x v=> obtain ⟨a,b⟩:=x; apply Subtype.ext; simp [PlaqAxes.rotate,PlaqAxes.ordered,h,le_of_lt v]
variable {S:Skate}(h:HasCrystal S)
include h
lemma lit_S (i j:PlaqAxes): star (S i j)= S i j:=by
 have ht:= h 1 true Anchored.one i j; rw [rotplain 1 rfl,rotplain 1 rfl,tax_i,SkateGlyph,det_i] at ht; unfold dirS StressFlux.sign at ht; simpa [i.property,j.property,Scroll.cSignX, -Fin.is_le'] using ht.symm
lemma onlyDiag (a b:PlaqAxes)(p:a≠b): S a b=0:=by
 rcases a with ⟨⟨i,j⟩,hp⟩; rcases b with ⟨⟨k,l⟩,hq⟩; change i < j at hp; change k<l at hq
 let a:PlaqAxes:=⟨(i,j),hp⟩; let b:PlaqAxes:=⟨(k,l),hq⟩
 let Y(v:Axis):=Signed.mirror v
 have ht:∃ v:Axis, dirS (Y v) a * dirS (Y v) b = -1:=by
    by_cases u:i=k
    · subst k; have e:j≠l:=fun q=>p (by apply Subtype.ext; exact Prod.ext rfl q)
      exact ⟨j,by simp [dirS,a,b, Y,Signed.mirror,StressFlux.sign, hp.ne,hp.ne.symm,e,hp,hq]⟩
    by_cases w:i=l
    · have e:k≠j:=ne_of_lt (hq.trans (w ▸ hp)); exact ⟨j,by simp [dirS,a,b,Y,Signed.mirror,StressFlux.sign, e.symm,w.symm,hp,hp.ne.symm,(show k< i from w.symm ▸ hq),show j≠l from hp.ne.symm.trans_eq w]⟩
    exact ⟨i,by simp [dirS,a,b,Y,Signed.mirror,StressFlux.sign, hp.ne,hp,hq,w,u]⟩
 obtain ⟨v,m⟩:=ht
 have ht:= h (Signed.mirror v) false (allFlips _ rfl) a b
 rw [rotplain _ rfl, rotplain _ rfl,m,tax_m,SkateGlyph, det_t] at ht
 simp [Scroll.cSignX,lit_S h] at ht
 replace ht:a=a ∧ S a b + S a b=0:=⟨rfl,eq_neg_iff_add_eq_zero.mp ht⟩; rcases ht with ⟨_,ht⟩; have hb:= congrArg Complex.im ht; have he:= congrArg Complex.re ht; norm_num at he hb; apply Complex.ext
 · change (S a b).re=0; linarith
 change (S a b).im=0; linarith
-- chirality already. diag anticommute.
lemma snowy (x y:Axis)(e:x≠y)(v:Anchored (Pec.X (Equiv.swap x y)))(a:PlaqAxes) : S (PlaqAxes.rotate (Pec.X (Equiv.swap x y)) a) (PlaqAxes.rotate (Pec.X (Equiv.swap x y)) a)= - S a a:=by
 let P:=Pec.X (Equiv.swap x y)
 have he:=h P false v a a; rw [show tariffX P=true from tax_s x y e,dirS_sq,one_smul,SkateGlyph,show detX P=true from detSwap x y e] at he; simp [Scroll.cSignX,lit_S h] at he; exact neg_eq_iff_eq_neg.mp he -- check
omit h
private lemma aSwap : Anchored (Pec.X (Equiv.swap (0:Axis) 1)):=by decide
private lemma bSwap : Anchored (Pec.X (Equiv.swap (2:Axis) 3)):=by decide
include h
lemma diag_S : S = paintS (S p02 p02):=by
 let d:=Pec.X (Equiv.swap (0:Axis) 1); let u:=Pec.X (Equiv.swap (2:Axis) 3)
 have h1:= snowy h 0 1 (by decide) aSwap; have h2:= snowy h 2 3 (by decide) bSwap
 have hr:= h1 p01; have hs: S p01 p01=0:=by
    change S p01 p01= -S p01 p01 at hr; apply Complex.ext
    · have k:=congrArg Complex.re hr; change _=-_ at k; change _=0; linarith only [k]
    have k:=congrArg Complex.im hr; change _=-_ at k; change _=0; linarith only [k]
 have hr2:= h1 p23; have hk:S p23 p23=0:=by
    change S p23 p23= -S p23 p23 at hr2; apply Complex.ext
    · have k:=congrArg Complex.re hr2; change _=-_ at k; change _=0; linarith
    have k:=congrArg Complex.im hr2; change _=-_ at k; change _=0; linarith
 have hx:S p03 p03= - S p02 p02:= h2 p02
 have hv:S p12 p12= - S p02 p02:= h1 p02
 have hz:S p13 p13=S p02 p02:=(h1 p03).trans (by rw [hx,neg_neg]) -- defeq args concrete?
 funext a b; by_cases p:a=b; swap; · unfold paintS; rw [if_pos p]; exact onlyDiag h a b p
 subst b; unfold paintS; rw [if_neg (not_not_intro rfl)]; rcases plaqlist a with l|l|l|l|l|l <;> subst a
 all_goals first
  | (rw [if_neg (by decide),if_neg (by decide)]; assumption)
  | (rw [if_pos (by decide)]; assumption)
  | (rw [if_pos (by decide)])
  | (rw [if_neg (by decide),if_pos (by decide)]; assumption)
#print axioms diag_S
end YM.CF.Compass
