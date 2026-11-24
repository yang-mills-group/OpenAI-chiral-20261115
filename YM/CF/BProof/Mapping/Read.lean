import YM.CF.BProof.Mapping.Up
import YM.CF.BProof.Release.Cut

/- Draw field type for common reading arguments. Signs true only N; no instruction reading
 D (equip 0), so will implement core enumerator via components i not D. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Mapping
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox House
open Charge (Tile Room Cave)
open Gauss Release Release.hot
open scoped Topology BigOperators Classical Matrix InnerProductSpace Matrix.Norms.Frobenius
local notation "G"=> SU.group
variable {s c: Side}(Y:Yard s)(g:Ratio c s)(S:Hall s)
structure Pawn (Y:Yard s) where
 sev : Finset Y.Col
 gauss : Roll.Plan Y
 gap : Locale.House Y
 dust : Config G s
 mood : Y.Glyph
namespace Pawn
variable {Y}
variable (x y:Pawn Y)(Z: Finset (Block Y c))
structure Agreed : Prop where
  sev (b): hide Y g b∈Z→ (b∈ x.sev↔ b∈ y.sev)
  gauss (b:Roll.Stamp Y): hide Y g b.1 ∈ Z → x.gauss b=y.gauss b
  gap (b:Y.Col): hide Y g b∈ Z→ x.gap b=y.gap b
  dust (b:Bond s): addr Y g b.1∈ Z→ x.dust b=y.dust b
  mood (i:Y.Index) (b: Bool) (p:Space s): ¬Y.D i→ hide Y g (location Y i b,p)∈ Z→ x.mood i (b,p)=y.mood i (b,p)
variable (z:ℝ)(T:PathData G){R:ℝ}{c':Clip}{M:ℕ}(θ:ℝ)(U:Beam c' R Y.short M z)
variable {S}
-- coordinate projection

def level := Release.γ Y T θ z U x.sev x.gauss x.gap
def issue := Locale.issue Y (level x z T θ U)
variable (S)
def rent := Y.sweepLabel z S (issue x z T θ U) x.mood
def put := Y.play z S (issue x z T θ U) (rent S x z T θ U) x.dust

def Shade (b:Y.Col)(R:ℕ): Prop := ∀ j, (Gauss.base Y).N b j R→ hide Y g j∈ Z
-- tangential homes
abbrev BlockShade (b:Y.Col)(R:ℕ): Prop := ∀ j:Y.Col,j.1=b.1→ Grid.dist (hide Y g b) (hide Y g j) ≤ R→ hide Y g j∈ Z
lemma block_read (b:Y.Col)(r:ℕ){k:ℕ}(h:k≤r*g.count.val) (p: BlockShade g Z b r): Shade g Z b k:= fun i v=>p i v.1.symm (near_hide Y g b i r ((Gauss.base Y).mono h v))
lemma shade (b:Y.Col)(r:ℕ)(u:Shade g Z b r): hide Y g b∈Z:=u b ((Gauss.base Y).start ..)
lemma shade_rides {b j:Y.Col}{r k:ℕ}(u:Shade g Z b (r+k))(v:(Gauss.base Y).N b j r): Shade g Z j k:=fun i p=> u i ((Gauss.base Y).triangle v p)
lemma local_level (h: Room Y M)(b:Y.Col)(p:Agreed g x y Z)(w: Shade g Z b U.horizon'):
    level x z T θ U b=level y z T θ U b:=by
 let l:=Beam.ζ_v T θ U h; let A:=Gauss.base Y
 have hg:hide Y g b∈ Z:= shade g Z b _ w
 have he: b∈x.sev ↔ b∈ y.sev:= p.sev b hg
 by_cases u:b∈x.sev; exact (if_pos u).trans ((p.gap b hg).trans (if_pos (he.mp u)).symm)
 unfold level Release.γ; rw [Sky.open_o _ _ _ _ U b _ u,Sky.open_o _ _ _ _ U b _ (he.not.mp u)]
 congr 1; ext t; unfold pin Function.curry Beam.drive Matrix.mulVec dotProduct; apply Finset.sum_congr rfl; intro j _; by_cases e:A.N b j.1 U.horizon'
 · rw [p.gauss j (w j.1 e)]; exact congrArg (·*_) (l.lock (b,t) _ _ (fun i (v:i∈ A.ball b U.horizon') => p.sev i (w i ((A.ball_m ..).1 v))) j)
 dsimp only; rw [l.door (b,t) j _ e,l.door (b,t) j _ e,zero_mul,zero_mul]
lemma paid_level {i:Y.Index}(p:Space s)(a:Y.Apt): put S x z T θ U (Y.inter ((i,p),a))=level x z T θ U (i,p) a:= Eq.trans (Y.mix_field _ _ (Y.inter_mem ((i,p),a))) (Locale.at_issue ..)
private lemma inter_bore' {b:Bond s}(t:Y.Door)(h:b=Y.inter t): addr Y g b.1=hide Y g t.1:=by
 rw [h]; unfold addr col inter; simp only [horiz,time_join,space_join]; rw [Posts.gap Y _ _ (Y.atD_mem t.1.1 t.2.1.isLt)] -- tune
lemma local_gap (h:Room Y M) (b:Bond s)(u:b∈Y.field) (p:Agreed g x y Z)(w: Shade g Z (col Y b.1) U.horizon'): issue x z T θ U b=issue y z T θ U b:=by
 obtain ⟨v,rfl⟩:= Y.reachedBy b u; have he : col Y (Y.inter v).1=v.1:= by unfold col inter; simp only [horiz,time_join,space_join]; rw [Posts.gap Y _ _ (Y.atD_mem v.1.1 v.2.1.isLt)]
 rw [he] at w; unfold issue; rw [Locale.at_issue,Locale.at_issue,local_level g x y Z z T θ U h v.1 p w]
lemma paid (p:Y.Index)(i:Bool)(h:¬Y.D p)(t: Space s × TAxis) : inlet (Y.u p) Y.long (issue x z T θ U) i t=level x z T θ U (location Y p i,t.1) (Y.lastDepth,t.2):=by
 let e : Y.Door:= ((location Y p i,t.1),Y.lastDepth,t.2); change issue x z T θ U (horiz _ t.1 t.2)=_; have he: horiz (front (Y.u p) Y.long i) t.1 t.2=Y.inter e:=by unfold inter e Angular.Yard.reach; dsimp only; rw [Y.last_depth, Y.atD_full,Y.gFrame _ _ h]
 rw [he]; exact Locale.at_issue ..
end Pawn
end YM.CF.BProof.Mapping
