import YM.CF.BProof.Gates.Entice

/- y receipt for any other sizes: only need PL block horizon ν≥bound; bands itself
 purchased independent. Buyer can ask for ≥4 or arbitrarily large. Arithmetic in D.B weight.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Gates
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Charge Charge.Form Gauss Weights Pricing
open scoped Topology BigOperators Classical MatrixOrder Matrix
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}
namespace Stage
variable (S:Gates.Stage c w R v) (L:Side) (a:ℕ)(y:ℝ)
structure Entice (W:ℕ) (y:ℝ) where
 dull : Dull S (gap L a) (DP L a y) y
 Ppos : 0<r_P L y
 rise : DP L a y+2*a=LP L y
 size : SizedP (LP L y) y
 lamp : sizeP y ≤ 2*(DP L a y:ℝ)
 Fqual : S.F.k₀ ≤ r_F y S.scene.size
 reach : gF y S.scene.size ≤ DP L a y/32
 lower : S.scene.size*Face.rY y ≤ gF y S.scene.size
 upper : (gF y S.scene.size:ℝ) < 2*S.scene.size*Face.rY y
 choice : bound S y (gap L a) ≤ W
 wide : 1 < DP L a y/32
 block : W ≤ DP L a y/32
 econ : 5*S.M y+2 < 2*(DP L a y/32)
 time : 4*(5*S.M y+3)+4 ≤ DP L a y
 after : 2≤S.M y

lemma entice (D:ℝ→ℕ) (v:PL fun y=>(D y:ℝ)) (h:∀ᶠ y in atTop,bound S y (gap L a) ≤ D y): ∀ᶠ y:ℝ in atTop, Nonempty (Entice S L a (D y) y):=by
 filter_upwards [h,S.geometry L a D v,S.book L a,scale_domain L a, Gates.permit L a S.scene.size (one_pos.trans_le S.scene.target) S.F.k₀] with y H h g V w; obtain ⟨A⟩:= g; obtain ⟨p,q,k,l'⟩:= w; exact ⟨A,V.2.1,V.1.2,V.2.2.1,V.2.2.2,p,q,k,l',H,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩
-- Integration setup geometry. include grid counts independent period. `W` block budget as in operator. require c'.val ≥4; can be made ≥arbitrary.
structure Setup (s:Side) (W:ℕ) (y:ℝ) where
 sheet : Bands s L a (LP L y)
 face : Side
 face_p : 4≤ face.val
 mesh : Ratio face s
 exact : mesh.count.val=gF y S.scene.size
 c' : Side
 g : Ratio c' s
 space : g.count.val=W
 hope : 4≤ c'.val
variable {s:Side}{D:ℕ}(P:Entice S L a D y)(Y:Setup S L a s D y)
namespace Setup
variable {S L a y} -- alias keep all implicit p? make Lean easier.
def yard := {toStrips:= Y.sheet.toStrips,even_q:=Y.sheet.even_count : Yard s}
def hall : Angular.Hall s:= ⟨S.F,S.K,Y.face,Y.mesh,r_F y S.scene.size⟩
lemma width : Y.yard.short=gap L a:=Y.sheet.gap_len
include P
lemma length : Y.yard.long=DP L a y:=by exact (Nat.add_right_cancel (Y.sheet.band_len.trans P.rise.symm))
include P
def pulse : Model S.K S.P c Y.yard.short S.M R y S.κ:= (by rw [width]; exact P.dull.p)
lemma sized : Face.Sized S.scene.size Y.mesh y (r_F y S.scene.size):= ⟨Y.face_p,Y.exact,by rw [Y.exact]; exact P.lower,by rw [Y.exact]; exact P.upper⟩
lemma room : Charge.Room Y.yard (S.M y):= ⟨(length P Y).symm ▸ P.time,P.after⟩
theorem agenda : Agenda Y.yard Y.hall Y.g S.K S.P 1 S.height S.M c w R S.κ y (S.focus Y.yard.short y) 4:=by
 let H:=P.dull; let d:=gap L a; let t:=S.focus Y.yard.short y
 have hl : bound S y Y.yard.short ≤ Y.g.count.val:=by rw [Y.space,Y.width]; exact P.choice
 unfold Stage.bound least at hl; have hx : Y.hall.k=r_F y S.scene.size:=rfl
 have hu : Deep.D Y.yard=DP L a y/32:=by unfold Deep.D; rw [length P]
 have hp:0<t:= Stage.focus_h S y _
 refine ⟨hu.symm ▸ P.wide,by rw [hu]; exact P.econ,by omega,by omega, ⟨?_,?_,?_,?_,?_,?_⟩,by norm_num, stretch_p _ (by norm_num) hp ?_, stretch_p _ (by norm_num) hp ?_,?_, H.ink,H.thin,pace_j ..,pace_w ..⟩ -- tune order
 · have := show 1<Deep.D Y.yard from hu.symm ▸ P.wide; unfold Deep.D at this; omega
 · rw [hu, show Y.hall.g.count.val=gF y S.scene.size from Y.exact,one_mul]; exact P.reach
 · rw [hu, Y.space]; exact P.block
 · exact Y.face_p
 · exact Y.exact
 · exact P.Fqual
 · unfold dist_need at hl; omega
 · rw [show Y.hall.X=S.F from rfl,hx]; unfold dist_need at hl; omega
 rw [Y.width]; exact H.stamp
lemma permits (q:BudgetPoint)(h:q.threshold=thresh y):ValidR c q (S.M y):= P.dull.permit q h -- local override?
-- connect label role onto Fields both before and after. For any labels in issued ward all face firms.
lemma firm (U:Config G s) (F:Y.yard.FaceS)(h:Y.yard.Climbed y Y.hall U F) : ∀ i, ¬Y.yard.D i→∀ b,Y.yard.Firmly Y.hall U F i b:= by
 intro i hi b; have hh:= P.dull.frame s Y.hall rfl rfl (Y.sized P) P.Fqual (Y.yard.u i) U (F i)
 rw [← length P Y] at hh; exact ⟨_,_, (hh (h i hi)).1 b⟩
lemma proceeds (T: PathData G)(θ:ℝ)(x:Pawn Y.yard) (h:Pawn.Rich Y.yard Y.hall y T θ (pulse P Y).X S.κ x) : Pawn.Proceeds Y.yard Y.hall y T θ (pulse P Y).X S.κ x:= Pawn.Rich.lucky Y.yard Y.hall x y T θ _ h (firm P Y _ _ (Y.yard.climbed y Y.hall _ _ h.2.2.1)) -- tune arg
end Setup
end Stage
end YM.CF.BProof.Gates
