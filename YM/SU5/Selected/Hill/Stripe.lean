import YM.SU5.Selected.Hill.Pont
import YM.SU5.Selected.Hill.Luge
import YM.SU5.Selected.Hill.Order
/-! # Coordinates of the read service. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Hill.Box
open Function Filter Metric Finset Lattice Tree Wilson RG Pressure Exterior Work.F03 Precision MeasureTheory Chene Trunk FreeResolvent Matrix Chene.Tail Melody SectorNext.Vacuum.FlatTree Calculus Next.Rank.Axial Chene.Perks
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius MatrixOrder Matrix InnerProductSpace Kronecker
open Next.SectorChange Luge SectorTools.PhysicalGaussianSwitch
variable {G:Gauge}{n:Side}(r:Side)(S:Lots n)(B':ℕ)
abbrev goods (G:Gauge) := LinkArray G (seat_set r S B')
abbrev Borders(G:Gauge):= LinkArray G (outside r S B')
abbrev frost := (freeze (G:=G) (columbia r n) (fun i=> i∈ Board r S B'))
def tones (x:goods r S B' G)(y:Borders r S B' G): Config G n:= (columbia r n).drape (frost r S B' x y)
lemma tones_mb (y:Borders r S B' G): Measurable (fun x=> tones r S B' x y) := (columbia r n).continuous_drape.measurable.comp ((freeze_meas (columbia r n) _).comp (measurable_id.prodMk measurable_const))
lemma tones_hit (x:goods r S B' G)(y:Borders r S B' G)(i:seat_set r S B') : tones r S B' x y (distil r S B' i)=x i:=by
 unfold tones; rw [←freeze_held (columbia r n) (fun i=> i∈ Board r S B') x y i]; exact (columbia r n).off_tree (frost r S B' x y) i.val
lemma tones_miss (x z:goods r S B' G)(y:Borders r S B' G)(j:EdgeT n)(q:∀ i,distil r S B' i ≠ j): tones r S B' x y j= tones r S B' z y j:=by
 by_cases p:j∈ (columbia r n).trunks
 · exact ((columbia r n).on_tree _ ⟨j,p⟩).trans ((columbia r n).on_tree _ ⟨j,p⟩).symm
 let f:FreeX r n:=⟨j,p⟩; have hp:f∉ Board r S B':=fun h=>q (⟨f,h⟩: seat_set r S B') rfl; let i:outside r S B':=⟨f,hp⟩; have he(x:goods r S B' G): tones r S B' x y j=y i:= ((columbia r n).off_tree (frost r S B' x y) f).trans (freeze_regular (columbia r n) (· ∈ Board r S B') x y i)
 rw [he,he]
variable {r S B'}{W:PathData G}{C:Clip}{P:BudgetPoint}{v κ e u:ℝ}(Z:ChartRatio G)(p:LocalRatio Z)
variable (L: Next.Rank.Spindle.Rules G)(x:goods r S B' G)(y:Borders r S B' G)
def keyUp (U:Config G n): ListT G n:= colordown (fun i=> G.plog (G.mat (U i)))
lemma homeward (y:Borders r S B' G)(i:Pens G (seat_set r S B')): keyUp (tones r S B' 1 y) (palace r S B' i)=0:=by
 change G.plog (G.mat (tones r S B' 1 y (distil r S B' i.1))) i.2=0; rw [tones_hit,Pi.one_apply,G.mat_one,G.plog_one]; rfl
lemma tinsel_l(v:Scene G (seat_set r S B'))(x:goods r S B' G)(y:Borders r S B' G)(h:∀ i:seat_set r S B', G.plog (G.mat (x i))= colorup v i):
 scrim (tones r S B' x y)= tin (keyUp (tones r S B' 1 y)+icing (distil r S B') v):=by
 let O:=seat_set r S B'; let G':=keyUp (tones r S B' x y); let U:= keyUp (tones r S B' 1 y); let A:=icing (distil r S B') v; suffices p:G'=U+A by
    change _=tin (U+A); rw [← p]; rfl
 funext i; let f:Pens G O → Pens G (EdgeT n):= palace _ S B'; by_cases e:∃ j:O, distil r S B' j=i.1
 · obtain ⟨j,d⟩:=e; let k:Pens G O:=(j,i.2); have he : f k=i:=Prod.ext d rfl; have hU:U i=0:= he ▸ homeward y k; have hA:A i=v k:=he ▸ reception f (fun i j p=> Prod.ext ((distil_inj r S B') (congrArg Prod.fst p)) (show (f i).2=(f j).2 from congrArg Prod.snd p)) _ _; rw [Pi.add_apply,hU,hA,zero_add]; change (G.plog (G.mat (tones r S B' x y i.1))) i.2= _; rw [← d, tones_hit, h] -- may rfl
   rfl
 rw [Pi.add_apply, show A i=0 from Calculus.displaced _ _ (fun j h=> e ⟨j.1, congrArg Prod.fst (show f j=i from h)⟩), add_zero]; dsimp only [U,G', keyUp, colordown]; rw [tones_miss r S B' x 1 y i.1 (not_exists.mp e)]
-- next log panel hYP:U menu over.
lemma charts_up {x:goods r S B' G} (a: ℝ)(w:1≤B')(h:S=menu (tones r S B' x y) a)(d:0 ≤ a)(z:4*r.val*a≤e)(he:e≤ L.c)(u:2*e < Z.radius)(i:seat_set r S B') : G.lieExp (G.plog (G.mat (x i)))=x i ∧ ‖G.plog (G.mat (x i))‖ ≤ 2*e:=by
 let U:=tones r S B' x y; have hg:Light r S 1 i.val.val.1:=(mem_filter.mp i.property).2.small w; have hp: Light r (menu U a) 1 i.val.val.1 := h ▸ hg
 have ht:= ((hp.link (frost r S B' x y) rfl i.val.val.2 d)).trans z
 have h':G.chord (x i) ≤ e:=by rw [← tones_hit r S B' x y i]; exact ht
 exact ⟨L.records _ (h'.trans he), (L.sleeve _ (h'.trans he)).trans (mul_le_mul_of_nonneg_left h' (by norm_num))⟩
include p
lemma arrival (v:Scene G (seat_set r S B'))(q:colorup v ∈ mouth Z)(a:ℝ)(w:1≤B')(t: x= release 1 (colorup v))(g:S= menu (tones r S B' x y) a)(d:0≤a)(z:4*r.val*a ≤e)(he:e≤L.c)(u:2*e< Z.radius)(i: seat_set r S B'): G.plog (G.mat (x i))=colorup v i∧ ‖colorup v i‖≤2*e:=by
 have he':G.lieExp (colorup v i)= x i:= by nth_rw 1 [t]; change _= _ *1; simp -- nth caution
 obtain ⟨A,C⟩:= charts_up Z L y a w g d z he u i; have hh:= p.inject (mem_ball_zero_iff.mpr (C.trans_lt u)) (q i (Set.mem_univ _)) (A.trans he'.symm); exact ⟨hh,hh ▸ C⟩ -- mem_ball_zero_iff?
end YM.Hill.Box
#print axioms YM.Hill.Box.tinsel_l
#print axioms YM.Hill.Box.arrival
