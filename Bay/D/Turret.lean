import Bay.D.Coast
import YM.SU5.Thin.Glacier.Crest
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

namespace D
open Exterior Precision Nacre
open scoped ContDiff
open Regis Regis.Head Etch Gleam Next.SectorChange Next.SectorChange.Gaussian
open Pressure Work.F03 ProbabilityTheory
local notation "T4"=>SU.group

open Next.Rank.Spindle
variable {c n:Side} {q:Ratio c n} {A:Support c} {D:Finset (Cell n)}
  {U:Config T4 n}{x:Head.Dir T4 n}{p:BudgetPoint}{a b k:ℕ}{o:Site n}
 (g:Kite n)

lemma spritz(a:Scree.pingS p.threshold (Lattice.halo b {g.rise o}) U):
    Scree.pingS p.threshold (Lattice.halo b {o}) (g.swirl U):=by
 intro j hj
 change (T4).chord (faceValue (Lattice.pull g.turn g.gust U) j)<_
 rw [Face.send_price _ _ _ _ _ (T4).chord_inv (fun w z=>(T4).chord_conj z w)]
 apply a
 obtain ⟨x,u,v⟩:=Finset.not_disjoint_iff.mp hj
 refine Finset.not_disjoint_iff.mpr ⟨g.rise x,?_, by rw[Work.H03.touched_send];exact mem_image_of_mem _ v⟩
 exact (show Lattice.halo b {g.rise o}= (Lattice.halo b {o}).image g.rise by
   unfold Kite.rise; rw[←Tye.dignify,image_singleton]).symm ▸ mem_image_of_mem g.rise u

lemma garden {x:Site n}(h:x∈Lattice.halo k {o}):separation (g.rise o) (g.rise x) ≤ k:=by
 have a:=mem_image_of_mem g.rise h
 unfold Kite.rise at a;rw[←Tye.dignify,image_singleton] at a
 obtain ⟨i,h,t⟩:=halo_spec.mp a
 rw [mem_singleton.mp h] at t; exact t

lemma rain(j:Cell n)
    (h:meek p U=D)(u: afar D a o)
    (q:separation o j.1 ≤ a):
    (T4).chord (faceValue U j) < p.threshold:=by
 have z:j∉D:= fun i=>(u j i).not_ge q
 refine lt_of_le_of_lt (le_of_not_gt ?_) (half_lt_self p.threshold_pos)
 exact fun v=>z (h ▸ mem_filter.mpr ⟨mem_univ _, v⟩)

lemma pelargon (t:b+2≤a)(h:meek p U=D)
 (u:afar D a (g.rise o)):
    Scree.pingS p.threshold (Lattice.halo b {o}) (g.swirl U):=by
 apply spritz
 intro i h
 obtain ⟨x,y,w⟩:=Finset.not_disjoint_iff.mp h
 obtain ⟨i',j,t⟩:=halo_spec.mp y
 rw [mem_singleton.mp j] at t
 apply rain _ ‹meek p U=D› u
 rw[←separation_comm]
 exact (separation_triangle i.1 x _).trans (le_trans
    (Nat.add_le_add (Work.E01.sep_touched _ _ w) ((separation_comm ..).trans_le t)) (by omega))

-- working bond estimate. 
variable {v:ℝ}(R:Rules T4)
lemma witness
   (w:TrustLogs x U q A v)(t:Gleam.Safe q A a o)
   (l:v≤R.c) (j:Pressure.Bond n)
   (h:separation o j.1+1≤a):
   represent x j=U j:=by
 have u:q.parent j.1=q.parent o:=t.2 _ (by omega)

 have z : q.parent (j.1+step j.2)=q.parent o:=
    t.2 _ ((separation_triangle _ j.1 _).trans ((Nat.add_le_add_left (Work.E01.sep_step_le j.1 j.2) _).trans h))
 obtain ⟨d,e⟩:=w j (by unfold Working InHouse; rw[u,z]; exact ⟨t.1,rfl,rfl⟩)
 rw [represent_link,show x (j.1,coord j.2)= _ from d, R.records (U j) (e.trans l)]

lemma walkBack(a:Step)(x:Site n): separation x (a.used x).1≤ 1:=by
 cases h:a.neg
 · simp[Step.used,h]
 simp only [Step.used,h,ite_true]; rw[separation_comm]
 have w:=Work.E01.sep_step_le (x-step a.dir) a.dir
 rw[sub_add_cancel] at w; exact w


lemma breathable
  (w:TrustLogs x U q A v)(t:Gleam.Safe q A a (g.rise o))
  (l:v≤R.c)(p:k+2≤a):
    Lattice.Agrees (Lattice.halo k {o}) (g.swirl U) (represent (g.sail x)):=by
 have e:represent (g.sail x)=g.swirl (represent x):=by simpa only [one_smul] using bank_at g.turn g.gust x 1
 rw[e]; intro i h _
 let B:=(posDir i.2).rotate g.turn
 have z : separation (g.rise o) (B.used (g.rise i.1)).1 ≤ k+1 :=
    (separation_triangle _ (g.rise i.1) _).trans (Nat.add_le_add (garden g h) (walkBack ..))
 have H:=witness R w t l (B.used (g.rise i.1)) ((Nat.add_le_add_right z _).trans p)

 change B.read U (g.rise i.1) = B.read (represent x) (g.rise i.1)
 rw[Step.read, Step.read, H]

lemma gale(h:ProbeBox x v)(t:0≤v): ‖g.sail x‖ ≤v:=by
 refine (pi_norm_le_iff_of_nonneg t).mpr fun i=>?_
 change ‖Bid.pulled (Head.arbor g.gust x) g.turn i‖≤v
 unfold Bid.pulled; dsimp only
 split
 · rw[norm_neg]

   let j:= ((posDir (axisEquiv.symm i.2)).rotate g.turn).used (affine g.turn 0 i.1)
   exact h (j.1+g.gust,j.2)
 let j:= ((posDir (axisEquiv.symm i.2)).rotate g.turn).used (affine g.turn 0 i.1)
 exact h (j.1+g.gust,j.2)

def Tall(k:ℕ):Prop:=∀ i s,(budD i s).length≤k
def Shutter(p:BudgetPoint) :Prop:=100≤p.B ∧ Tall (p.B/10)
local notation "K"=>p.B/10
lemma lNear(ht:Shutter p)(i:Cella n)(h:i.1∈Lattice.halo (p.B/10+3) {o}):
 separation (g.rise o) (leaf g i).1 ≤ p.B:=by
 apply (separation_triangle _ (g.rise i.1) _).trans
 exact le_trans (Nat.add_le_add (garden g h) ((Work.E04.slot_separation ..).trans (ht.2 i.2.1 g.turn))) (by have hz:=ht.1;omega)
-- K.succ expands p.B/10.succ? use (p.B/10+3)
lemma lDeep(ht:Shutter p)(td:Deep q A D (hallBill p.B) (g.rise o))
    (i:Cella n)(h:i.1∈Lattice.halo (p.B/10+3) {o}):
    rimB q A p.B D (leaf g i):=by
 apply td.turn
 have :=lNear g ht i h
 unfold hallBill Sequest
 omega

abbrev chia (R:Rules T4)(p:BudgetPoint)(v:ℝ):=p.threshold+faceCutError R v
lemma chia_p (p:BudgetPoint)(v:ℝ):0≤chia R p v:=by
 unfold chia faceCutError
 have :=R.positive; have :=p.threshold_pos;have:0<(T4).colorScale:=(T4).colorScale_pos
 positivity
lemma lCurl(ht:Shutter p)(td:Deep q A D (hallBill p.B) (g.rise o))
   (w:TrustLogs x U q A v)(hv:0≤v)(hj:v≤R.c)(hm:meek p U=D)
   (i:Cella n)(h:i.1∈Lattice.halo (p.B/10+3) {o}):
   |brine (g.sail x) i|≤chia R p v:=by
 rw [brine_sail,abs_mul,parity,skewSq,one_mul]
 let b:=leaf g i
 let z:=faceValue U b
 have hz:(T4).chord z <p.threshold:=rain b hm td.2 ((lNear g ht i h).trans (by unfold hallBill Sequest;omega))
 have hk:= angleFaceSmall w hv hj b (td.1.shift (e:=4) (by
   have :separation (g.rise o) b.1 ≤ p.B:=lNear g ht i h
   unfold hallBill Sequest;omega))
 let a:=faceCurl b x
 have hy:=PiLp.norm_apply_le a i.2.2; rw[Real.norm_eq_abs] at hy
 refine hy.trans ?_
 refine (norm_le_norm_sub_add a ((T4).curvature z)).trans ?_
 rw [norm_sub_rev a,add_comm]

 exact add_le_add (((T4).curvature_norm z).trans hz.le) hk.2
lemma lDuct (w:TrustLogs x U q A v)(td:Deep q A D (hallBill p.B) (g.rise o))(hj:v≤R.c):
    Lattice.Agrees (Lattice.halo (p.B/10) {o}) (g.swirl U) (represent (g.sail x)):=breathable g R w td.1 hj (by unfold hallBill Sequest;omega)
lemma lAwning (td:Deep q A D (hallBill p.B) (g.rise o))(hm:meek p U=D):
   Scree.pingS p.threshold (Lattice.halo p.B {o}) (g.swirl U):=
 pelargon g (show p.B+2≤hallBill p.B by unfold hallBill Sequest;omega) hm td.2
end YM.CF.Bay.D
