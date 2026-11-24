import Bay.D.Minnow
import Bay.D.Yacht
import Bay.Loggia
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
open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection Zephyr.Chern
local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine
open Carol

open Laurent
variable {a b c r D L δ mW:ℝ}{w:Berth}{z:Cover}{m:ℕ}
local notation "τflux"=>Zephyr.Chern.stream
lemma fuelX (g:w.Rig a c m)(x:Site w.side)(s:Signed)(u:Pane w.side)
 (h:Guard u w.d):
 ech (room x s) (w.M (profile u))=
    swapX (detX s) (w.M (profile (flashA (room x s) u))):=by
 let P:=w.P.par;let t:=room x s
 have ht:1≤P.K.j:= by rw[P.kJ]; norm_num
 let f:=P.V.note.fields_one w.side (P.U.needed.trans g.deep)
 rw[show detX s=detX t.s from (congrArg detX (show t.s=s from p_s x)).symm]
 exact funde_f (castX t) (xtra t.charge) (spinU t.charge t.s) (spinZ t.charge t.s) u _ ht w.R.J.M _ f (h.shrink P.U.gem)

lemma anchor(z:Cover):separation (node (w.home z)) 1 ≤ size ((2:ℕ) • z):=by
 unfold Berth.home
 rw[ node_wrap,separation,add_sub_cancel_right]
 exact pdist_wrap ..

abbrev tuneZ (w:Berth)(x:Site w.side)(f:w.First):Pane w.side→ℂ:=
    gapX w.p w.K x f.X
structure Phoenix (w:Berth)(x:Site w.side)(f:w.First)(A:Icey (Cella (More w.side)))(r L δ:ℝ):Prop where
    phoenix: Vessel w.p (node x) (w.p.B/10) r w.d L (tuneZ w x f) A
    jewel: gem (tuneZ w x f ∘ Zephyr.Chern.petals (τflux _)) δ
    stamp: bud (tuneZ w x f ∘ Zephyr.Chern.petals (τflux _)) 2 = splash A (sheet _ paint)
    sweat: (δ/bytes)^2 ≤ mass A


lemma sail {W V:ℝ}
  (t:Calcite a w.d D r V)(x:Oily a w.d (breadth z) W)(hz:0 < δ)
  (p:Shallow w.p (w.p.B/10) w.side r)
  (g:4*(w.p.B/10+3+size ((2:ℕ) • z))+1<w.side.val)
  (y:∀ s,gem (spout (play (w.home z) s m w.M) (τflux _)) δ)
  (q: W*quota^2*w.wid a b≤δ/2)
  (l: w.Rig a c m)(f:w.First)(u:w.Before a b m (w.home z) f):
 ∃ A, Phoenix w (w.home z) f A r (max (quota^2*b) (V*(quota^2*b))) (δ/2):= by
 have hk:=Berth.clearance l
 have hj:=y;rw [←add_halves δ] at hj
 rw[mul_assoc] at q
 have h:=spark hk.dept (fuelX l (w.home z)) u.lump hk u.stone u.endStone x (deep_grace z) q hj
 obtain ⟨v,A,s⟩:= sonata hk u.stone t p
 have j:4*(w.p.B/10+3+separation (node (w.home z)) 1)+1<w.side.val:=by
    apply lt_of_le_of_lt _ g
    have :=anchor (w:=w) z; gcongr
 obtain ⟨e,mc⟩:=vivid s t.rp j h (half_pos hz).le
 exact ⟨A,⟨v.more (le_max_left ..),s.more (le_max_right ..)⟩,h,e,mc⟩

lemma harbor_frost{P:VΩ} (hr:0<r): ∀ᶠ s:ℕ in atTop,
    frosty (Pressure.radiusB (xTop P s)/10) (Pressure.temp (xTop P s)) ≤ iceR r ∨
      ¬0<Pressure.temp (xTop P s):=by
 have he := ((Work.E09.radiusB_temp 0).add (Work.E09.radiusB_temp 1)).const_mul 8
 simp only [zero_add,mul_zero,pow_zero,pow_one,←add_mul] at he
 filter_upwards [(turnover P.par).eventually (he.eventually (ge_mem_nhds (ice_pos hr)))] with s g
 by_cases h:0<Pressure.temp (xTop P s)
 · apply Or.inl
   unfold frosty xTop
   rw[mul_assoc]
   apply le_trans _ g
   gcongr; exact Nat.div_le_self .. -- gcongr h solved?
 exact Or.inr h

theorem regatta {P:VΩ}(a c b:ℝ)(m:ℕ)(z:Cover)(t:0< m)
  (ha:0<a)(hb:0≤b):
 ∃r L δ,0<r∧0≤L∧0<δ ∧ Dry P (fun w=>w.Rig a c m →∀f,w.Before a b m (w.home z) f→
     ∃ A,Phoenix w (w.home z) f A r L δ):=by
 obtain ⟨W,⟨x⟩⟩:=oily ha P.par.dpos (breadth z)
 obtain ⟨δ,hδ,u⟩:=starrySky P m t z
 obtain ⟨D,r,V,y⟩:=calcites ha P.par.dpos
 refine ⟨r,max (quota^2*b) (V*(quota^2*b)),δ/2,y.rp,
    (mul_nonneg (sq_nonneg _) hb).trans (le_max_left ..),half_pos hδ,?_⟩
 filter_upwards [u,(existOil a b (W*quota^2) P ha).eventually (ge_mem_nhds (half_pos hδ)),harbor_frost (P:=P) y.rp] with s H J E
 filter_upwards [(ageFar P s).eventually_gt_atTop (4*(Pressure.radiusB (xTop P s)/10+3+size ((2:ℕ) • z))+1)] with i p k _ g f h
 let w:=takeUp P s i k
 have hx : 4*(w.p.B/10+3+size ((2:ℕ) • z))+1<w.side.val:=by rw [g.sizeB];exact p
 have hp:Shallow w.p (w.p.B/10) w.side r:=by
   refine ⟨?_,?_,?_⟩
   · have:=w.p.B_pos;omega
   · change 2*(w.p.B/10+1)< w.side.val*2; omega
   
   rw [g.threshold,g.sizeB]
   exact E.resolve_right (not_not.mpr (show 0<w.th from g.threshold ▸ w.p.threshold_pos))
 have t : W*quota^2*w.wid a b ≤ δ/2:=by unfold Berth.wid;rw [g.sizeB];exact J
 exact sail y x hδ hp hx (H i k) t g f h
end YM.CF.Bay.D
