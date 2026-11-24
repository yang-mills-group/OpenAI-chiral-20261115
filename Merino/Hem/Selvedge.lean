import Merino.Hem.Juno
import Merino.Waist
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 28000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Hem
open Filter Topology Lattice Lat Tulip Branch Cube Tenant Drapes Metric
open _root_.Zephyr.Chern
open scoped Matrix Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Finset Swell

variable {n:Side}

open Py.Rate.LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Skye Scree Vale RG
open Py (hueW stemS pinpr)
variable (P:Spine)



lemma regnum_big (s:ℕ): Tendsto (fun i=>(RegNum P s i).val) atTop atTop:=by
 apply tendsto_atTop_mono _ P.run.ir_grows.tendsto_atTop
 intro i
 let v:= (P.run.ir i).val
 change v≤v*P.par.R.L.val^s*2*P.par.block.val
 exact (Nat.le_mul_of_pos_right _ (pow_pos (P.par.R.L.property) s)).trans
   ((Nat.le_mul_of_pos_right _ (by decide:0<2)).trans
      (Nat.le_mul_of_pos_right _ P.par.block.property))

open Sour Scroll Spire
private lemma shorten
  {o:Seat n}{X Y F:Oil n}{a b c d B E δ:ℝ}{m:ℕ}(t:Trunk o X m a b d)
  (g:Soak o Y a c d)(p:∀ V:Openc (More n) d,F V.val=X V.val+Y V.val)
  (σ:Signed)
  (u:Oily a d B E)(v: Temper (boxA (rim n σ) o) (stream n) B)
  (h:δ+E*(Tenant.quota^2*c)<slash σ *
    (bud (glaze (stream n) (julStep (rim n σ) F)) 2).re):
   let f:=glaze (stream n) (julStep (rim n σ) X)
   Bud f ∧ δ < slash σ * (bud f 2).re:=by
 let s:=rim n σ
 have y:=soak_glaze (jul_sells s g) u v
 have x:=soak_glaze (trunk_move t s).pay u v
 have r:glaze (stream n) (julStep s F) =ᶠ[𝓝 0] (glaze (stream n) (julStep s X))
      + glaze (stream n) (julStep s Y):=by
    filter_upwards [petals_open u.s.ready (stream n)] with j hj
    let w:=Sour.fog s d ⟨_,hj⟩
    change (ech s⁻¹ (F w.val)).trace=(ech s⁻¹ (X w.val)).trace+(ech s⁻¹ (Y w.val)).trace
    rw [p]; unfold ech; rw [singT,win_a,map_add,Matrix.trace_add];rfl
 rw [((x.1.bloom.add y.1.bloom).congr r).bud_eq,Pi.add_apply,Complex.add_re,mul_add] at h
 refine ⟨x.1,?_⟩
 let z:=bud (glaze (stream n) (julStep s Y)) 2
 have yp:slash σ * z.re ≤ E*(Tenant.quota^2*c):=by
    refine (le_abs_self _).trans ?_
    rw [abs_mul, slash_abs,one_mul]
    exact (Complex.abs_re_le_norm _).trans (y.2 _)
 exact lt_of_add_lt_add_right (h.trans_le (add_le_add_right yp _))

def Wreath (n:Side) (F:Oil n)(δ:ℝ)(σ:Signed):Prop:=
    let f:=glaze (stream n) (julStep (rim n σ) F)
    Bud f ∧ δ < slash σ * (bud f 2).re

abbrev petals_fee (P:Spine)(m:ℕ)(z:Cover)(p:Bolts)(δ:ℝ)(σ:Signed)(s i k:ℕ):Prop:=
   ∀ d:Dress P s i k p m (wrap _ z),Wreath _ d.y.color δ σ

lemma spruced (h:SprigFee P){m:ℕ}(hm:0 < m)(z:Cover)(p:Bolts)(σ:Signed):
   ∃ δ:ℝ,0<δ∧onReg P (petals_fee P m z p δ σ):=by
 obtain ⟨v,a,q,H⟩:=uncle σ h hm z (by rw [P.par.kJ]; decide)
 obtain ⟨E,⟨e⟩⟩:=oily p.decay P.par.dpos (breadth (offing σ z))
 have t:Tendsto (fun s=>E*(Tenant.quota^2*(loseM P p.a s*p.c))) atTop (𝓝 0):=by
    simpa only [zero_mul,mul_zero] using ((((lose_limit P p.a p.decay).mul_const p.c).const_mul
      (Tenant.quota^2)).const_mul E)
 refine ⟨v/2,half_pos a,?_⟩
 unfold onReg
 filter_upwards [H,t.eventually (gt_mem_nhds (half_pos a))] with s g f
 filter_upwards [(regnum_big P s).eventually_ge_atTop q] with i l k _ d
 have y:=d.ticket.hem.sip
 change Trunk (node d.y.origin) _ _ _ _ _ at y
 rw [d.here] at y
 refine shorten (δ:=v/2) (F:=cuirass P m z s i k) y d.wane d.glaze_funds σ e ?_ ?_
 · rw [box_off]
   exact deep_grace _
 exact lt_trans (add_lt_add_right f _ |>.trans_eq (add_halves _)) (g i k l)

lemma wreathing (h:SprigFee P){m:ℕ}(hm:0 < m)(z:Cover)(p:Bolts):
   ∃ δ:ℝ,0<δ∧onReg P (fun s i k=>
     ∀ d:Dress P s i k p m (wrap _ z),∀ σ,Wreath _ d.y.color δ σ):=by
 choose e u v using spruced P h hm z p
 let t:=(Finset.univ:Finset Signed)
 have r:t.Nonempty:=univ_nonempty
 obtain ⟨w,l,j⟩:=exists_min_image t e r
 refine ⟨e w,u w,?_⟩
 unfold onReg at *
 filter_upwards [eventually_all.mpr v] with s g
 filter_upwards [eventually_all.mpr g] with i f k b d σ
 have x:=f σ k b d
 exact ⟨x.1,(j σ (mem_univ _)).trans_lt x.2⟩
