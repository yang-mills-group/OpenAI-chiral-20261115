
import Organdy.Droplet
import Organdy.Domaine
import Organdy.Album
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Larva
open Filter Topology Metric Lattice Exterior Precision 
open Tulip Branch Cube Lat Tenant Drapes _root_.Zephyr.Chern

open scoped Matrix.Norms.L2Operator Matrix
attribute [local instance] opCStarAlgebra
local notation "G" => SU.group
variable {N m:Side}{d r:ℝ}


open Swell Scree Skye RG Fock Wilson Payne MeasureTheory
open _root_.Zephyr.Chern


open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
-- BudgetPoint namespace? rg
variable {o:Site (More N)}{X: Oil N}{A: Dye N}{K:Scree.Loom N}{p:BudgetPoint}{D b:ℝ}
variable (h:Canal (lensBox (p.B/10) o) X b d)(f:WindowDress K p d)

include h f
lemma heart:
    chime K p o X 1=sketch X 0:=by
 have e:(1: Config SU.group (More N))∈safeZone p o:=by
    intro i _
    simpa [faceValue,travel,square] using p.threshold_pos
 rw [chime,litView f h e (fun _ _ _=>rfl) (guard0 f.pos.le)]
 have m:represent (0:Dir (More N))=1:=by funext i; simp [represent,collect,RG.increment]
 rw [sketch,story,m]
variable (t:Spool d r)
  (l:Album d r D p.threshold (p.B/10) o X A)
  {η:ℝ}
include t l
lemma silken (v:separation 0 o≤1)
  (a:‖chime K p o X 1‖≤ η):
  Domaine (p.B+6) r p.threshold η D (chime K p o X) A:=by
 let Z:=slatLit f h
 have U:0≤D:=(A.qty_nonneg).trans l.pie
 rw [heart h f] at a

 let B:=p.B/10
 let Y:=lensBox (p.B+6) (0:Site (More N))
 have m:foot p o⊆Y:=by
   intro i g
   obtain ⟨x,h,d⟩:=halo_spec.mp g
   rw [Finset.mem_singleton] at h;subst x
   exact halo_spec.mpr ⟨0,Finset.mem_singleton_self _,(separation_triangle ..).trans
     ((Nat.add_le_add v d).trans (by omega))⟩
 refine ⟨(show Continuous (fun A:Op (Single N)=>Matrix.trace A) from continuous_id.matrix_trace).measurable.comp Z.bright,fun g x=>?_,fun x y a=>
   congrArg Matrix.trace (Z.local_ x y (agrees_mono a m)), fun x=>?_,l.pal,?_,l.pie,?_⟩
 · rw [chime,chime,Z.move, trace_twist] -- tune

 · by_cases w:x∈safeZone p o
   · let i:Ids N:= Classical.arbitrary _
     let V:= K (x,i)
     have c:Cheap o (p.B/10) x p.threshold:=by
       intro j n
       refine (w j ?_).le
       have d:=p.B_pos
       exact Finset.not_disjoint_iff.mpr ⟨j.1,
         halo_spec.mpr ⟨o,Finset.mem_singleton_self _,n.trans (by omega)⟩,
         Work.E01.base_touched j⟩
     rw [chime,frameLit f h w i]
     have hh:=l.pk V x (stem_real f (x,i)).property (fun e l m=>(f.lamp o x i w e l m).symm) c
     exact (norm_le_norm_sub_add (story X V) (sketch X 0)).trans
       ((add_le_add hh a).trans_eq (add_comm ..))
   have c:0≤η:= (norm_nonneg _).trans a
   rw [chime,shine,Set.indicator_of_notMem w,Matrix.trace_zero,norm_zero]
   exact add_nonneg c (mul_nonneg U (sq_nonneg _))
 · apply Ink.within_mono l.pin
   intro i y
   have b:=separation_triangle 0 o i.1.1
   apply wet_iff.mpr
   have e:= wet_iff.mp y
   omega
 intro V x u m' c
 have w:V∈safeZone p o:= by
   intro i g
   exact c i (fun a=>g (Disjoint.mono_left ((lensBox_mono _ (show p.B≤p.B+4 by omega)).trans m) a))
 have x':=pinpoint t (show ‖x‖<2*r by linarith [t.1])

 have e:chime K p o X V=sketch X x:=by
    let i:Ids N:=Classical.arbitrary _
    rw [chime,frameLit f h w i]
    refine congrArg Matrix.trace (h.slip (stem_real f (V,i)) ⟨_,x'⟩ ?_)
    apply from_leaks
    exact fun j s t=>(f.lamp o V i w j s t).symm.trans (u j (m (downLit' s)) (m (downLit' t)))
 rw [e,show sketch X x-A.gilt (blush x)=sketch X 0+(sketch X x-sketch X 0-A.gilt (blush x)) by ring]
 exact (norm_add_le ..).trans (add_le_add a (l.pen x m'))

omit t
include l
-- Quadratic coefficient after masking directly on stream
lemma stanza {i:ℕ}(s:∀ u∈stains o (p.B/10),separation u.1.1 1≤ i)
 (q:4*i+1<N.val):
  Bud (chime K p o X ∘ petals (stream N)) ∧
  bud (chime K p o X ∘ petals (stream N)) 2=A.gilt (decree ∘ dot):=by
 have a:chime K p o X ∘ petals (stream N)
      =ᶠ[𝓝 0] maline (sketch X) 0 (hueD N):=by
   have g:petals (stream N) 0 ∈safeZone p o:=by
      rw [petal_idle]; intro i _
      simpa [faceValue,travel,square] using p.threshold_pos
   have e:∀ᶠ u in 𝓝 0, petals (stream N) u∈ safeZone p o:=
      (cont_petal (stream N)).continuousAt.eventually (ping_o.mem_nhds g)
   filter_upwards [e, petals_safe (stream N) f.pos] with u i j
   rw [Function.comp_apply,chime, litView f h i (fun _ _ _=>rfl) j, maline,zero_add,recreate]
 refine ⟨((l.pet (hueD N)).congr a).1,?_⟩
 rw [bud_congr a,(l.pet (hueD N)).bud_eq]
 exact Ink.same l.pin (fun i j=> baroque q i (s i j))
