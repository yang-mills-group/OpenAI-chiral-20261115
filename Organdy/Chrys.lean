import Organdy.Larva
import Organdy.Almond
import Zephyr.Chern.Garden
import YM.Next.STATIONARY.Joint.OnShell
import YM.CF.Thera.Jolt
import YM.CF.Support.Hit
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.CF.Organdy.Larva
open Filter Topology Metric Lattice Exterior Precision 
open Tulip Branch Cube Lat Tenant Drapes _root_.Zephyr.Chern

open scoped Matrix.Norms.L2Operator Matrix
attribute [local instance] opCStarAlgebra
local notation "G" => SU.group
variable {N m:Side}{d r:ℝ}

abbrev Tiny (d:ℝ)(U:Wilson.Config SU.group m):=profile U∈Openc m d
lemma pinpoint (t:Spool d r){x:Dir m}(v:‖x‖ < 2*r):
 Tiny d (represent x):=by
 have e:=t.2 x (0:Dir m) ((0:ℝ):ℂ) v (by have p:=t.1;rw [norm_zero,mul_zero];linarith)
 rw [play,zero_smul,add_zero] at e;exact e

variable {S:Band N}{P:Oil N}{C:Toll (Single N)}

abbrev story (P:Oil N)(U:Wilson.Config SU.group (More N)) :ℂ:= (P (profile U)).trace
abbrev sketch (P:Oil N) (x:Dir (More N)):ℂ:= story P (represent x)

variable (h:Piece d S C P)
include h
lemma fiction (t:Spool d r):
 Almond r (ledgerV C) (sketch P):=by
 have E:=ledgerT h.toTicket
 refine ⟨t.1, E.1,?_,?_⟩

 · have e:ContinuousOn (fun x:Chin N=>(P x).trace) (Openc _ d):=
      continuousOn_iff_continuous_restrict.mpr E.continuousE
   exact e.comp realCont.continuousOn (fun x hx=>pinpoint t ((mem_ball_zero_iff.mp hx).trans_le (by rw [two_mul])))
 intro x y ex ey
 have a:=t.1
 have b(z:ℂ)(v:‖z‖< 3*(r/‖y‖)):spun x y z∈Openc _ d:=by
    apply t.2 _ _ _ ((by linarith):‖x‖ < 2*r)
    rw [←mul_div_assoc, lt_div_iff₀ (norm_pos_iff.mpr ey)] at v;linarith
 refine ⟨fun z=>(P (spun x y z)).trace,?_,fun z v=>E.norms ⟨_,b z v⟩,fun u _=>congrArg (fun x=>(P x).trace) (play ..)⟩
 classical
 let V:=ball (0:ℂ) (3*(r/‖y‖))
 let w:=fun z=> if f:z∈V then
    (⟨_,b z (mem_ball_zero_iff.mp f)⟩:Openc (More N) d) else
    ⟨_,pinpoint t (show ‖x‖ < 2*r by linarith)⟩
 have e:∀ u∈V, (w u).val=spun x y u:=fun u f=>by simp [w,f]
 rw [show (fun z => (P (spun x y z)).trace)=∑ i:Single N,fun z=>P (spun x y z) i i by
       funext z; rw [Finset.sum_apply];rfl]
 apply DifferentiableOn.sum
 intro i _
 exact (h.fuel i i V isOpen_ball w
    ((knit x y).differentiableOn.congr e)).congr (fun u v=>congrArg (fun f=> P f i i) (e u v).symm)

variable {U V:Wilson.Config SU.group (More N)}
lemma literal (u:Tiny d U)(v:Tiny d V)(f:∀e∈leaks S, U e=V e) : story P U = story P V:=by
 have e:fare S (profile U) (profile V)=0:=Finset.sum_eq_zero fun i m=>by
    have g:profile U i=profile V i:=funext fun z=>by simp [profile,f i m]
    rw [g, sub_self,norm_zero]
 have a:=(ledgerT h.toTicket).varies ⟨_,u⟩ ⟨_,v⟩
 change ‖story P U-story P V‖ ≤ _*(fare S (profile U) (profile V)/|d|) at a
 simpa [e, norm_le_zero_iff, sub_eq_zero] using a
lemma tone (u:Tiny d U)(g:Site (More N)→SU.E):
   story P (gauge g U) = story P U:=by
 rw [story, profile_g]
 exact (ledgerT h.toTicket).gauge g ⟨_,u⟩
lemma reword (u:Tiny d U)(v:Tiny d V)(g:Site (More N)→SU.E)
   (f:∀e∈leaks S, gauge g U e=V e): story P U=story P V :=
 (tone h u g).symm.trans (literal h (by rw [Tiny,profile_g];exact o_act _ _ _ u) v f)

omit h
def plaise (g:SU.E)(y:Dir m):Dir m:=fun i=>SU.group.adjoint g (y i)
lemma solid (g:SU.E)(y:Dir m):
 represent (plaise g y)=gauge (fun _=>g) (represent y):=by
 funext e
 simp only [represent,RG.increment, Lattice.gauge,Pi.one_apply,mul_one]
 apply SU.group.mat_injective

 rw [SU.group.mat_mul,SU.group.mat_mul,SU.group.mat_inv,SU.group.mat_lieExp,SU.group.mat_lieExp]
 rw [show collect SU.group (plaise g y) e=SU.group.adjoint g (collect SU.group y e) from rfl,
     SU.group.mat_adjoint,SU.group.exp_conjugate];rfl

include h
lemma faint (t:Spool d r)(x:Dir (More N)):
 bean1 (sketch P) 0 x=0:=by
 obtain ⟨L,p⟩:=(fiction h t).honey.lean_paid
 rw [p x]
 refine Stationary.slot_fixed Thera.yet_one L.toContinuousLinearMap ?_ x
 intro g y
 change L (plaise g y)=L y
 rw [←p,←p,bean1,bean1]
 apply congrFun (bud_congr ?_)
 have u:∀ᶠ u in 𝓝 (0:ℝ), ‖u•y‖ < 2*r :=
   ((continuous_id'.smul continuous_const).norm.continuousAt (x:=0)|>.tendsto.eventually
     (gt_mem_nhds (show ‖(0:ℝ)•y‖<2*r from by simpa using mul_pos (by norm_num:0<(2:ℝ)) t.1)))
 filter_upwards [u] with u v
 unfold maline sketch
 rw [zero_add,zero_add,show u• plaise g y=plaise g (u•y) by funext i;exact (map_smul (SU.group.adjoint g) u (y i)).symm, solid]
 exact tone h (pinpoint t v) _

abbrev poem (P:Oil N)(x:Dir (More N)) := bean2 (sketch P) 0 x
omit h in private lemma rec_eq (f:ℝ→ℂ): ![f 0,bud f 1,bud f 2]=bud f:= by unfold bud;rfl
lemma bloom_paid(t:Spool d r)(x:Dir (More N)):
 Bloom (maline (sketch P) 0 x) ![(sketch P) 0,0,poem P x]:=by
 have p:=((fiction h t).mixer 0 x (by simpa using t.1)).1.bloom
 have e: ![(sketch P) 0,0,poem P x]=bud (maline (sketch P) 0 x) := by
    rw [←rec_eq]
    have a: maline (sketch P) 0 x 0=sketch P 0:=by simp [maline]
    rw [a, show bud (maline (sketch P) 0 x) 1=0 from faint h t x]
 rw [e];exact p

lemma poem_bend (t:Spool d r): ∃ Q: Dir (More N)→ₗ[ℝ]Dir (More N)→ₗ[ℝ]ℂ,
      (∀x,poem P x=Q x x)∧∀ x y,Q x y=Q y x:=(fiction h t).honey.bend_paid

lemma phrase_le (t:Spool d r)(x:Dir (More N)):
 ‖poem P x‖ ≤ sweets r * ledgerV C * ‖x‖^2 :=
   (fiction h t).honey.bend x

lemma rhyme (t:Spool d r){x:Dir (More N)}(u:‖x‖ < r):
 ‖sketch P x - sketch P 0 - poem P x‖ ≤
      sweets r * ledgerV C * ‖x‖^3:= by
 have e:=(fiction h t).honey.coat 0 x 1 (by simpa using t.1) (by simpa using u)
 simpa [skewer, faint h t x, sub_sub] using e

lemma ryme (t:Spool d r){x:Dir (More N)}(u:‖x‖<r):
 ‖sketch P x-sketch P 0‖ ≤
      sweets r * ledgerV C * (1+r) * ‖x‖^2:=by
 refine (norm_le_norm_sub_add _ (poem P x)).trans
    ((add_le_add (rhyme h t u) (phrase_le h t x)).trans ?_)
 rw [show sweets r*ledgerV C*‖x‖^3+sweets r*ledgerV C*‖x‖^2
    =sweets r*ledgerV C*(1+‖x‖)*‖x‖^2 by ring]
 gcongr
 exact (fiction h t).honey.plus
