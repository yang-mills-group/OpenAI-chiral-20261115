import YM.SU5.FiniteGaugeData.Lycan.Duke
import YM.SU5.FiniteGaugeData.Lycan.Bird
/-! # Actual on-site currents. window of chirality. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Stationary Mir Royal
namespace Venice
-- all choices. all axes arcs.
variable {ι:Type*} {X Y₀ Z:Window.Component}{p q x: Cover}{N:Side}
abbrev Oval(z:Cover)(C:Window.Component):Grit:= {σ:=C.fam, launch:=z,landing:=z,line:= [],activate:=by rfl,u:=C.up,d:=C.down,up:=C.hu,dn:=C.hd}
abbrev coupleK (A:Window.Component)(x:Cover)(K: Calibration): W K:=bookFee K (Oval x A)
lemma locale (K:Calibration): Locator K (coupleK X x K) {(nodeC x)}:=by
 let A:= (ProbeCode.Country K (Oval x X)).place; rw [show ({nodeC x}: Finset Cover)=(Oval x X).town by simp [Chisel.town,Lattice.visits]]; exact A
lemma present(V:Pane N): ProbeCode.score (Oval x X) N V= Window.current N X.fam (wrap N x) X.up X.down V:=by
 let A:= Oval x X; let D:= A.buyD N V; have he:D=A.buyD N 1:=rfl; -- travel all U
 have hp:D=Window.jOp N X.fam (wrap N x) X.up X.down:=by
   ext ⟨a,i⟩ ⟨b,j⟩; rw [he,A.at_off,Window.jOp_entry]; unfold A Oval; dsimp only; congr 1; unfold Chisel.shiftSign; simp only [Lifted.winding]; rw [fee_real,fee_one] -- tune congr
 exact congrArg dg hp
variable {F:ℕ→ι→ Cover}{z:ι→Gaia}{r:ℕ→ℝ}
-- charge.IN. include SI coordinates strict equiv. Composition to A for all points.
structure Run (r:ℕ→ℝ)(F:ℕ→ι→ Cover)(z:ι→Gaia):Prop where
 basisE:∀ i:ℕ,0<r i
 comes:Tendsto r atTop atTop
 seekingE:∀ a:ι,Tendsto (fun i=>riseX (r i) (F i a)) atTop (𝓝 (z a))
 wins:∀ a b:ι,z a=z b → ∀ᶠ i in atTop,F i a=F i b
abbrev Focal:= ι × Window.Component
local notation "Α"=> Focal (ι:=ι)
abbrev OvO (F:ℕ→ι→ Cover) (i:ℕ)(a:Α):= Oval (F i a.1) a.2
abbrev sigA(a:Α):=a.2.fam
abbrev hiA(a:Α):=a.2.up
abbrev loA(a:Α):=a.2.down
abbrev pulseA(f:ι→Gaia)(a b:Α):= f b.1-f a.1
abbrev forte (x:ι→Gaia)(X: List (Α)):= absoluteP sigA hiA loA (pulseA x) X
variable (ω:Run r F z)
include ω in
lemma stoneC: GlobeP (OvO F) r sigA hiA loA (pulseA z):= by
 refine ⟨ω.basisE,ω.comes,fun _ _=> ⟨rfl,rfl,rfl⟩,fun a b=> ?_,fun a b t=> (ω.wins b.1 a.1 (sub_eq_zero.mp t)).mono fun n p=>p⟩; let V:= Tendsto.sub (ω.seekingE b.1) (ω.seekingE a.1); exact V.congr' (Eventually.of_forall fun i=>by dsimp only; exact Emu.face_z ..)
-- color shape (incl i,j with same z: returns 0 too, not continuous as y→x if y≠x).
local notation "Υ"=>Α×SU.Slot
abbrev melody(f:ι→Gaia)(a b:Α):= Onyx.pencil (pulseA f a b) (loA b) (hiA a)
private lemma melody_ϕ (z:ι→Gaia) : specter hiA loA (pulseA z)=violet (melody z):=rfl
private lemma nilF(a:Α)(z:ι→Gaia): melody z a a=0:=by simp [melody,pulseA,Onyx.pencil]
section
variable (σ:Window.Family){p q r':ι}
lemma forte_1 (a:Α):forte z [a]=0:=by unfold forte absoluteP; rw [melody_ϕ,cost_1 _ _ _ (Q:=lint sigA a) rfl,nilF,mul_zero]
private lemma τ_cost (H:Υ→Υ→ℂ)(y z w:Υ)(p:H y y=0)(q:H z z=0)(r:H w w=0): Album H [(y,y),(z,z),(w,w)]= H y z*H z w*H w y+H y w*H z y*H w z:=by
 rw [spindle,p,zero_mul]; simp only [slid, smul_eq_mul, twos,q,r]; ring
private lemma γ_cost (c:Α→Α→ℂ)(a b d:Α)(p:c a a=0)(q:c b b=0)(t:c d d=0) (i j k:SU.Slot): let H:=violet c (D:=SU.Slot); let G:= ((a,i):Υ); let W:= ((b,j):Υ); let P:= ((d,k):Υ); Album H [(G,G),(W,W),(P,P)]= if i=j ∧ j=k then c a b*c b d*c d a+c a d*c b a*c d b else 0:=by
 intro H G W P; rw [τ_cost H _ _ _]; swap; · simp [G,H,violet,p]; -- maybe subgoals swapped order
 by_cases e:i=j; · subst j; by_cases u:i=k <;> simp [H,G,W,P,violet,u, eq_comm] -- tune `Ne.symm` dangerous
 by_cases u:j=k; · subst k; simp [H,G,W,P,violet,e,eq_comm]
 simp [H,G,W,P,violet,u,e,eq_comm]; all_goals simp_all [H,W,P,violet]
lemma forte_3 (u: Y₀.fam=X.fam)(v: Z.fam=X.fam)(a b d:ι): forte z [(a,X),(b,Y₀),(d,Z)]= (dimf X.fam:ℂ)* Window.sixM (z a) (z b) (z d) X Y₀ Z :=by
 let A:Α:= (a,X); let B:Α:= (b,Y₀); let C:Α:= (d,Z); let kappa:= melody z; let U:= Window.colors X.fam
 let K' := kappa A B*kappa B C*kappa C A+kappa A C*kappa B A*kappa C B; have he:K'= Window.sixM (z a) (z b) (z d) X Y₀ Z:=by unfold K' kappa melody; unfold Window.sixM; unfold loA hiA pulseA A B C; dsimp only; ring
 unfold forte absoluteP; rw [melody_ϕ]; change Conv _ (violet kappa) [A,B,C]=_; unfold Conv; rw [Silk]; simp_rw [Silk]; have ha: lint sigA A=U:=rfl; have hb:lint sigA B=U:= congrArg Window.colors u; have hc:lint sigA C=U:= congrArg Window.colors v; rw [←he]; simp_rw [show ∀ i j k:SU.Slot, Album (violet kappa) [(((A,i):Υ),(A,i)), (((B,j):Υ),(B,j)), (((C,k):Υ),(C,k))]=_ from fun i j k=>γ_cost kappa A B C (nilF A z) (nilF B z) (nilF C z) i j k,ha,hb,hc]; change (∑ i∈U,∑ j∈U,∑ k∈U, (if i=j ∧ j=k then K' else 0))=_; rw [←colors_card]; let Φ(i j k:SU.Slot):= if i=j∧j=k then K' else 0; -- reduce
 have ht(i)(p:i∈ U): ∑ j∈U,∑ k∈ U,Φ i j k= K':=by
   rw [sum_eq_single_of_mem i p]; · simp [Φ,p]
   intro v _ t; simp [Φ,Ne.symm t]
 rw [sum_congr rfl ht,sum_const,nsmul_eq_mul]
end
#print axioms forte_3
end Venice
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
