import Organdy.Snug
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Organdy
open Function Filter Topology Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel
open Swell StressExchange Buffered
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra


variable {N:Side}
local notation "Ω"=>Single N
/-- Enough to apply to real physical plates: t is Loom threshold (possibly larger than
ping threshold); d the Canal qualification (possibly larger than Loom's). -/
structure StageSet (K:Scree.Loom N) (p:BudgetPoint) (d:ℝ):Prop where
 pos: 0<d
 lamps:∃ t e:ℝ, ∃ q:ℕ, Roof N t e q K∧p.threshold≤t∧e≤d∧p.B/10+q≤p.B

lemma touchFour(i:Face (Per N)){x y}(u:x∈ touched i)(t:y∈ touched i):separation x y≤4:=
 (separation_triangle x i.1 y).trans (Nat.add_le_add ((separation_comm ..).trans_le (Work.E01.sep_touched i x u)) (Work.E01.sep_touched i y t))

variable {K:Scree.Loom N}{d a b:ℝ}{p:BudgetPoint}
local notation "C" => lensBox (p.B/10)
local notation "P" => lensBox p.B
abbrev foot (p:BudgetPoint) (o:Seat N):=lensBox (p.B+4) o
abbrev safeZone (p:BudgetPoint) (o:Seat N): Set (Pane N):={u|pingS p.threshold (lensBox p.B o) u}

def shine (K:Scree.Loom N)(p:BudgetPoint)(o:Seat N)(X:SOp N):Pane N → Op Ω :=
 (safeZone p o).indicator fun V=> X (profile (K (V,Classical.arbitrary (Ids N))))

variable {o:Seat N}{U V:Pane N}{X:SOp N}
lemma safeed (w:Agrees (foot p o) U V): U∈safeZone p o ↔ V∈ safeZone p o:=by

 have h(i)(g:¬ Disjoint (lensBox p.B o) (touched i)):faceValue U i=faceValue V i:=by
    obtain ⟨x,t,u⟩:= Finset.not_disjoint_iff.mp g
    obtain ⟨z,e,a⟩:=halo_spec.mp t
    exact WilsonStartup.face_local i U V (agrees_mono w (fun y v=>halo_spec.mpr ⟨z,e,(separation_triangle z x y).trans (Nat.add_le_add a (touchFour i u v))⟩))
 exact ⟨fun r i t=> h i t ▸ r i t,fun r i t=>(h i t).symm ▸ r i t⟩
variable (v:StageSet K p d)
lemma downLit {q:ℕ} (y:q≤ p.B/10) : lensBox q o ⊆ foot p o:= lensBox_mono o (y.trans ((Nat.div_le_self ..).trans (Nat.le_add_right ..)))
lemma downLit' : lensBox (p.B/10) o ⊆ foot p o:=downLit le_rfl

structure WindowDress (K:Scree.Loom N)(p:BudgetPoint) (d:ℝ):Prop where
 pos: 0<d
 bill:Measurable K
 paid(U:Orbit N):Guard (K U) d
 rev(V:Pane N)(t:Ids N)(g:Seat N→ E):
    K (Lattice.gauge g V, threadG g t)=Lattice.gauge g (K (V,t))
 lamp(o:Seat N)(U:Pane N)(t:Ids N): U∈safeZone p o → Agrees (lensBox (p.B/10) o) U (K (U,t))
include v
lemma dressing : WindowDress K p d:=by
 obtain ⟨t,e,q,f,r,w,u⟩:=v.lamps
 refine ⟨v.pos,f.bill,fun i=> Guard.shrink (f.paid i) w, f.rev,?_⟩

 intro o U T h i l m
 have x:win q i⊆ lensBox p.B o:=by
    intro j k; obtain ⟨y,v,b⟩:=halo_spec.mp k
    have S:ends i⊆lensBox (p.B/10) o:= insert_subset_iff.mpr ⟨l,singleton_subset_iff.mpr m⟩
    obtain ⟨z,r,c⟩:=halo_spec.mp (S v)
    exact halo_spec.mpr ⟨z,r,(separation_triangle _ y _).trans ((Nat.add_le_add c b).trans u)⟩
 have pU:pingS t (lensBox p.B o) U:=fun j w=>(h j w).trans_le r
 exact (f.lamp U T i (Disjoint.mono_right x (ping_le pU).symm)).symm
omit v

variable (f:WindowDress K p d)

abbrev beam_real (v:0<d)(U:Pane N)(g:Guard U d): Openc (More N) d:=⟨profile U,U,g,by simpa⟩
abbrev stem_real (z:Orbit N): Openc (More N) d:= beam_real f.pos _ (f.paid z)
lemma stemM (t:Ids N) : Measurable fun V:Pane N=> stem_real f (V,t) :=
 (profile_c.measurable.comp (f.bill.comp (measurable_id.prodMk measurable_const))).subtype_mk

structure Slat (I:Support (More N))(A:Pane N→Op Ω)(b:ℝ):Prop where
 bright:Measurable A
 quick(U:Pane N):motes (A U) ≤ b
 local_:Lattice.LocalOn I A
 move(g:Seat N→E)(U:Pane N): A (Lattice.gauge g U)= twist (tradew N g) (A U)
 core(U:Pane N) : cutM (modesIn N I)*A U *cutM (modesIn N I)= A U

variable (h:Canal (lensBox (p.B/10) o) X b d)


lemma cutCover {I:Type*} [Fintype I] [DecidableEq I] {s t:Finset I}{X:Op I} (x:cutM s*X*cutM s=X)(v:s⊆t): cutM t*X*cutM t=X:=by
 rw [← x]
 ext i j; simp only [cutM, Matrix.mul_diagonal, Matrix.diagonal_mul]
 by_cases hi:i∈s <;> by_cases hj:j∈s <;> simp [hi,hj]; simp [v hi,v hj]
include h f

lemma litView {U V:Pane N}(w:U∈safeZone p o)(hp:Agrees (lensBox (p.B/10) o) U V)
    (t:Guard V d):shine K p o X U=X (profile V):=by
 rw [shine,Set.indicator_of_mem w]
 let z:Orbit N:=(U,Classical.arbitrary _)
 apply h.slip (stem_real f z) (beam_real f.pos _ t)
 exact from_leaks (fun i a b=> (f.lamp o U z.2 w i a b).symm.trans (hp i a b))

lemma frameLit (w:U∈safeZone p o)(T:Ids N):shine K p o X U=X (profile (K (U,T))):=
 litView f h w (f.lamp o U T w) (f.paid _)

lemma slatLit: Slat (foot p o) (shine K p o X) b:=by
 let t:Ids N:= Classical.arbitrary (Ids N)
 let z(U:Pane N):=stem_real f (U,t)
 have u:Measurable (fun V=> X (z V).val):=h.fluent.measurable.comp (stemM f t)
 refine ⟨u.indicator (ping_o.measurableSet),fun U=>?_,fun U V r=>?_,fun g U=>?_,fun U=>?_⟩

 · by_cases w:U∈safeZone p o; rw [frameLit f h w t]; exact h.swift (z U)
   rw [shine, Set.indicator_of_notMem w]; have g:0≤b:=(motes_nonneg _).trans (h.swift (z U)); simpa [motes]
 · have k:=safeed r
   by_cases w:U∈safeZone p o
   · rw [frameLit f h (k.mp w) t]
     exact litView f h w (fun i a b=> (r i (downLit' a) (downLit' b)).trans (f.lamp o V t (k.mp w) i a b)) (f.paid _)
   rw [shine,Set.indicator_of_notMem w,Set.indicator_of_notMem (mt k.mpr w)]
 · have k:(Lattice.gauge g U)∈safeZone p o↔U∈safeZone p o:=pingB _ _
   by_cases w:U∈ safeZone p o
   · rw [frameLit f h (k.mpr w) (threadG g t), f.rev, profile_g,frameLit f h w t]; exact h.wheel (z U) g
   rw [shine,Set.indicator_of_notMem w,Set.indicator_of_notMem (mt k.mp w), map_zero]
 · by_cases w:U∈ safeZone p o
   · rw [frameLit f h w t]; exact cutCover (h.mount (z U)) (modes_monotone downLit')
   rw [shine, Set.indicator_of_notMem w, mul_zero, zero_mul]

end YM.CF.Organdy
