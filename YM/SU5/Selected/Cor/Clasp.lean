import YM.SU5.Selected.Cor.Stamps
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
namespace Mezz
set_option synthInstance.maxSize 24000
attribute [local instance] opCStarAlgebra
open Lifted (nodeC node_of)
open Payroll Tender
variable (A:Mezz) {T:Type}[Fintype T][DecidableEq T](P:Society T)
variable (N:Side)
local notation "U"=> park N A.OuterPos
local notation "Q"=> park N A.Broad
local notation "T₀"=> park N A.Core
structure Caste {N:Side}(M:Tulip.Male)(C ε:ℝ)(w:ℕ)(X Z: Coast→ Wq A.marks): Prop where
  value : A.Legate
  enoughW: w≤ A.W
  enoughN:10*A.beams < N.val
  billR: TideFrame (G:=A.G) A.n A.marks X Z A.D w ε ε C
  billF: Payroll (1-Crest.Airy.tip N M) (hire A.marks X (A.detent N)) (hire A.marks Z (A.detent N)) C C ε ε
  spinA: spar 4 M (1: Pane N)=(Crest.Airy.tip N M)⊗ₖ (1:Op SU.Slot)
  -- from `$V.U` given actual elect at P.d
  spinC: IsStarProjection (spar 4 M (1:Pane N))
  spinD: ∀ (a:Axis)(i:Bool), twist (carR a 0 N) (sp i 4 M (1:Pane N))=sp (!i) 4 M (1:Pane N)

variable {N}{M:Tulip.Male}{C ε:ℝ}{w:ℕ}{X Z:Coast → Wq A.marks}(p: A.Caste (N:=N) M C ε w X Z)
local notation "V" => cutM (Tset N)
local notation "L" => A.dart P N X
local notation "H" => A.dart P N Z
local notation "R₀" => (Ro N)
local notation "F" => (1-sp false 4 M (1: Pane N)) -- universe
local notation "d" b:max => hand b (cutM (Tset N))
local notation "ω" => Complex.I
namespace Caste
include p
lemma volume_pay: Payroll (F) L H C C ε ε:=by
 let G:=1-Crest.Airy.tip N M; have U': F=G⊗ₖ(1:Op SU.Slot):=by rw [show sp false 4 M (1:Pane N)=_ from p.spinA]; unfold G; rw [warp_sub, Matrix.one_kronecker_one]
 rw [U']; exact (p.billF.twill (1-Crest.Airy.tip N M) _ _ _ _ _ _ SU.Slot).inspect _ _ _ _ _ _ _ _ (A.seat_cast P) -- order
lemma volume_leg : Commute F (R₀).val:=by
 have h: twist (R₀) F= F:=by rw [Ro,one_twist,map_sub,map_one,p.spinD,map_sub,map_one,p.spinD,Bool.not_not]
 change F * _=_; exact (congrArg (fun W: Op (Single N)=> W * (R₀).val) h.symm).trans (twist_product (R₀) F)
private lemma trip_lock {S: Finset Cover}{a:Axis}(u:S⊆ A.Core): (S.image (plane 1 0).motion).image (plane 0 0).motion ⊆ A.Core:=by
 have h0:=A.Outer_spin 0 (by decide); have h1:=A.Outer_spin 1 (by decide); rw [← h0] -- `← h1` inside
 exact image_subset_image ((h1) ▸ image_subset_image u)
omit p in
private lemma modes_split {S T:Finset (Seat N)}(h:Disjoint S T) : Disjoint (modesIn N S) (modesIn N T):= disjoint_left.mpr (fun x u v=> disjoint_left.mp h ((modes_at ..).1 u) ((modes_at ..).1 v))
lemma tri_splits {a b: A.Fish P N}(p':Contained (modesIn N U) a)(q:Contained (modesIn N U) b) : aᴴ * ((R₀).val* b)=0 ∧ ((R₀).val* a)ᴴ*b=0:= by
 let g := A.OuterPos; let v:= (g.image (plane 1 0).motion).image (plane 0 0).motion
 have hv:2*A.vol< (More N).val:=by have h:=p.enoughN; unfold beams at h; unfold vol; change _<N.val*2; omega
 have hp:Disjoint (modesIn N U) (modesIn N (park N v)):= modes_split (land_apart _ _ hv A.Outer_room (trip_lock (a:=0) A p A.Outer_room) A.Outer_dis)
 exact ⟨p'.other (sparkleT q Ro_trip) hp,(sparkleT p' Ro_trip).other q hp.symm⟩
def tollS (C:ℝ):=100*C
def lowerP (C:ℝ):= (tollS C)⁻¹
def upperP (C:ℝ):= (tollS C)/2
lemma sememes (t:C≥1) : Payroll F (Payroll.design (R₀) L (lowerP C)) (Payroll.design (R₀) H (upperP C)) (2*C/(tollS C)) (C*tollS C) ε (ε*tollS C):= by
 obtain ⟨c,dL⟩:= tri_splits A P p (dart_x A P N _ _ p.billR p.enoughW) (dart_z A P N _ _ p.billR p.enoughW)
 exact Payroll.designed _ _ _ _ _ _ _ (volume_pay A P p) (R₀) (volume_leg A p) c dL (show 0<tollS C by unfold tollS; linarith) -- tune syntax named p then positional

-- basic pillar. 
lemma spans_L : Contained (modesIn N (T₀)) (L):= (dart_x A P N _ _ p.billR p.enoughW).grows (modes_monotone (image_subset_image A.Outer_room))
lemma spans_H: Contained (modesIn N (T₀)) (H):= (dart_z A P N _ _ p.billR p.enoughW).grows (modes_monotone (image_subset_image A.Outer_room))
lemma spans_ro (A':A.Fish P N) (h:Contained (modesIn N (T₀)) A')(u:ℝ): Contained (modesIn N (T₀)) (design (R₀) A' u):= by
 have hv:= sparkleT h (Ro_clasp (A.Outer_spin 0 (by decide)) (A.Outer_spin 1 (by decide))); rw [design,sub_eq_add_neg, ← neg_smul]; exact (h.add (hv.smul (-ω))).smul _
lemma skates : d true * L = L:= by change (1-cutM (Tset N):Op _)*L=L; rw [←dim_cut]; exact dart_pitch A P N _ _ p.billR p.enoughW
variable (i:A.Lot)(b:Bool)
-- use orientation X. restricted supports $P.Zuma variant definition clamp
local notation "X₀" => A.cork P N i b L
local notation "Z₀" => A.cork P N i b H
local notation "Y₀" => park N (A.yard i.1 true)
local notation "Y'₀" => park N (A.yard i.1 false)
-- anchor Bool patch charge. real plane cost et.
lemma rooted_x : Contained (modesIn N (park N (A.clan i.1 true b))) (X₀) := by
 apply (containedP ..).mpr; rintro ⟨⟨x,j⟩,q⟩ u t; by_contra v; obtain ⟨b',o,y,g⟩:= A.cork_pos P N i b _ _ p.billR p.enoughW v
 apply u; apply (modes_at ..).2; dsimp only; rw [g]; refine mem_image_of_mem _ ?_; have h':=(A.Zumba_left i.1 true _ o p.value); have e:=(h'.trans (by rw [eq_self,true_and])).trans y.symm -- y : b=true ↔ atom; need (λ → Prop notation) orientation
 cases b; exact mem_sdiff.mpr ⟨o,fun i=>Bool.noConfusion (e.mp i)⟩; exact mem_inter.mpr ⟨o,e.mpr rfl⟩
#print clan
lemma stage_x : Contained (modesIn N (Y₀)) (X₀):= by
 have hv:A.clan i.1 true b⊆ A.yard i.1 true:= by cases b; exact sdiff_subset; exact inter_subset_left
 exact (rooted_x A P p i b).grows (modes_monotone (image_subset_image hv))
lemma stage_v : Contained (modesIn N (Y'₀)) ( (d false)* Z₀):= by
 apply (containedP ..).mpr; rintro ⟨⟨x,j⟩,q⟩ u t; change (cutM (Tset N)* Z₀) _ t= _; rw [cutM, Matrix.diagonal_mul]; split_ifs with e
 · rw [one_mul]; by_contra v; obtain ⟨b',o,y,g⟩:=A.cork_minus P N i b _ _ p.billR p.enoughW ((Window.mem_Tset ..).1 e) v; exact u ((modes_at ..).2 (show node x ∈_ from g.symm ▸ (mem_image_of_mem _ o))) -- tune
 rw [zero_mul]
end Caste
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz.Caste
#print axioms sememes
#print axioms stage_v
#print axioms stage_x
