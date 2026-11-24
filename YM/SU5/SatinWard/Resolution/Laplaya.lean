import YM.SU5.SatinWard.Resolution.PeacoatE
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 350000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical Kronecker
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "Γ" => Single N
open Buffered _root_.Zephyr.Chern
open IndexMag Chamber Surplus
namespace AuroraX
local notation "I"=> _root_.Zephyr.Chern.IS
open Laurent
open Ember Hove Lifted
variable (D:Division) {P T:SOp N} (E:Pattern P T r d a v)
variable (q:BudgetPoint)(t:Scree.Loom N){k m:ℕ}{g:ℝ} (C:Checked q t g d a k m)(H:4*q.B<N.val)
-- citizen array.G from receptor.Will.Layout.No boundary shift exceptions.
abbrev landSheet (B:ℕ):= {x:Cover // x∈ disM B}
abbrev shoreEntry (B:ℕ):= landSheet B × _root_.Zephyr.Chern.IS
noncomputable def saleLoc (N:Side)(x:Cover){B:ℕ}(i:shoreEntry B):Single N:= _root_.Zephyr.Chern.tag N (x+i.1.val) i.2
local notation "Φ" x:max=> saleLoc (B:=q.B) N x
variable (x:Cover)
include H
lemma sale_inj : Injective (saleLoc (B:=q.B) N x):= by
 rintro ⟨a,u,v⟩ ⟨b,y,z⟩ T'
 have he:wrap N (x+a.val)= wrap N (x+b.val)∧ (u:SpinIdx)=y∧v=z:=⟨congrArg (fun i:Single N=>i.1.1) T',congrArg (fun i:Single N=>i.1.2) T',congrArg Prod.snd T'⟩
 have hv: a.val=b.val:= (power_wide q H _ a.property).symm.trans ((congrArg Lattice.lift (?_ : wrap N a.val=wrap N b.val)).trans (power_wide q H _ b.property)); swap; · apply add_left_cancel (a:=wrap N x); rw [←map_add, ←map_add]; exact he.1
 rw [show a=b from Subtype.ext hv,he.2.1,he.2.2]
def canvasB := (univ:Finset (shoreEntry q.B)).image (saleLoc N x)
local notation "Θ"=> canvasB (N:=N) q x -- N implicit? H not in def
omit H
lemma power_entry (i:Single N)(p:node i.1.1 ∈ offsetMask q.B (wrap N x)) : i∈ canvasB (N:=N) q x :=by
 let a:= Lattice.lift (i.1.1-wrap N x); have hp :wrap N (x+a)=i.1.1:=by rw [map_add,show wrap N a=i.1.1-wrap N x from wrap_lift ..]; abel
 have he: Lattice.lift (wrap N a)= a:= by conv_lhs=> rw [show wrap N a=i.1.1-wrap N x from wrap_lift ..]; -- tactic align
 have ht: node (wrap N a)∈ offsetMask q.B (wrap N 0):=by
    obtain ⟨w,m,z⟩:=halo_spec.mp p; rw [mem_singleton.mp m, ←hp] at z; apply halo_spec.mpr; refine ⟨_,mem_singleton_self _,?_⟩; rw [show separation (node (wrap N 0)) (node ((wrap N) a))= separation (node (wrap N x)) (node (wrap N (x+a))) from ?_]; exact z; rw [Hove.ζdist, Hove.ζdist, map_zero,map_add, separation,separation]; congr 1; congr 1; abel
 have hh:a∈disM q.B:=by have hv(k:Axis):= hour_cap q a k he ht; refine box_test.mpr ⟨fun i=>?_,fun i=>?_⟩ <;> (specialize hv i; omega)
 rw [canvasB]; refine mem_image.mpr ⟨(⟨a,hh⟩, (i.1.2,i.2)),mem_univ _,?_⟩; change ((wrap N (x+a),i.1.2),i.2)=i; rw [hp]
-- Power covariance for any Mark with restricted endpoints, not only density.B.C.
variable (A:Op (Single N)) (w:cutM (modesIn N (offsetMask q.B (wrap N x))) * A * cutM (modesIn N (offsetMask q.B (wrap N x)))=A)
include w H
lemma standardLayout {M:Type*} [AddCommMonoid M](F:Γ→Γ→ M)(p: ∀ i j, A i j=0→ F i j=0) : ∑ i:Γ,∑ j:Γ,F i j= ∑ i:shoreEntry q.B,∑ j:shoreEntry q.B,F ((saleLoc N x) i) ((saleLoc N x) j):=by
 let φ:=saleLoc (B:=q.B) N x; let X:=Θ; have he(i j:Γ)(u:A i j≠0):i∈X∧ j∈ X:= by let v:= scope_cut w i j u; exact ⟨power_entry q x i v.1,power_entry q x j v.2⟩
 have hh(F:Γ→ M) : ∑ i∈X,F i=∑ i:shoreEntry q.B,F (φ i):= by unfold X φ canvasB; rw [Finset.sum_image]; exact fun _ _ _ _ s=> sale_inj q H x s -- `unfold X φ` maybe φ not present at LHS.Meta
 rw [show (∑ i:Γ,∑ j:Γ,F i j)=∑ i∈X,∑ j:Γ,F i j from ?_, hh]; swap; · refine (sum_subset (subset_univ _) (fun i _ v=>sum_eq_zero fun j _=> ?_)).symm; exact p _ _ (Classical.not_not.mp fun l=> v (he i j l).1)
 apply sum_congr rfl fun i _=> ?_; rw [←hh]; exact (sum_subset (subset_univ _) (fun j _ v=>p _ _ (Classical.not_not.mp fun l=>v (he (φ i) j l).2))).symm -- rw phi spelling tune
#print axioms standardLayout
end AuroraX
end YM.CF.LitCurrent
