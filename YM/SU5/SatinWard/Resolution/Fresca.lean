import YM.SU5.SatinWard.Resolution.CapsuleP
import YM.Lattice.Box
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
variable (D:Division) {P T:SOp N} (E:Pattern P T r d a v)
variable (q:BudgetPoint)(t:Scree.Loom N){k m:ℕ}{g:ℝ} (C:Checked q t g d a k m)
local notation "Z₁"=> Openc (More N) d
open Salt
open Laurent
abbrev disM (k:ℕ):Finset Cover:=Lattice.box (2*k)
noncomputable def powerM (k:ℕ):Finset SectorLayer:= (disM k)×ˢ(disM k)

lemma hour_cap (x:Cover)(b:Axis)(e:Lattice.lift (wrap N x)=x) (g: node (wrap N x) ∈ offsetMask q.B (wrap N 0)) : (x b).natAbs ≤ 2*q.B:=by
 obtain ⟨m,z,d⟩:=halo_spec.mp g; rw [mem_singleton.mp z] at d; apply le_trans (comp_size x b); apply Nat.cast_le (α:=ℝ)|>.mp; push_cast; exact (hour_note x e).trans (by gcongr)
include C
lemma on_erad (h:Axis)(i:SectorLayer)(V:Pane N) (p:‖(shrinkCoast N (onPay D E q t h 0 k V) i)‖ ≠ 0): i∈powerM q.B:=by
 have h' : (shrinkCoast N (onPay D E q t h 0 k V) i) ≠0:=by simpa using p
 by_cases t':shoreZ N i; swap; · exact False.elim (h' (if_neg t'))
 rw [shrinkCoast,if_pos t',onPay,zero_add,zero_add] at h'; let F:=centHat D (wrap N 0) E t q k (h,false) V; let g:= grantJ D E (wrap N 0,(h,false)); let X:= (_root_.Zephyr.Chern.tag N i.1); let Y:=(_root_.Zephyr.Chern.tag N i.2); have he:∃ u v,F (X u) (Y v) ≠ 0:=by by_contra! v; apply h'; ext u w; change _* F (X _) (Y _)=0; rw [v,mul_zero]
 have hz:moored (node (wrap N 0)) g:=E.moorJ (wrap N 0,(h,false)); obtain ⟨z,w,f⟩:=he; let u:=scope_cut (modes_pass _ g C hz (show Orbit N from (V,Classical.arbitrary _))) (X z) (Y w) f; have ht(x:Cover)(e:∀ i:Axis,(x i).natAbs ≤ 2*q.B): x∈disM q.B:= by
    apply Lattice.box_test.mpr; constructor<;> intro i<;>specialize e i<;> omega
 rw [powerM]; exact mem_product.mpr ⟨ht i.1 (fun j=>hour_cap q _ j t'.1 u.1), ht i.2 fun j=> hour_cap q _ j t'.2 u.2⟩
omit C
lemma power_wide (u:4*q.B < N.val)(z:Cover)(v:z∈disM q.B) : Lattice.lift (wrap N z)=z:=by
 apply lift_eq_iff.mpr; refine ⟨rfl, fun i=>?_⟩; obtain ⟨p,d⟩:=box_test.mp v; specialize p i; specialize d i; omega
include C in
lemma coastMemory (u:4*q.B<N.val)(i:Axis): momenti D E q t k i = Complex.I • lacquer (∑ x∈powerM q.B,onPay D E q t i 0 k 1 x):=by 
 unfold momenti; congr 2; rw [tsum_eq_sum (s:=powerM q.B)]; apply sum_congr rfl fun i hi=> if_pos ⟨power_wide q u i.1 (mem_product.mp hi).1,power_wide q u i.2 (mem_product.mp hi).2⟩; intro i g; apply Classical.not_not.mp; intro z; exact g (on_erad D E q t C _ i 1 (by simpa [vowBand] using z))
-- unit translation EXACT for ALL periods, even Pace.Shift for Ward use. required `spatial tests near circumference` interacts Moller.
include C
lemma centTrade(h:Axis)(x:Cover)(i:SectorLayer) : onPay D E q t h x k 1 i=onPay D E q t h 0 k 1 i:=by
 let W:=taxiPlus (wrap N x); let U:= grantJ D E (wrap N x,(h,false)); let v:Pane N:=1; let Y:= live t q k (wrap N x) U v; let z:= (h,false); let U':= grantJ D E (wrap N 0,(h,false))
 have p: centHat D (wrap N 0) E t q k (h,false) 1= ech W Y:=by
    have he:= cent_roll D (wrap N x) E C W v z; have ht:teamTravel W (wrap N x,z)= (wrap N 0,z):= by
         rw [teamTravel]; apply Prod.ext; · exact (shore_pose ..).trans (by rw [sub_self])
         exact shore_dir ..
    rw [ht,show flashA W v=v from bareRoom x,show pose W (wrap N x)=wrap N 0 from (shore_pose ..).trans (by rw [sub_self])] at he; change _=(if det_S W=true then star _ else _) at he; simp only [show det_S W=false from det_i,Bool.false_eq_true,if_false] at he; exact he
 unfold onPay; rw [p,zero_add,zero_add]; rw [shore_plus x]; rw [add_comm x i.1,add_comm x i.2]; rfl
end AuroraX
end YM.CF.LitCurrent
