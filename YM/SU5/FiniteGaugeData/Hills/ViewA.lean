import YM.SU5.FiniteGaugeData.Hills.Rooms
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)
namespace Hills
open Nacre Heat Charm Chrono Journey SalonG Terrace
variable (a j:Axis)(d n:ℕ)
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}{P:Call Λ l}{J:Wicket Λ l}
variable (W':Universal Y h u v I E)(R:Rolled Y h u v J P)
variable (A:Repertory Y h W' R a)
local notation "T"=> StructureH Y h a W' R A
abbrev Camera : Hilbert:= CoreH ((StructureH Y h a W' R A).Unity)
local notation "U"=> (StructureH Y h a W' R A).Unity
local notation "D"=> dip (U)
local notation "P'"=>planeP (U)
local notation "U'"=> cpo (U)
local notation "C"=> Camera Y h a W' R A
local notation "W1"=> W (tent Y h)
local notation "E'" f:max=> E s ((f:W (tent Y h)).val)
variable {x y:W (tent Y h)} (f:Plan Y h a d x)(A':A.space.Op)(e:0<d)
include A
section coins
variable (z:ℤ)(x₀:Camera Y h a W' R A)
lemma photo_cast (p:Allows a j z): tock Y h s W' R a j A z p ((U') x₀)=(U') x₀:= DFunLike.congr_fun ((T).dip_left s j z p) x₀
lemma photo_absorbs (p:Allows a j z)(x:A.space): (D) (tock Y h s W' R a j A z p x)=D x:= DFunLike.congr_fun ((T).dip_step s j z p) x
lemma socialP (p:Allows a j z): social (U) (A'* tock Y h s W' R a j A z p)=social (U) A':=by ext1 u; change (D) (A' _)= (D) (A' _); congr 2; exact photo_cast Y h _ a j W' R A z u p
lemma socialR (p:Allows a j z): social (U) (tock Y h s W' R a j A z p * A')=social (U) A':= ContinuousLinearMap.ext fun v=> photo_absorbs .. -- order/inference
abbrev billC (e:0<d): (Camera Y h a W' R A).Op:= social (U) (Wedge Y h s a d W' R A f e)
include f e
lemma pad_fixed (t:d≤ n)(p:Plan Y h a n x): billC Y h s a d W' R A f e=billC Y h s a n W' R A p (e.trans_le t) :=by
 obtain ⟨m,rfl⟩:= Nat.exists_eq_add_of_le t; unfold billC; rw [wicket_pad Y h s a d (d+m) x W' R A f e rfl (e.trans_le t) p, socialP]
lemma absWick (p:Plan Y h a n x)(w:0<n) : billC Y h s a d W' R A f e=billC Y h s a n W' R A p w:=by
 let m:=d+n; let r:=plan_larger Y h a d m x (by unfold m; omega) f; exact (pad_fixed Y h s a d m W' R A f e (by unfold m; omega) r).trans (pad_fixed Y h s a n m W' R A p w (by unfold m; omega) r).symm
lemma bill_eq (p:Plan Y h a d y)(w:x=y): billC Y h s a d W' R A f e=billC Y h s a d W' R A p e:= by subst y; rfl
lemma repeat_nat (i:ℕ)(p:Plan Y h a n (clockW Kₜ a i x))(r:0<n): billC Y h s a d W' R A f e=billC Y h s a n W' R A p r:=by
 let z:=plan_steps Y h a d x f (i:ℤ) (by positivity) (show (d:ℤ)+i≤ ↑(i+d) from by omega)
 have hx:billC Y h s a d W' R A f e=billC Y h s a (i+d) W' R A z (by omega):=by unfold billC; rw [wicket_adv Y h s a d (i+d) x W' R A f e i rfl z,socialR]
 exact hx.trans (absWick Y h s a (i+d) n W' R A z (by omega) p r)
lemma repeat_int (i:ℤ)(p:Plan Y h a n (clockW Kₜ a i x))(r:0<n): billC Y h s a d W' R A f e=billC Y h s a n W' R A p r:=by
 rcases le_total 0 i with v|v
 · obtain ⟨j,rfl⟩:= Int.eq_ofNat_of_zero_le v; exact repeat_nat Y h s a d n W' R A f e j p r
 let j:=(-i).toNat; have hx: (j:ℤ)+i=0:=by unfold j; omega
 let y:=clockW Kₜ a i x; have he:x=clockW Kₜ a j y:=by unfold y; rw [clock_add,hx,tic_zero]
 let z:Plan Y h a d (clockW Kₜ a j y):= Eq.mp (congrArg (Plan Y h a d) he) f
 exact (bill_eq Y h s a d W' R A f e z he).trans (repeat_nat Y h s a n d W' R A p r j z e).symm -- orientation if j=0; t≤
end coins
end Hills
end YM.CF.Buffered.Afterglow.Hierarchy
