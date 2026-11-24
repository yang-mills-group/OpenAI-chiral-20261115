import YM.SU5.FiniteGaugeData.CodaT.Pep
import YM.SU5.FiniteGaugeData.CodaT.Niagara
import YM.SU5.FiniteGaugeData.Mirage.Sheet
import YM.CF.Fir.Grove
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
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
open YM.SU5.FiniteGaugeData.CodaT Eight
/-! # Authorized source for Leaning program. -/
open Fock.Reduction.Drama.Pack Fock.Relief YM.SU5.FiniteGaugeData.Cuprite.Spirit
variable {N M:Side}{S:Finset Cover}{T U:Finset (Site N)}{K:Calibration}{W':W K}{c r s t ε ν H:ℝ}{G Q:Op (Single N)}{n m k d w:ℕ}
-- matching natural currencies for any wired bilinear (WP18). Does not need aligning at planar origins. We construct explicitly so basis signs checked on tiny wrapped endpoints, to read moving slope for this family stencil. Here `Spin10`/`δ5` each paid, upper/lower. Common law on gauge. -/
namespace Niagara
variable {x y a b:Cover}{u v:SpinIdx}
open Largo Mirage -- placeholder
open Dial -- tickA
variable (M':Tulip.Male)(N:Side)
local notation "R"=> reedsK M' N
local notation "ψ" => spar 4 M' (1:Pane N)
local notation "X0"=> tickA N
local notation "Q₀"=> cutM (ruddy N)
abbrev hubK(N:Side)(P:Male):= (1+reedsK P N)*cutM (ruddy N)
abbrev main (M:Male)(N:Side): Op (Single N):= (hubK N M) ⊗ₖ (1:Op SU.Slot)
open Cascade
private lemma π0 : tickA N= (cutM (ruddy N)) ⊗ₖ (1:Op SU.Slot):=by
 rw [touchP]; ext ⟨a,i⟩ ⟨b,j⟩; by_cases h:a=b<;> by_cases p:i=j; subst b j; simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one, cutM,Matrix.diagonal_apply_eq]; simp_rw [show (a,i)∈Tset N ↔ _ from grade_one ..]; simp [ruddy]
 all_goals simp [cutM,h,p,Matrix.kroneckerMap_apply,Matrix.one_apply,Matrix.diagonal_apply]
private lemma zeroTick : cutM (ruddy N)= E₁ (fun _=> Aop) N:=by
 unfold E₁; rw [pilesV]; ext ⟨x,i⟩ ⟨y,j⟩; rw [jump_apply, Adef,← raising]; by_cases h:x=y <;> by_cases p:i=j <;> by_cases t:i∈plusHalf <;> simp_all [ruddy,cutM,Matrix.diagonal_apply,h,t]
private lemma θy: flatH M' N * hubK N M'=hubK N M':=by
 rw [hubK,zeroTick]; unfold flatH reedsK E₁; rw [←piles1 (N:=N), pilesA,pilesP,pilesP]; apply pilesE; intro p u e; have hp:= Fir.lead true 4 M'.val M'.2 u e; rw [sub_eq_add_neg] at hp; exact hp
private lemma assignK : Q₀* hubK N M'= Q₀ := by
 rw [hubK,add_mul,one_mul,mul_add,(cutM_idp (ruddy N)).1, ←mul_assoc,reeds_s,mul_assoc,(show cutM (scel N)*cutM (ruddy N)=0 from cutP_com (ruddy N) (ruddy N) le_rfl),mul_zero,add_zero]
variable (h:Standing (tickA N) (spar 4 M' (1:Pane N)))
include h
lemma pinF : oblique X0 ψ=main M' N:=by
 let U:=main M' N; let J:= oblique X0 ψ; have hx:X0*U=X0:=by rw [π0]; unfold U main; rw [op_kron_mul,assignK,one_mul]
 have hu:ψ*U=U:=by unfold U main spar; rw [profile_trivial,fFlat,op_kron_mul,θy,one_mul]
 have p:J*U=U:=by nth_rw 1 [←hu]; rw [←mul_assoc,TuneC.up h.luxury,hu]
 change J=U; nth_rw 1 [←p]; rw [← show J * X0=J from h.luxury.stem] -- dangerous all J; tune
 rw [mul_assoc,hx]
omit h
namespace Chisel
variable (X:Chisel)
local notation "Λ"=> X.launch
local notation "f"=> X.landing -- syntax local notation hash fn collisions e f names below
local notation "A"=> X.upCard N
local notation "B"=> X.downCard N
local notation "W" => X.buyD N 1
local notation "μ" => Window.colors X.σ
local notation "G"=> reedsK M' N B A
private lemma mainEntry (p q:SU.Slot): main M' N (B,p) (A,q)= if p=q then G else 0:=by
 unfold main hubK; rw [Matrix.kroneckerMap_apply]; change (((1+R)*Q₀) _ _) *_=_; rw [Largo.compass',if_pos (mem_product.mpr ⟨mem_univ _,X.up⟩),Matrix.add_apply,Matrix.one_apply_ne (X.unequal N)]; by_cases h:p=q; rw [Matrix.one_apply,h]; simp; rw [Matrix.one_apply_ne h]; simp [h] -- notation B Arc
lemma at_off (a b: Mini N)(p q:SU.Slot): X.buyD N 1 (a,p) (b,q)= if a=A∧ b=B∧ p∈colors X.σ∧ p=q then X.shiftSign N else 0:=by unfold buyD surfN; rw [Matrix.smul_apply, X.run_o, internal,map_one]; change _ • (if a=A∧b=B then (cutM μ*1 *cutM μ) p q else 0)=_; rw [mul_one, (cutM_idp μ).1]; by_cases h:a=A<;>by_cases h':b=B<;>by_cases u:p∈ μ<;>by_cases q':p=q<;>simp_all [cutM,Matrix.diagonal_apply] -- tune f
lemma sumCost (V:Standing (tickA N) (spar 4 M' (1:Pane N))) : Relief.cup X0 ψ W=(Window.dimf X.σ:ℂ)* X.shiftSign N*G:=by
 unfold Relief.cup; rw [pinF M' N V]; let K:=main M' N; let L:=X.shiftSign N; let U:= X.buyD N 1; unfold Matrix.trace; change (∑ i:Single N, (K*U) i i)=_
 have hp(a:Mini N)(i:SU.Slot) : (K*U) (a,i) (a,i)= if a=B∧i∈ μ then L*G else 0:=by
    rw [Matrix.mul_apply,sum_eq_single (A,i)]; rw [show U _ _ = _ from at_off N X _ _ _ _]; by_cases p:a=B∧ i∈ μ; rw [if_pos ⟨rfl,p.1,p.2,rfl⟩,if_pos p,p.1]; rw [show K _ _=_ from mainEntry M' N X i i, if_pos rfl]; unfold L; ring
    rw [if_neg ?_,if_neg p,mul_zero]; exact fun h=>p ⟨h.2.1,h.2.2.1⟩; -- tune
    intro b _ h; rcases b with ⟨k,j⟩; rw [show U (k,j) _=_ from at_off N X _ _ _ _,if_neg (fun g=> h (Prod.ext g.1 g.2.2.2)),mul_zero]; simp
 rw [show ∑ i:Single N, (K*U) i i= _ from Fintype.sum_prod_type (fun x: Mini N×SU.Slot=> (K*U) x x)]; simp_rw [hp]; rw [sum_eq_single B]; simp only [true_and]; rw [←sum_filter,(show univ.filter (fun i:SU.Slot=>i∈ μ)=μ from (by ext; simp)),sum_const,nsmul_eq_mul,colors_card]; change ↑(dimf X.σ)*(X.shiftSign N*G)=_; simp only [shiftSign,mul_assoc]
 intro b _ h; simp only [h,false_and,ite_false,sum_const_zero]; simp
-- wave assembly
private lemma rentX(y:Cover)(x:Site N): frequency x (wrap N y) * Lifted.winding N y= Laurent.mode (mel x) y:=by
 rw [←freq_mode]; unfold Lifted.winding; rw [← mode_fee, ←mode_shift,Rush.carrying]
abbrev slotWeight (X:Chisel):ℝ:= (dimf X.σ:ℝ)
def angleK (X:Chisel)(U F: Momentum):ℂ:= Laurent.mode U (X.landing-X.launch)*(-zen F) X.d X.u
abbrev μWallet X M(z:Momentum):= angleK X z (mixL 4 M z)
lemma modeCost : X.shiftSign N*G = ∑ i: Site N, (((N.val:ℝ)^4:ℝ):ℂ)⁻¹ * μWallet X M'.val (mel i):=by
 unfold reedsK E₁; rw [upCard, downCard,Rush.price,mul_sum]; apply sum_congr rfl; intro i _; unfold μWallet angleK; -- wrong order
 let x:=mel i; let h:=Lifted.winding N; let k:=h f; let p:=h Λ; let e:=frequency i; let a:=e (wrap N Λ); let b:=e (wrap N f)
 let U:= (-zen (mixL 4 M'.val x)) X.d X.u; let P:= Laurent.mode x
 have he:P (f-Λ)=b*k*(star (a*p)):=by
    have hv:=mode_adjoint x Λ; rw [show star x=x from (mel_h _).1] at hv; unfold P; rw [sub_eq_add_neg, mode_shift, ←hv,←rentX,←rentX]
 have hn:=Lat.normF_ne N; let Wq:=Lat.normF N
 change (p*star k)*((b/Wq)*U*star (a/Wq))=_*(P _*U); rw [he,star_mul,star_div₀,show star p=p from fee_real _,show star k=k from fee_real _,show star Wq=Wq by simp [Wq,Lat.normF]]; rw [show (((N.val:ℝ)^4:ℝ):ℂ)=Wq*Wq from (by unfold Wq Lat.normF; push_cast; ring)]; change Wq≠0 at hn; field_simp
end Chisel
end Niagara
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
