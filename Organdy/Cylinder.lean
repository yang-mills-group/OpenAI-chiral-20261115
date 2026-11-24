import YM.SU5.Exchange.Stack.Manor
import YM.SU5.Interaction.Source.Reduction
import YM.CF.Buffered.Probes
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


variable {I:Type*} [Fintype I] [DecidableEq I]
abbrev motes (A:Op I):= ∑ i:I, ∑ j:I, ‖A i j‖
lemma motes_nonneg (A:Op I) : 0 ≤ motes A := by unfold motes; positivity
lemma motes_add (A B:Op I) : motes (A+B) ≤ motes A + motes B := by
 unfold motes; rw [←sum_add_distrib]; apply sum_le_sum; intro i _; rw [←sum_add_distrib]
 exact sum_le_sum fun j _=>norm_add_le _ _
lemma motes_sum {ι:Type*}(r:Finset ι)(f:ι→ Op I):motes (∑ i∈r,f i) ≤ ∑ i∈r,motes (f i):= by
 induction r using Finset.induction_on with
 |empty=> simp [motes]
 |insert i r h ih=> rw [sum_insert h,sum_insert h]; exact (motes_add _ _).trans (add_le_add le_rfl ih)

variable {N:Side}{X:SOp N}{a b d:ℝ}{o:Seat N}{k:ℕ}
local notation "D" => Openc (More N) d
local notation "Ω"=> Single N
lemma waves {S:Sa N}{c:Toll Ω}{F:Raw (Openc (More N) d) Ω}
  (h:Ticket (bail N d) (bail N d) S c F)(x:Openc (More N) d): motes (F x) ≤ ledgerV c:=
 sum_le_sum fun i _=>sum_le_sum fun j _=>(h.expo i j).bounded x


lemma soak_motes (h:Soak o X a b d) (v:0≤a)(x:Openc (More N) d): motes (X x.val) ≤ b := by
 obtain ⟨F,C,L,e,t,p⟩:=h
 rw [p x]; apply (motes_sum _ _).trans; exact (sum_le_sum fun i _=>
 ((waves (L i).toTicket x).trans (le_mul_of_one_le_left ((motes_nonneg _).trans (waves (L i).toTicket x)) (rent_one v i)))).trans t

abbrev lensBox {N:Side}(k:ℕ)(o:Seat N):= Lattice.halo k {o}
lemma lensBox_mono (o:Seat N){k l:ℕ}(h:k≤l):lensBox k o⊆ lensBox l o:=by
 intro i p; obtain ⟨j,v,u⟩:=halo_spec.mp p; exact halo_spec.mpr ⟨j,v,u.trans h⟩

variable {S:Support (More N)}
lemma from_leaks {U V:Pane N}(h:Agrees S U V) : fare S (profile U) (profile V)=0:=by
 unfold Tulip.fare
 refine sum_eq_zero fun i p=> ?_
 have T:= (mem_filter.mp p).2; rw [show profile U i=profile V i from funext fun d=>by unfold profile; rw [h i T.1 T.2],sub_self,norm_zero]

lemma fig_cut {I S:Support (More N)} {F:Raw (Openc (More N) d) Ω} {c:Toll Ω}
 (p:Ticket (bail N d) (bail N d) S c F) (v:c≠0 → S⊆ I) (x:D)
 : cutM (modesIn N I) * F x * cutM (modesIn N I) = F x := by
 ext i j; rw [cutM, Matrix.mul_diagonal,Matrix.diagonal_mul]

 by_cases h:c i j=0
 · have hv:= (p.expo i j).bounded x; rw [h] at hv
   rw [show F x i j=0 from norm_le_zero_iff.mp hv,mul_zero,zero_mul]
 have t:c≠0:= by rintro he; rw [he] at h; exact h rfl
 obtain ⟨_,hi,hj⟩:=(p.expo i j).triggered h
 rw [if_pos ((modes_at I i).mpr (v t hi)), if_pos ((modes_at I j).mpr (v t hj)), one_mul, mul_one]

structure Canal {N:Side}(I: Support (More N))(X:SOp N)(b d:ℝ): Prop where
  fluent : Continuous (fun x:Openc (More N) d => X x.val)
  swift (x:Openc (More N) d) : motes (X x.val) ≤ b
  wheel (x:Openc (More N) d)(g:Seat N→E):
    X (relayg g x.val)=twist (tradew N g) (X x.val)
  slip (x y:Openc (More N) d) (h:fare I x.val y.val=0): X x.val=X y.val
  mount (x:Openc (More N) d): cutM (modesIn N I)* X x.val*cutM (modesIn N I)=X x.val
lemma trunks_canal (h:Trunk o X k a b d)(p:0≤a):Canal (lensBox k o) X b d:=by
 let I:=lensBox k o
 obtain ⟨F,C,H,v,r,g⟩:= h.home
 have small (S:Sa N) (t:C S≠0):S⊆lensBox k o:=by
   obtain ⟨e,j⟩:=v S t; have u:=f_then (H S) t
   intro i l; exact halo_spec.mpr ⟨o,mem_singleton_self _, ((u.lim _ e _ l).trans j).le⟩

 refine ⟨?_,soak_motes h.pay p,fun x z=>?_,fun x y t=>?_,fun x=>?_⟩
 · rw [funext g]; exact continuous_finsetSum _ fun S _=>(H S).toTicket.cont
 · rw [g x, show X (relayg z x.val)=_ from g ((forum N d).drive z x), map_sum]
   exact sum_congr rfl fun S _=>(H S).frame.frame z x
 · rw [g x,g y]; apply sum_congr rfl; intro S _
   ext i j
   have ht:‖F S x i j-F S y i j‖≤ C S i j * (fare S x.val y.val / |d|):=((H S).expo i j).variation x y
   have hi:C S i j=0 ∨ fare S x.val y.val=0:=by
      by_cases b:C S=0; · left; rw [b]; rfl
      exact Or.inr (le_antisymm ((fare_inc (small S b) x.val y.val).trans_eq t) (fare_t ..))
   apply sub_eq_zero.mp; apply norm_le_zero_iff.mp; rcases hi with w | w <;> simpa only [w,zero_div,zero_mul,mul_zero] using ht
 · rw [g x,mul_sum,sum_mul]; exact sum_congr rfl fun S _=>fig_cut (H S).toTicket (small S) x

end YM.CF.Organdy
