import YM.SU5.SatinWard.Resolution.StrobeE
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
variable (D:Division) (κ:ℝ)
variable {P T:SOp N}(E:Pattern P T r d a v)(y:Site N)
local notation "Z₁"=>Openc (More N) d
open Salt
open Laurent
-- $expiry ∆*∥forest∥. applies all € menus with Room_s.S
lemma leeAge (z:SOp N)(s:Single N)(j:Single N)(w:Z₁) {o:Seat N}(h:Soak o z a κ d)(u:0 < a) : ‖z w.val s j‖ ≤ κ *Real.exp (-(a/2)* ((separation o (node s.1.1):ℝ)+(separation o (node j.1.1):ℝ))):=by
 obtain ⟨F,V,p,c,q,r⟩:= h; let x:ℝ:= (separation o (node s.1.1):ℝ)+(separation o (node j.1.1):ℝ); let y:= Real.exp (-(a/2)*x); have hy:0≤ y:=(Real.exp_pos _).le
 have hz(S:Sa N):0 ≤ ledgerV (V S):=sum_nonneg (fun i _=>sum_nonneg (fun j _=>(p _).nonn i j)); rw [r w,Matrix.sum_apply]; refine (norm_sum_le ..).trans ((sum_le_sum (?_:∀ S∈univ, ‖F S w s j‖≤ (rent a S* ledgerV (V S))*y)).trans ?_); swap; · rw [←sum_mul]; exact mul_le_mul_of_nonneg_right q hy
 intro S _; let t:=(p S).expo s j; apply t.bounded w|>.trans; by_cases z: V S s j=0; · rw [z]; exact (mul_nonneg (mul_nonneg (rent_pos ..).le (hz _)) hy)
 have ho:o∈S:=by by_contra h; apply z; rw [c _ h]; rfl
 let ⟨U,b,X⟩:=t.triggered z -- let syntax?
 have he:1 ≤ rent a S*y:=by unfold Branch.rent y; rw [←Real.exp_add]; apply Real.one_le_exp; unfold x; have v₁:separation o (node s.1.1) < S.card:=U.lim _ ho _ b; have p₂:separation o (node j.1.1)< S.card:= U.lim _ ho _ X; linarith only [mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ)|>.mpr v₁.le) u.le,mul_le_mul_of_nonneg_left (Nat.cast_le (α:=ℝ)|>.mpr p₂.le) u.le]
 rw [mul_right_comm]; exact le_trans (le_trans (single_le_sum (fun i _=>(p S).nonn s i) (mem_univ j)) (show _ ≤ ledgerV (V S) from single_le_sum (fun i _=>sum_nonneg (fun j _=> (p S).nonn i j)) (mem_univ s))) (le_mul_of_one_le_left (hz _) he)
lemma needle_cap {ι:Type}[Fintype ι][DecidableEq ι](X:Op ι)(t:∀ i j:ι,‖X i j‖ ≤ κ) : ‖X‖ ≤ (∑ i:ι,∑ j:ι, ‖(Matrix.single i j (1:ℂ))‖)*κ:=by
 nth_rw 1 [show X=∑ i:ι,∑ j:ι,X i j • (Matrix.single i j (1:ℂ)) from ?_]; refine (norm_sum_le ..).trans ?_; simp_rw [sum_mul]; refine sum_le_sum (fun i _=>(norm_sum_le ..).trans (sum_le_sum (fun j _=>?_))); swap -- holes order? inspect
 · ext i j; simp [Matrix.sum_apply,Matrix.single,ite_and, mul_ite]
 rw [norm_smul,mul_comm]; exact mul_le_mul_of_nonneg_left (t ..) (norm_nonneg _)
lemma hour_note (x: Cover)(v:Lattice.lift (wrap N x)=x): (size x:ℝ) ≤ 2*(separation (node (wrap N 0)) (node (wrap N x)):ℝ):=by
 let V:= under_node x v; rw [node_wrap,separation, add_sub_cancel_right,smul_neg,map_neg,pdist_neg] at V; rw [separation_comm,node_wrap,node_wrap]; simp only [smul_zero,map_zero,zero_add,separation, add_sub_cancel_right]; exact_mod_cast V -- 1 variable vs zero
local notation "ΨN"=> shore N
local notation "W₀" => ∑ i:I,∑ j:I, ‖(Matrix.single i j (1:ℂ))‖
abbrev expNote(a:ℝ)(x y:Cover): ℝ:=Real.exp (-a/4*((size x:ℝ)+(size y:ℝ)))
def faithMoney(a:ℝ):ℝ:= (∑ i:I,∑ j:I, ‖(Matrix.single i j (1:ℂ))‖)*a
lemma holds_money (e:0≤κ):0≤ faithMoney κ:=mul_nonneg (sum_nonneg (fun i _=>sum_nonneg (fun j _=> norm_nonneg _))) e
lemma faith_scale (v:ℝ): faithMoney (v*κ) = v*faithMoney κ:=by unfold faithMoney; ring
lemma minuteAge (x y:Cover)(f:Lattice.lift (wrap N x)=x)(g:Lattice.lift (wrap N y)=y) (h:Soak (node (wrap N 0)) P a κ d)(p:0<a) (w:Z₁): ‖shore N x y (P w.val)‖≤ (faithMoney κ)*expNote a x y:=by
 have hs:0≤κ:=soakCostNN h; rw [faithMoney,mul_assoc]; apply needle_cap; intro i j; let t:= leeAge κ P (_root_.Zephyr.Chern.tag N x i) (_root_.Zephyr.Chern.tag N y j) w h p; unfold expNote; change ‖(flag N x*flag N y)*_‖≤ _; rw [norm_mul,norm_mul,flag_norm,flag_norm,one_mul,one_mul]; apply t.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone _) hs); change -(a/2)*((_ :ℝ) + (separation (node (wrap N 0)) (node (wrap N y)):ℝ))≤ _; change -(a/2)*((separation (node (wrap N 0)) (node (wrap N x)):ℝ)+_)≤ _; linarith only [mul_le_mul_of_nonneg_left (hour_note x f) p.le, mul_le_mul_of_nonneg_left (hour_note y g) p.le]
#print axioms minuteAge
end AuroraX
end YM.CF.LitCurrent
