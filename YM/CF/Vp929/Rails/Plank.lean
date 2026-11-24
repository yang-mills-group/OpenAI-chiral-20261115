import YM.CF.Vp929.Analysis.ExpTransfer
import YM.CF.Hake.Song
import YM.CF.Hake.Ply
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Hake
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo
open Jet
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{f g:E→ℂ}{x:E}{k:ℕ}{a:ℝ}
variable {C B V:ℝ}{ι J n:Type}[LinearOrder n][Fintype n]
variable {F G:E→FC n}{c d:Raid n}
lemma Pence.mono (h:Pence k f x C)(g:C≤B): Pence k f x B:=⟨h.smooth,h.earned.trans g⟩
lemma Woody.mono (h:Woody k F x c)(e:c≤d): Woody k F x d:=⟨h.own,fun i=>(h.haveP i).mono (e i)⟩
lemma Woody.smulP (h:Woody k F x c)(u:ℂ):Woody k (u•F) x (‖u‖ • c):=by
 refine ⟨?_,fun i=>(h.haveP i).σ u⟩; exact h.own.mono fun z p=> spanS p u
lemma Woody.close {I:Type*}{Λ:I→Raid n}{s:Filter I}[s.NeBot](u:Tendsto Λ s (𝓝 c))(v:∀ᶠ i in s,Woody k F x (Λ i)): Woody k F x c:=by
 let p:=v.exists.choose_spec; refine ⟨p.own,fun j=>⟨(p.haveP j).smooth,ge_of_tendsto ?_ (v.mono fun i h=>(h.haveP j).earned)⟩⟩; exact tendsto_pi_nhds.mp u j
open VolumeRate
variable {N m:ℕ}{z:ℂ} {b w:ℝ}
local notation "z@" => ((b:ℂ)+z*w)
local notation "θ" i => ((wooden N b w i:ℝ):ℂ)
variable {U:E→ℂ→ℂ} {Cₚ:ℝ} (L:Appears N Cₚ)(hC:0<Cₚ) (hz:‖z‖≤2) (v:2^(k+2)*m≤N)
include L hC hz v
lemma Pence.panelP{T:ℕ→ℝ}(P:∀ x,Pencilled m (U x)) (H:∀ i∈VolumeRate.panel N,Pence k (fun x=> U x (θ i)) x (T i)): Pence k (fun x=> U x z@) x (Cₚ*∑ i∈VolumeRate.panel N,T i):= by
 obtain ⟨W,G⟩:= Pencilled.transfer L hz hC k v P (fun i p=> (H i p).smooth); refine ⟨W,le_trans ?_ (mul_le_mul_of_nonneg_left (sum_le_sum fun i e=>(H i e).earned) hC.le) ⟩
 unfold potash; rw [sum_comm (s:= VolumeRate.panel N),mul_sum]; apply sum_le_sum; intro j p; simp_rw [noble,← mul_sum]; rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (G _ (Nat.le_of_lt_succ (mem_range.mp p))) (by positivity)
lemma Woody.panelP{W:E→ℂ→FC n}{T:ℕ→Raid n} (P:∀ x,Pencilled m (W x))(H:∀ i∈VolumeRate.panel N,Woody k (fun x=> W x (θ i)) x (T i)): Woody k (fun x=> W x z@) x (Cₚ • ∑ i∈VolumeRate.panel N,T i) := by
 classical
 refine ⟨?_,fun i=>?_ ⟩
 · filter_upwards [eventually_all.mpr (fun i:VolumeRate.panel N=> (H i i.prop).own)] with x t; obtain ⟨_,_,G⟩:= ((P x).mono ((Nat.le_mul_of_pos_left _ (pow_pos (by decide : (0:ℕ)<2) _)).trans v)).span (c:=b) (w:=w) L hz; rw [G]; exact snack fun i h=> spanS (t ⟨i,h⟩) _
 rw [Pi.smul_apply,Finset.sum_apply]; exact Pence.panelP L hC hz v (fun x=> (P x).map ({toFun:= fun x=> crumb x i,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}:FC n→ₗ[ℂ]ℂ)) (fun j p=>(H _ p).haveP i)

variable {W:E→ℂ→ FC n}{T: VolumeRate.panel N → Raid n} {g₀:E→ FC n}{g': VolumeRate.panel N→ E→ FC n} (cT:VolumeRate.panel N→ℂ)(c0:ℂ)
lemma twigP (P:∀ x,Pencilled m (W x))(hp:∀ i:VolumeRate.panel N,(fun x=> W x (θ i))= cT i • g' i)(ht:g₀=c0 • (fun x=> W x z@))(hg:∀ i:VolumeRate.panel N, Woody k (g' i) x (T i))(u:ℝ)(hv:∀ i:VolumeRate.panel N,‖c0‖*‖cT i‖≤u): Woody k g₀ x ((u*Cₚ) • ∑ i,T i):= by
 classical
 let T'(i:ℕ):= if h:i∈VolumeRate.panel N then ‖cT ⟨i,h⟩‖ • T ⟨i,h⟩ else 0
 have V: ∀ i∈VolumeRate.panel N,Woody k (fun x=>W x (θ i)) x (T' i):=by intro i h; unfold T'; rw [dif_pos h,hp ⟨i,h⟩]; exact (hg _).smulP _
 rw [ht]; refine ((Woody.panelP L hC hz v P V).smulP _).mono ?_; rw [←Finset.sum_coe_sort (VolumeRate.panel N) T',smul_smul,smul_sum,smul_sum]; apply sum_le_sum; intro i _; unfold T'; rw [dif_pos i.prop,smul_smul,mul_right_comm]; exact smul_le_smul_of_nonneg_right (mul_le_mul_of_nonneg_right (hv i) hC.le) (hg i).p
end YM.CF.Hake
