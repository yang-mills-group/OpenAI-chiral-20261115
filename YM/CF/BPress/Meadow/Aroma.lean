import YM.CF.BPress.Meadow.Halo
/- X Mark operator seed from coordinates in $V_\pm$. frame follows, even off-data. local version. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Meadow
open Function Filter Finset NormedSpace Metric SU SU.Pair Mesa Fock Lattice Cube Lat Spin Dial Grid Grid.Entity Delivery Lute.Kite MeasureTheory RG Net Tent Sheet
open scoped Topology BigOperators NNReal Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace Classical
attribute [local instance] opCStarAlgebra
variable {s:Side}{T: Sheet.Atlas}{L y C C':ℝ}{b:ℕ}(W:Tunnel s)(F:Net s T L y C C' b) (U: Micro s)(p : Duo s) (k:Tiling s)
lemma shuffle_seq(a b:Mach s)(P:marks s): shuffle a (shuffle b P)= shuffle (a*b) P:=funext fun i=> (scaled_s ..).symm
lemma shuffle_one(P:marks s):shuffle 1 P=P:=funext fun i=> scaled_one _
lemma shuffle_curve {X:Type*}[MeasurableSpace X] {a:X→Mach s}{p:X→marks s}(g:Measurable a)(h:Measurable p): Measurable fun i=> shuffle (a i) (p i):= by apply measurable_pi_lambda; intro i; exact scaled_meas.comp (f:=fun j:X=>(a j i,p j i)) (((measurable_pi_apply i).comp g).prodMk ((measurable_pi_apply i).comp h))
lemma urgent_morph {T:Support s}{U V:Micro s}{P Q:marks s}{K:ℝ}(p:Alert U T P K)(M:Mach s) (h:gauge M U=V)(u:Set.EqOn (shuffle M P) Q T): Alert V T Q K:=by rintro i t; rw [←h]; have ht:= inside_iff ..|>.mp t; rw [show urgent (gauge M U) i Q=urgent (gauge M U) i (shuffle M P) from ?_,urgent_s _ _ _ M]; exact p i t; unfold urgent; rw [←u ht.1,←u ht.2]
namespace Frame
open Tunnel
abbrev headS(s:Side) :marks s:=fun _=> Seed
def headM := shuffle (haloM W p)⁻¹ (headS s)
def ψ := atlasG F W (W.reads U) p
-- in axial coordinates watching $W$
def tea := tree k W.mem (cloak W W.lips) (gauge (ψ W F U p) (W.orient U)) (shuffle (ψ W F U p) (headM W p))
def ferns (x:Site s): Sprout:= if x∈cloak W (body W) then headM W p x else shuffle (ψ W F U p)⁻¹ (tea W F U p k) x
def sprigs:=shuffle (W.axial U)⁻¹ (ferns W F U p k)
lemma ψ_meas : Measurable (fun x:Micro s × Duo s=> ψ W F x.1 x.2):=by
 apply W.book_cont.measurable.comp (f:=fun x:Micro s × Duo s=> F.deck W (W.reads x.1) x.2); apply measurable_pi_lambda; intro i; exact (F.deck_meas W i).comp (f:=fun x: Micro s × Duo s=> (W.reads x.1,x.2)) ((W.reads_cont.measurable.comp measurable_fst).prodMk measurable_snd)
@[fun_prop] lemma head_meas : Measurable (headM W):= shuffle_curve (halo_meas W).inv measurable_const
@[fun_prop] lemma ferns_m : Measurable (fun x : Micro s× Duo s=>ferns W F x.1 x.2 k):=by
 have ht:Measurable (fun x : Micro s× Duo s=> tea W F x.1 x.2 k):=(tree_m k ..).comp (f:=fun x :Micro s × Duo s=> (gauge (ψ W F x.1 x.2) (W.orient x.1),shuffle (ψ W F x.1 x.2) (headM W x.2))) ((gauge_joint.measurable.comp ((ψ_meas ..).prodMk (W.orient_cont.measurable.comp measurable_fst))).prodMk (shuffle_curve (ψ_meas ..) ((head_meas W).comp measurable_snd))) -- tune
 apply measurable_pi_lambda; intro i; unfold ferns; split; exact (measurable_pi_apply _).comp ((head_meas W).comp measurable_snd); exact (measurable_pi_apply _).comp (shuffle_curve (ψ_meas ..).inv ht) -- tune
lemma sprigs_m : Measurable (fun x:Micro s × Duo s=> sprigs W F x.1 x.2 k):= shuffle_curve (W.axial_cont.measurable.inv.comp measurable_fst) (ferns_m W F k)
local notation "R"=>ψ W F U p
local notation "A"=>W.orient U
local notation "χ"=> (W.axial U) -- not Lute
-- gauges. equality full ferns under branch (branch identity outside W) but $U$ reads beyond allowed? cropping solves
lemma gauge_tea (a:Mach s): tea W F (gauge a U) (p*(W.framesE a)⁻¹) k=tea W F U p k:=by
 unfold tea ψ headM; rw [gauge_halo, gauge_universe]; refine tree_identical k _ _ _ _ _ _ _ _ rfl rfl ?_ ?_; intro x v; have he: Set.EqOn (R*(W.branchM a)⁻¹* (W.axial (gauge a U))*a) (R*χ) W.mem:=by
    intro i p; have ht:= W.overlap U a p; simp only [Pi.mul_apply] at *; simp only [Pi.inv_apply]; rw [mul_assoc,mul_assoc,ht,inv_mul_cancel_left]
 rw [orient,gauge_trans,gauge_trans,orient,gauge_trans]; let Q:= R*(W.branchM a)⁻¹* (W.axial (gauge a U))*a; change Q x.1* U x*(Q (endAt x))⁻¹=(R*χ) x.1*_ *((R*χ) (endAt x))⁻¹; rw [show Q x.1= _ from he ((inside_iff ..).mp v|>.1), show Q (endAt x)= _ from he ((inside_iff ..).mp v|>.2)]

 have hx:R*(W.branchM a)⁻¹*(haloM W p*(W.branchM a)⁻¹)⁻¹=R*(haloM W p)⁻¹:=by group
 unfold ψ at hx; rw [shuffle_seq, shuffle_seq,hx]; exact fun _ _=>rfl
lemma gauge_fern(a:Mach s) : ferns W F (gauge a U) (p*(W.framesE a)⁻¹) k= shuffle (W.branchM a) (ferns W F U p k):=by
 funext x; unfold ferns shuffle; dsimp only; split; next f=> -- simp both branches
    unfold headM shuffle; rw [gauge_halo,mul_inv_rev,inv_inv, ←scaled_s]; rfl
 unfold ψ; rw [gauge_universe,gauge_tea,mul_inv_rev,inv_inv]; exact scaled_s ..
lemma gauge_sprigs(a:Mach s) : Set.EqOn (sprigs W F (gauge a U) (p*(W.framesE a)⁻¹) k) (shuffle a (sprigs W F U p k)) W.mem:=by
 unfold sprigs; rw [gauge_fern,shuffle_seq,shuffle_seq]; intro i h; have ht:=W.overlap U a h; let X:= W.axial (gauge a U); let V:=W.branchM a
 unfold shuffle; simp only [Pi.mul_apply,Pi.inv_apply]; have he:X i * a i=V i*χ i:=ht; apply (show _ from congrArg (fun v=> scaledV v (ferns W F U p k i)) ?_); change (X i)⁻¹*V i=a i*_ ; rw [show V i=X i*a i*(χ i)⁻¹ from (by rw [he]; group)] ; group -- tune

lemma fern_local(V:Micro s)(h:Lattice.Agrees W.mem U V): ferns W F U p k=ferns W F V p k:=by
 have he:= W.reads_local U V h; have ht:ψ W F U p=ψ W F V p:=by rw [ψ,ψ,he]
 have hx: tea W F U p k=tea W F V p k:=by
    unfold tea; rw [ht]; refine tree_identical k _ _ _ _ _ _ _ _ rfl rfl (fun i t=>?_) (fun _ _=>rfl); unfold Lattice.gauge; rw [W.orient_local U h i ((inside_iff ..).mp t).1 ((inside_iff ..).mp t).2]
 unfold ferns; rw [ht,hx]
lemma sprig_local(V:Micro s)(h:Lattice.Agrees W.mem U V): sprigs W F U p k=sprigs W F V p k:=by
 let X:= W.axial; have hx:= W.axial_only U (show Set.EqOn U V W.stores from fun i t=> h _ ((inside_iff ..).mp (W.stores_sub t)).1 ((inside_iff ..).mp (W.stores_sub t)).2); rw [sprigs,hx,fern_local W F U p k V h]; rfl

structure Launch (W:Tunnel s)(F:Net s T L y C C' b)(U:Micro s)(p:Duo s)(k:Tiling s) : Prop extends Firm W F U p where
 step1 : k.r=1
 wardK : ward k W
 curvature : Rings U W.mem (climate k.b)
 tollX : sphereRate*(amt y)≤soil k.b

variable (Y:Launch W F U p k)
include Y
lemma Initial : Alert A (cloak W W.lips) (headM W p) (sphereRate*amt y) := by
 let X:=gauge (haloM W p) A; have hp:Alert X (cloak W W.lips) (headS s) (sphereRate*amt y):=by
    intro i p; have he:= inside_iff ..|>.mp p; have hx:= inside_cost W F U _ Y.toFirm i he.1 he.2; change dist (scaledV (X i) Seed) Seed≤_; apply le_trans ?_ (mul_le_mul_of_nonneg_left hx sphereRate_cost.positive.le); nth_rw 2 [← scaled_one Seed]; exact scaled_chord ..
 exact urgent_morph hp (haloM W p)⁻¹ (by unfold X; rw [gauge_trans,inv_mul_cancel,gauge_self]) (fun _ _=>rfl)
private lemma ripe : let S:=cloak W W.lips; Rings (gauge R A) W.mem (climate k.b)∧ Alert (gauge R A) S (shuffle R (headM W p)) (soil k.b):= ⟨rings_g (rings_g Y.curvature _) _,fun i t=> urgent_s _ _ _ _|>.le.trans (((Initial W F U p k Y) i t).trans Y.tollX)⟩ -- let syntax apply
lemma fern_f (x:Site s) {i:Link s}(p0:x=i.1∨x=endAt i)(v:i∈ inside W.mem)(h:i∉inside (cloak W (body W))) : ferns W F U p k x=shuffle R⁻¹ (tea W F U p k) x:=by
 unfold ferns; split; swap; · rfl
 rename_i e; obtain ⟨l,r⟩:= ripe W F U p k Y; unfold shuffle tea; rw [tree_eq Y.step1 _ _ (cloak_sub ..) l r x (pin_corridor W Y.wardK i v h x p0 e), shuffle,←scaled_s]; simp [scaled_one] -- tune under unfolding
lemma flowering : Alert A W.mem (ferns W F U p k) (inheritance k.b):=by
 obtain ⟨l,r⟩:= ripe W F U p k Y; let T:=tea W F U p k; intro i h; by_cases p':i∈inside (cloak W (body W)); swap
 · rw [show urgent A i (ferns W F U p k)= urgent A i (shuffle R⁻¹ T) from ?_]; swap; · unfold urgent; rw [fern_f W F U p k Y _ (i:=i) (Or.inl rfl) h p', fern_f W F U p k Y _ (i:=i) (Or.inr rfl) h p']
   have he:= tree_urgent Y.step1 _ _ (cloak_sub ..) l r _ i.2 (corridor W Y.wardK i h p').1; rw [←urgent_s A i (shuffle R⁻¹ T) R, shuffle_seq, mul_inv_cancel, shuffle_one]; exact he
 obtain ⟨v,g⟩:= inside_iff ..|>.mp p'; unfold urgent; rw [ferns,if_pos g, ferns,if_pos v]; apply le_trans ((Initial W F U p k Y) i (inside_cov (S:=cloak W (body W)) (fun i u=>mem_filter.mpr ⟨(mem_filter.mp u).1, (mem_filter.mp u).2.trans (Nat.le_add_right ..|>.trans Y.wardK.2.1)⟩) p')) (Y.tollX.trans ?_); unfold soil inheritance; rw [←one_div]; gcongr; exact leaf_one
lemma sprigs_urgent : Alert U W.mem (sprigs W F U p k) (inheritance k.b):= urgent_morph (flowering W F U p k Y) χ⁻¹ (by unfold orient; rw [gauge_trans,inv_mul_cancel,gauge_self]) (fun _ _=>rfl)
end Frame
end YM.CF.BPress.Meadow
