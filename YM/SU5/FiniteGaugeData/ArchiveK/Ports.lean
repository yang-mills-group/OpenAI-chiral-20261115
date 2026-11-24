import YM.SU5.FiniteGaugeData.ArchiveK.Recur
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace YM.CF.Window.ArchiveK
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush Largo WithLp
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
set_option linter.unusedSectionVars false
attribute [local instance] opCStarAlgebra
open LightK Violas
variable {G:E4≃ₗᵢ[ℝ] E4}{D m u v:ℕ}(K:ZephyrG G D m) (p:Space3) (F:FilterK)
namespace Midway
abbrev Pix(v:ℕ):= Tang→Fin v
abbrev Zpo(w:ℕ):= Fin (w^3)
abbrev Stamp(v w:ℕ): Type:=Pix v × Zpo w -- abbrev
abbrev ground (x:Pix v): Tang→ℤ:= fun i=> (x i).val
abbrev Cub(p:ℕ) :ℕ:=p^3
lemma ground_in : Injective (ground (v:=v)):=by intro i j e; funext z; apply Fin.ext; exact Int.ofNat_inj.mp (congr_fun e z)
lemma inn(q w:ℕ) : page (Stamp q w)=(q*w)^3:=by simp [page,Stamp,Pix,Zpo,Tang,mul_pow]
local notation "∆"=> depthG G
local notation "Ω"=> sailX G
local notation "Σ"=> crestG G p
local notation "Γ"=> emitX
variable (q w:ℕ)
-- orientation sign b= pos Upper; neg lower. lattice graph.L
abbrev basetime (q:ℕ):=32*q
def flagZ (b:Bool) (t:ℕ):ℤ:= if b then t else -(t:ℤ)
def terraceY (j:Stamp q w) (b:Bool) : Cover := full (ground j.1) (flagZ b (basetime q + j.2.val))
def actor (j:Stamp q w) (b:Bool) : Cover := ∑ i:Axis, (terraceY q w j b i) • runeX K i -- mark Lower centered at dotted.Then shift filter.Other side.The cartridge.
local notation "U"=> actor K q w
local notation "T"=> terraceY q w
lemma actor_e(j:Stamp q w)(b:Bool) : emitX (actor K q w j b)= (D:ℝ) • G (position (songQ (1:ℝ) (ground j.1)) (flagZ b (basetime q+j.2.val))):=by
 unfold actor; rw [rune_camera, show Γ (terraceY q w j b) =position _ _ from ?_]; apply PiLp.ext; intro i; refine Fin.lastCases ?_ (fun i=>?_) i; rfl; simp only [emit_axis,songQ,position,terraceY,emitX]; unfold full; simp
-- geometry depth, injection. depths interval independence.
def beadY(q D:ℕ)(k:ℕ):ℝ:= (basetime q + k:ℕ)* (D:ℝ)
lemma flagplus (j:Stamp q w) (b:Bool): depthG G (Γ (actor K q w j b))= if b then beadY q D j.2.val else -(beadY q D j.2.val):=by
 unfold depthG; rw [actor_e]; unfold sailX; rw [up_G,real_inner_smul_right,LinearIsometryEquiv.inner_map_map, kv]; unfold flagZ beadY; cases b<;> simp [mul_comm] <;> ring
lemma collar (j:Stamp q w) (b:Bool): crestG G p (Γ (actor K q w j b))= inner ℝ p (songQ D (ground j.1)):=by
 unfold crestG; rw [actor_e]; unfold seedX; rw [up_G,real_inner_smul_right,LinearIsometryEquiv.inner_map_map, kv,zero_mul,add_zero]; rw [show songQ (D:ℝ) (ground j.1)=(D:ℝ) • songQ (1:ℝ) (ground j.1) from ?_,real_inner_smul_right]; apply PiLp.ext; intro i; simp [songQ]
lemma actor_t(b:Bool) : Injective (fun j:Stamp q w=> actor K q w j b):=by
 rintro ⟨i,u⟩ ⟨j,z⟩ e; have hv:0<(D:ℝ):= Nat.cast_pos.mpr K.unitC; obtain t:=congrArg Γ e; rw [actor_e,actor_e] at t; obtain v:= G.injective ((smul_right_injective _ hv.ne') t); have ht := congrArg YM.time v; have hx:=congrArg spatial v; simp only [time_position,spatial_position] at ht hx; dsimp only at *; have he :i=j:=by apply ground_in; funext a; have he:= congrArg (fun x:Space3=>x a) hx; change 1*_ = 1*_ at he; simpa using he -- tune
 rw [he]; refine congrArg (fun y=> (j,y)) (?_ : u=z); apply Fin.ext; unfold flagZ at ht; cases b <;> simp at ht; exact ht; exact ht
include K
lemma spore (j:Pix q) (b:ℝ)(t:0≤b) : ‖songQ b (ground j)‖ ≤ 3*b*q:=by
 let p:= songQ b (ground j); have he(i:Tang): 0≤p i:= by unfold p songQ; dsimp only [ground]; positivity
 have hv: ‖p‖^2≤ 3*(b*q)^2:=by
    rw [EuclideanSpace.real_norm_sq_eq]; refine (sum_le_sum (g:=fun i:SpaceAxis=> (b*q)^2) (fun i _=>?_ )).trans (le_of_eq ?_)
    · apply pow_le_pow_left₀ (he i); change b*↑((j i).val:ℤ) ≤_; push_cast; gcongr; exact (j i).isLt.le
    simp [Tang, SpaceAxis]; -- tune
 change ‖p‖ ≤ _; rw [←sq_le_sq₀ (norm_nonneg _) (by positivity:0≤3*b*q)]; apply hv.trans ; nlinarith only [sq_nonneg (b*q)]
-- radial & per-coordinate. charges bounds high. objective eventually all q width. simpler q≥ R=w^3 implies heights. component signs. needed translated lower (filter) too after. 
lemma square_R (e:w^3 ≤ q)(j:Stamp q w)(b:Bool): ‖Γ (actor K q w j b)‖ ≤ 36*q*D:=by
 let x:=songQ 1 (ground j.1); let v:ℝ:= flagZ b (basetime q+j.2.val); have hv: |v| ≤ 33*q:= by
    have he: j.2.val≤ q:= Nat.le_trans j.2.isLt.le e; unfold v flagZ basetime; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> push_cast <;> first| (rw [abs_neg,abs_of_nonneg (by positivity:0≤32*(q:ℝ)+j.2.val)]; linarith only [Nat.cast_le (α:=ℝ)|>.mpr he])| (rw [abs_of_nonneg (by positivity:0≤32*(q:ℝ)+j.2.val)]; linarith only [Nat.cast_le (α:=ℝ)|>.mpr he])
 rw [actor_e,norm_smul, Real.norm_natCast,LinearIsometryEquiv.norm_map]; have ht: ‖x‖≤3*q:= by simpa using spore K q j.1 (1:ℝ) zero_le_one;
 rw [mul_comm _ (D:ℝ)]; refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg D); rw [←sq_le_sq₀ (norm_nonneg _) (by positivity)]; rw [norm_xray]; change ‖x‖^2+v^2 ≤_; have hp:= add_le_add (pow_le_pow_left₀ (norm_nonneg x) ht 2) (pow_le_pow_left₀ (abs_nonneg v) hv 2); rw [sq_abs] at hp; nlinarith only [hp,sq_nonneg (q:ℝ)]
lemma sign_R (j:Stamp q w)(b:Bool)(i:Axis) : 6*(q:ℝ)*D ≤ if b then ((Γ (actor K q w j b)) i) else -((Γ (actor K q w j b)) i):=by
 let f(k:ℝ):= seedX G (songQ k (ground j.1)); have hb: ‖f D‖ ≤ 3*q*D:=by unfold f; rw [seed_size]; exact le_trans (spore K q j.1 (_:ℝ) (by positivity)) (le_of_eq (by ring)); -- tune
 let t0:=(beadY q D j.2.val); let v:=emitX ((U) j b); have hv:v=f D + (if b then t0 else -t0) • Ω:=by
    rw [show v=_ from actor_e K q w j b]; let r:ℝ:= flagZ b (basetime q+j.2.val); let X:= songQ 1 (ground j.1); change (D:ℝ) • (upright G (X,r))=_; -- tune unifier of prod
    rw [line_G,smul_add,smul_smul]; -- compare tang via seed linear
    congr 1; · unfold f seedX; simp_rw [up_G,←map_smul]; apply congrArg G; apply PiLp.ext; intro i; refine Fin.lastCases ?_ (fun j=>?_) i; change (D:ℝ) • (0:ℝ)=(0:ℝ); simp; simp [X,position,songQ]
    apply congrArg (fun x:ℝ=>x • Ω); change (D:ℝ)*r=_; unfold r t0 flagZ beadY; cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> push_cast <;> ring
 have he:= (arm_abs (f D) i).trans hb; have hT:32*(q:ℝ)* D ≤ t0:= by unfold t0 beadY basetime; push_cast; nlinarith only [show 0 ≤ (j.2.val:ℝ)*(D:ℝ) by positivity];
 have hy:0≤ 32*(q:ℝ)* D:=by positivity;
 have hp:= mul_le_mul hT (K.flat i) (by norm_num) (le_trans hy hT); change _ ≤ if b then v i else -v i; rw [hv]; cases b <;> simp only [Bool.false_eq_true,↓reduceIte,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul] <;> linarith only [hp,(abs_le.mp he).1,(abs_le.mp he).2,hy]
end Midway
end YM.CF.Window.ArchiveK
