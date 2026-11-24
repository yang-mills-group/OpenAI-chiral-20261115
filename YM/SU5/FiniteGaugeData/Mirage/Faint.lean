import YM.SU5.FiniteGaugeData.Mirage.Velour
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 20000
set_option maxHeartbeats 440000
noncomputable section
namespace YM.CF.Window.Mirage
open Function Filter Lattice Cube Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
open Scroll Spire Peaks Tap Tenant Tulip Buffered Fock.Brique Window.Brique Largo
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
variable {N X:Side}{s r d w j:ℕ}{a C:ℝ}{σ τ:Window.Family}{S T U:Finset Cover}
local notation "Μ"=> Single N
local notation "Κ"=> FC (Single N)
open SU Scree Dial Cascade Skye Paige Branch
variable {n:ℕ}{c r C d f f₁:ℝ}{R T U:Support (More N)}
variable {Z:Peg N}(O:Casing N Z.e (Z.Ft false) c C d){o:Seat N}{W:Pane N→ℂ} {F:Corset T R o}{Y: FC (Single N)}{X:Op (Single N)}
variable {Y':Loom N}(h:CashMask F W U (d*r) Y')
open scoped Classical
include O h
lemma paid_copy (p:Marble (Z.Ft false (1:Pane N)) T n Y a) (t:Lattice.halo w T ⊆ U)(e: 0 ≤ Z.e) (g:0≤ f₁)(q: a +(2*tailCost c C w+r*C) ≤ f-f₁)(u:U⊆R): Crater w f₁ f Z R (cared U (cargo F W Y)) n false := by
 refine Crater.intro' g fun x t' H=>?_ ; have hx:x∈ setOf (fun x:Fields N=> Agrees U x.1 x.2):=by by_contra hv; apply H (Set.indicator_of_notMem hv _)
 rw [cared,Set.indicator_of_mem hx] at H ⊢; let P:=Z.Ft false; let v:= F.g x.1; have he : W x.1≠0:=fun t=> H (by unfold cargo; rw [t,zero_smul]); let y:= gauge v x.2
 have hw: Tulip.fare U (Tulip.profile y) 1 ≤ d*r:= (by
    let z:= h.top x.1 he; rw [show Tulip.fare U _ 1= Tulip.fare U (profile (gauge v x.1)) 1 from ?_]; exact z; apply sum_congr rfl; intro i p; apply congrArg (fun x=> ‖x-(1:Chin N) i‖); funext a; unfold profile; rw [ (Skye.tied U x.1 x.2 v v hx (fun i _=>rfl)) i (mem_filter.mp p).2.1 (mem_filter.mp p).2.2]) -- lhs y
 let r₀:= Z.e; have hv':Guard y r₀:= t'.cov v
 let K0:= 2*tailCost c C w+r*C; have hez : ‖cutM (modesIn N T)*(P y-P (1:Pane N))‖ ≤ K0:= shape_fee O w _ (1:Pane N) hv' (guard0 e) _ _ t (profile_trivial.symm ▸ hw)
 obtain ⟨P',j,ℓ,χ,D,q₁⟩:= p.prize; let Z₀:= twist (tradew N v⁻¹); let Z':=Z₀ P'; refine ⟨Z', rot _ ℓ _, T,t.trans u,j.twist_t _ (shifter v⁻¹ _), (trace_twist ..).trans χ,?_,?_⟩ -- order witness
 · let S' := acts (star (flipsP v⁻¹ Y)) (mateK N); have ht: Full Z' S':= by unfold S'; rw [shafted v⁻¹ Y]; exact twist_tap0 D v⁻¹
   intro k h; unfold cargo; rw [star_smul,act_smul,map_smul, show acts (creed false k) _ = _ from ht k h,smul_zero]
 have hz: P x.2= Z₀ (P y):=by rw [show P y=twist (tradew N v) (P x.2) from O.coloredWT x.2 t' v]; unfold Z₀; rw [Mono_tradew,twist_inv]
 have hk:‖P'*P y-P'*P 1‖ ≤ K0:= by rw [←mul_sub]; nth_rw 1 [←j.rightP]; rw [mul_assoc]; exact (norm_mul_le ..).trans ((mul_le_of_le_one_left (norm_nonneg _) (ℓ.norm_le _)).trans hez)
 change ‖Z₀ P' * P _‖ ≤ _; rw [hz,←map_mul,show Z₀=_ from rfl]; refine le_trans (le_of_eq (twist_norm ..)) ?_; change ‖P'*P (1:Pane N)‖≤a at q₁; change a+K0 ≤ _ at q; exact le_trans (sub_le_iff_le_add'.mp ((norm_sub_norm_le ..).trans hk)) (by linarith only [q₁,q])
omit O h
lemma Marble.turned (w:Marble X T n Y a) (g: Seat N→SU.E): Marble (twist (tradew N g) X) T n (flipsP g Y) a:=by
 obtain ⟨A,t,H,v,e,s⟩:=w.prize; let U:=tradew N g; refine ⟨twist U A,t.twist_t U (shifter g _), rot _ H U, (trace_twist ..).trans v, ?_,?_⟩; · rw [shafted g Y]; exact twist_tap0 e g
 rw [←map_mul]; exact (twist_norm ..).trans_le s
include O in
lemma Marble.rightRoom (v:0≤ Z.e)(g:SU.E)(K J:FC (Single N))(w:Marble (Z.Ft false 1) T n (K*J) a)(t:orbitB K g=K): Marble (Z.Ft false 1) T n (K*orbitB J g) a:=by
 obtain hw:= w.turned (globalH N g); rw [← O.coloredWT _ (guard0 v), globalWind,map_mul] at hw; nth_rw 1 [←t]; exact hw
section support
variable {P Q: Op (Single N)}{κ:ℕ}{M:Tulip.Male}
lemma abrupt (c1: Support (More N)): Stump c1 1:=⟨continuous_const,fun _ _ _=>rfl,fun x=> (norm_one (α:=ℂ)).le,fun _ _=>rfl⟩
end support
end YM.CF.Window.Mirage
