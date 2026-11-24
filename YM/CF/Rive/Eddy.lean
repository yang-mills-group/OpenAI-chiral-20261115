import YM.CF.Rive.Moor
import YM.CF.Rive.Fare
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Rive
open Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
variable {P:BudgetPoint}{X Y Z:Aura n}{V W:Firing n}{D:Support (More n)}
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial
variable {ι:Type}[Fintype ι][LinearOrder ι]
variable {N:Side} {T S:BeatL N}{R0:ℝ}[Nonempty (Haro.ΘS R0)]
open Haro Ione Larch Glyph Sour.BondL
variable {a b c d e s W:ℝ}(A: BondL T S (body_Q (N:=N) R0) b c a d){p:BudgetPoint}{L:Scree.Loom N}{q:ℕ}{t:ℝ}(g:Roof N t d q L)(h:0<d)(w0:1 ≤ W)
variable {z0 z1:ℝ}(k: HopeT d z0 z1 p.order)(hv:p.threshold ≤ z1)(y:p.threshold ≤ t)(hx:q+10 ≤ p.B)(v:cipherK q ≤5*p.B)(w:3≤p.B)
open Mew Push.AbsoluteSums Trees -- remove
local notation "sT"=> p.supportExponent+1+1
local notation "τx"=> A.bead W p
local notation "HX" i:max=> litB A g h W w0 k hv y hx v w i
variable (I: Key ι→ Aura N→ Support (More N)→ ℝ)(F: Key ι→ Vow.Cusp N)
variable (f:∀ i∈hill ι,∀ X:Aura N,∀ D⊆X.val,Fray p W (cipherK q) X D (F i X D) (I i X D))(r:∀ i∈hill ι,Bake.Turf (fun X=>F i X ∅)) (i: Haro.ΘS R0)
variable {ℓ μ M0 J K0 ε u α κ:ℝ}(ηP:TagT T S (body_Q (N:=N) R0) d)
variable (Ht:∀ i∈hill ι,Timer (Cadre.chip (cribR (A.bead W p)) (I i)) (A.bead W p) κ u μ (widthK N p.B) (spanV p.B) M0 J ε K0 1 (A.bead W p))(hl: 0≤ℓ)(hp:0<α)(pL:ℓ+α≤u-μ*1)(h':1 ≤κ)
local notation "Fv" k:max => pivotS A g h W (F k) w0 hv y hx v w (by assumption) i -- k collision
local notation "D'" z:max=> Φψ A g h W (F z) w0 hv y hx v w k i
local notation "Ω"=> (ε*M0+spanV p.B*α⁻¹*M0*J)
local notation "Θ" z:max=> fun x:Aura N=> (pivotS A g h W (F z) w0 hv y hx v w k i) x ∅
variable {hQ γ δ σ o p' O V:ℝ}(K: Key ι→ Pax N)(l₁:∀ x:Aura N,∀ i∈hill ι,∀ j:Orbit N, ¬ visible p x.val ∅ j.1 → K i x j=0)
variable(p_:∀ i∈hill ι, let R':=fun j:Aura N=> F i j ∅-F 0 j ∅; ∃ C A:Aura N→ℝ, (∀ j:Aura N,Medal p j.val ∅ (R' j-K i j) W (C j))∧ (∀ x:Seat N,tallB C p.B (p.supportExponent+1+1+1) x ≤ O) ∧ (∀ j:Aura N,Medal p j.val ∅ (K i j) W (A j)) ∧ (∀ x:Seat N,tallB A p.B (p.supportExponent+1+1+1) x ≤ V)) -- K i :=OLD_i−OLD_base
variable (hdv: (p.supportExponent+1+1)+δ ≤ ℓ)(ho:δ≤1)(hδ:0 < δ)(hγ:0<γ)(hq:degreePrice p.B γ δ <1)(hy:0< σ)(hm: M0+M0+σ*(V+ (O+(ε*M0+spanV p.B*α⁻¹*M0*J)+(ε*M0+spanV p.B*α⁻¹*M0*J))) ≤ γ) -- invalid notation. needs budget enters vP timer.B.M 
local notation "γx"=> degreePrice p.B γ δ
local notation "Yt"=> (O+Ω+Ω)
include Ht w0 f hl hp pL h' l₁ p_ hdv ho hδ hγ hq hy hm
lemma black_Q(z:Key ι)(hz:z∈hill ι):∃ (B:Aura N→ℝ), Ready Palot.stern p.B B (sT) γ δ (degreePrice p.B γ δ) ∧ (∀ X:Aura N, Medal p X.val ∅ ((Θ z) X) W (B X)) ∧ (∀ X:Aura N, Medal p X.val ∅ ((Θ 0) X) W (B X))∧∃ A:Aura N→ℝ,(∀ Y:Aura N,Medal p Y.val ∅ (FeeD p (Θ z) Y-FeeD p (Θ 0) Y-K z Y) W (A Y))∧∀ i:Seat N,tallB A p.B (p.supportExponent+1+1) i≤ (Yt+2*σ⁻¹*(γ*γx^1*(1-γx)⁻¹)+2*(γ*γx^2*(1-γx)⁻¹)):=by
 obtain ⟨C,L,q,hg,hvK,hKu⟩:= p_ z hz -- tune. identify implicit 
 let p':=fun (z:Mew.Key ι) (t:z∈hill ι)=> A.worth_K g h W w0 i _ k hv y hx v w (f z t) (Ht z t) hl hp pL
 let N0(z):=Sco (n:=N) (I z) τx; let Nℓ(z):=ScoL (n:=N) (I z) τx
 let U0:Pax N:= Θ z; let G' := Θ 0; let q0:= U0-G'-K z; let E:= C+urnL (Nℓ z)+urnL (Nℓ 0); have he(Y): Medal p Y.val ∅ (q0 Y) W (E Y):=by
    have hZ : q0 Y=(F z Y ∅-F 0 Y ∅-K z Y)+ ((D' z) Y)+ - ((D' 0) Y):=by unfold q0; dsimp only [U0,G',pivotS,Stax.lamp,Φψ]; simp only [Pi.sub_apply]; abel -- tune
    rw [hZ]; exact ((q Y).plus ((p' _ hz).1 _ _ (empty_subset _)).2.merit).plus ((p' _ roots).1 _ _ (empty_subset _)).2.merit.negT
 let X:= urnL (N0 z)+urnL (N0 0)+ σ • (L+E); have hf(t:Mew.Key ι)(ht:t∈hill ι)(x:Aura N): Medal p x.val ∅ ((Θ t) x) W (N0 t x ∅):= ((p' _ ht).1 _ _ (empty_subset _)).1.merit -- notation
 have hj := zero_le_one.trans w0
 have heX(i):(0:ℝ)≤ (L+E) i:=add_nonneg ((hvK i).wage hj) ((he i).wage hj); have hlX(i):0 ≤ σ*((L+E) i):=mul_nonneg hy.le (heX _)
 let a':=p.supportExponent+1+1+δ; have hk(t:Mew.Key ι)(ht:t∈hill ι)(x:Seat N): tallB (urnL (N0 t)) p.B a' x ≤ M0 ∧ tallB (urnL (Nℓ t)) p.B a' x≤ Ω:=by
    obtain ⟨u,V,y⟩:= p' t ht
    have h0: tallB (roofL (Nℓ t) κ) p.B ℓ x ≤ Ω := by nth_rw 1 [show ℓ=ℓ-0*1 from by ring]; rw [parse]; exact y x
    refine ⟨(tall_m _ (fun i=> (hf t ht i).wage hj) (le_trans hdv ((le_add_of_nonneg_right hp.le).trans pL)) x).trans (lam_H (N0 t) x κ p.B _ (zero_lt_one.trans_le h') (fun X D t=> (u _ _ t).1.merit.wage hj) (by rw [parse]; exact V x)|>.1), (tall_m _ (fun i=>(u _ _ (empty_subset _)).2.merit.wage hj) hdv x).trans (lam_H (Nℓ t) x κ p.B _ (zero_lt_one.trans_le h') (fun X D t=> (u _ _ t).2.merit.wage hj) h0|>.1)⟩
 have hE(x:Seat N): tallB E p.B a' x ≤ Yt :=by unfold E; rw [Larch.tall_add,Larch.tall_add]; exact add_le_add (add_le_add ((tall_m _ (fun i=> (q i).wage hj) (add_le_add_right ho _) _).trans (hg x)) (hk _ hz x).2) (hk _ roots x).2
 have hp'(Y):Medal p Y.val ∅ (U0 Y) W (X Y):=(hf _ hz Y).big ((le_add_of_nonneg_right ((hf _ roots Y).wage hj)).trans (le_add_of_nonneg_right (hlX Y)))
 have hx'(Y): Medal p Y.val ∅ (G' Y) W (X Y):=(hf _ roots Y).big ((le_add_of_nonneg_left ((hf _ hz Y).wage hj)).trans (le_add_of_nonneg_right (hlX Y)))
 have hL:Ready Palot.stern p.B X (sT) γ δ γx:=by
    refine ready_T hγ hδ hq (fun i=>(hp' i).wage hj) ?_
    intro t; unfold X; rw [Larch.tall_add,Larch.tall_add,Larch.tall_s,Larch.tall_add]; exact (add_le_add (add_le_add (hk _ hz t).1 (hk _ roots t).1) (mul_le_mul_of_nonneg_left (add_le_add ((tall_m _ (fun i=> (hvK i).wage hj) (add_le_add_right ho _) _).trans (hKu t)) (hE t)) hy.le)).trans hm
 have hy'(Y):Medal p Y.val ∅ (U0 Y-G' Y) W (σ⁻¹*X Y):=by
    rw [show U0 Y-G' Y=K z Y+q0 Y from by unfold q0; simp only [Pi.sub_apply,add_sub_cancel]]; refine ((hvK Y).plus (he Y)).big ((le_inv_mul_iff₀ hy).mpr (le_add_of_nonneg_left ?_)); exact add_nonneg ((hf _ hz Y).wage hj) ((hf _ roots Y).wage hj)
 have hy0(i:Aura N)(x:Orbit N): U0 i x-G' i x=K z i x +q0 i x:=by unfold q0; simp only [Pi.sub_apply,add_sub_cancel]
 refine ⟨X,hL,hp',hx',_, fun Y=> Rive.liftT Y σ hy hL w0 hp' hx' hy' he (K z) hy0 (fun v=> l₁ v z hz),fun i=>?_⟩ -- tune
 exact Rive.loft_T σ hy hL w0 hp' hx' hy' he _ hy0 (fun v=>l₁ v z hz) i ((tall_m E (fun i=> (he i).wage hj) (le_add_of_nonneg_right hδ.le) i).trans (hE i))
end YM.CF.Rive
