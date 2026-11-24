import YM.CF.Vp929.Match.Blazon
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Sour
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree Cadre Palot
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Fock Rush Scroll Paige Vault Phase Acorn Spire
open Pastry Vow Rue
attribute [local instance] opCStarAlgebra
variable {n:Side}{a b c d C r:ℝ}[Nonempty (Haro.ΘS r)]
local notation "SA"=> Seat n
local notation "VX"=> Aura n
local notation "Hk"=> hook SA
open Hake Jet Sault Stax
attribute [local instance] loreM loreN
open Branch Tenant Drapes Rill Sault
attribute [local instance] Rill.boreKSpace Rill.boreXN
local notation "JS"=> Single n
local notation "SO"=> Support (More n)
local notation "Γ"=> (FC (Dwell n))
open Exa Tap Dial Haro
variable {κ:Type*}(T S:BeatL n)
local notation "Φ"=> body_Q (N:=n) r
variable {T S} {A:Elm n (ΘS r) d a b}(q:Tempered A){p:BudgetPoint}{t z0 z1 W:ℝ}{δ:ℕ}{L:Scree.Loom n}(g:Roof n t d δ L)(u:0<d)(W0:1 ≤ W)
variable {H: Op (Single n)→ FC (Dwell n)} {Z:Single n→ Single n→FC (Dwell n)}(f: Glyph H Z W)
variable (k:HopeT d z0 z1 p.order)(v:p.threshold ≤ t)(w:p.threshold ≤ z1)(hQ:δ+10 ≤ p.B)(hq:cipherK δ≤ 5*p.B)(hB:3≤p.B)
include f
open Glyph
lemma chorX {Y: ΘS r→ Op JS}(h:Poetic Y):Poetic (fun i=>H (Y i)):=by
 apply h.c_lin H
 · intro x y; simp_rw [f.whirl,Matrix.add_apply,add_smul,sum_add_distrib]
 intro t x; simp_rw [f.whirl,Matrix.smul_apply,Finset.smul_sum, smul_assoc t]
include u q
lemma collσ (V:Orbit n)(T: SO)(O:Aura n):Poetic (fun i=>Sault.rind (coll_T p O ∅ (Glyph.cure H g u (A.F T i)) V)):=by
 unfold coll_T; split_ifs; swap; · simp_rw [Sault.rind,map_zero]; exact Poetic.zero
 exact Poetic.comp ((Pastry.cane _).eval.restrictScalars ℝ) (chorX f (q T _))
lemma νPh(T:Aura n)(V:Orbit n):Poetic (fun i=>A.into.vik H g u p i T V):=by
 unfold Lawn.vik actsF; simp_rw [Finset.sum_apply]; exact Poetic.cogv _ _ (fun j _=>chorX f (q j _))
omit q f
variable {v₀:ℝ}{B': BondL T S (body_Q (N:=n) r) v₀ b a d}
include W0 v w hQ hq hB k f q
lemma φ_vote (T:Scree.Hub n)(V:Orbit n)(X:SO)(x:X∈Glyph.panel p T):Poetic (fun i=> vote (A.F X i) g u p H T V.1):=by
 let F(i):= vote (A.F X i) g u p H T V.1
 let J: Cipher n →ₗ[ℝ] FC (Dwell n):= ((Dough (Dwell n)).val).toLinearMap.restrictScalars ℝ
 have h:Poetic (fun i=>J (F i)):=by
    change Poetic (fun i=> (F i).val)
    have he(i): (F i).val= _ := runT g u f A i v hQ hq hB k w W0 T X x V
    simp_rw [he]; exact collσ q g u f V X (Bake.lagE T)
 obtain ⟨G,m⟩:=LinearMap.exists_leftInverse_of_injective (f:=J) (LinearMap.ker_eq_bot.mpr Subtype.coe_injective)
 rw [show (fun i=> vote (A.F X i) g u p H T V.1)= (fun i=> G (J (F i))) from funext fun i=>(DFunLike.congr_fun m _).symm]
 exact h.comp G
lemma φ_radical :Poetic (fondC g u A H p):=by
 apply Poetic.assemble; intro T; apply Poetic.assemble; intro V; unfold fondC doveK; simp_rw [Finset.sum_apply,Pi.smul_apply]; exact Poetic.cogv _ _ (fun j t=>Poetic.money _ (φ_vote q g u W0 f k v w hQ hq hB T (V,Classical.arbitrary _) j t))
omit q f
variable (l:LaurelP B')
include l
lemma syllabi :Poetic (B'.lineH (p:=p) g u) ∧ Poetic (fun i=> B'.floatH (p:=p) g u i+B'.scarf (p:=p) g u i)∧ Poetic (B'.choir (p:=p) g u):=by
 refine ⟨φ_radical l.firm g u W0 (pal_v W W0) k v w hQ hq hB, (φ_radical l.mild g u W0 (pal_v W W0) k v w hQ hq hB).add (φ_radical l.uplift g u W0 (oreV W W0 _) k v w hQ hq hB),?_⟩
 apply Poetic.assemble; intro j; apply Poetic.assemble; intro V
 exact (((((νPh l.firm g u (pal_v W W0) j V).add (νPh l.mild g u (pal_v W W0) j V)).add (νPh l.uplift g u (oreV W W0 _) j V)).add (νPh (l.coneF false) g u (tail_k W W0) j V)).add (νPh (l.coneF true) g u (leg_k W W0) j V)).add (νPh l.step g u (less_k W W0) j V)
end YM.CF.Sour
