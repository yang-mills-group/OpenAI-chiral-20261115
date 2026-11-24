import YM.CF.Cadre.Point
import YM.CF.Cadre.Gear
import YM.CF.Vow.Grow
import YM.CF.Bake.Pep
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Stax
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
local notation "CΞ"=> Cipher n
variable (P: BudgetPoint)(h:ℝ)(δ:ℕ)
-- output O.D mask secure all.Leaves. δ-radius marks for operator exposure
abbrev Lives (X:Aura n)(D:Support (More n))(U:Copy n): Prop:=∀ i:Orbit n,U i ≠0→ halo δ D ⊆ X.val∧D ⊆ flags P.threshold i.1
structure Fray (X:Aura n)(D:Support (More n))(U:Copy n)(C:ℝ):Prop where
 merit: Medal P X.val D U h C
 loaf:Lives P δ X D U
variable {P h δ}
section
variable {F W:Copy n}{C D E:ℝ}{X:Aura n}{S'i:Support (More n)}
lemma Fray.sumP {ι:Type*}(Z:Finset ι)(U:ι→ Copy n)(r:ι→ℝ)(hQ:∀ i∈Z,Fray P h δ X S'i (U i) (r i)):Fray P h δ X S'i (∑ i∈Z,U i) (∑ i∈Z,r i):=by
 refine ⟨Medal.sumP _ _ _ fun i p=> (hQ _ p).merit,fun i p=>?_⟩; rw [Finset.sum_apply] at p; obtain ⟨y,v,p⟩:= exists_ne_zero_of_sum_ne_zero p; exact (hQ y v).loaf i p
lemma Fray.smulF(p:Fray P h δ X S'i F C)(t:ℝ):Fray P h δ X S'i (t • F) (‖t‖*C):=⟨p.merit.rum _,fun i q=> p.loaf i fun v=> q (by rw [Pi.smul_apply,v,smul_zero])⟩
lemma Fray.vert {Y:Aura n}{D:Support (More n)}(Z:Finset (Aura n))(t: Z∈drum X Y D)(W:Aura n→ Copy n)(v:Aura n→ℝ)(g:∀ i∈Z, Fray P h δ i (D∩i.val) (W i) (v i))(w:0 ≤ h):Fray P h δ X D (∏ i∈Z,W i) (∏ i∈Z,v i):=by
 obtain ⟨⟨_,e⟩,_,f⟩:= (drum_p ..).mp t; have hz(y:Aura n)(p:y∈Z):y.val⊆ X.val:= (coneL p).trans (by rw [f]; exact subset_union_right)
 have hx(i:Aura n)(p:i.val⊆X.val): i.val\(D∩i.val)⊆ X.val\D:=fun j s=>let h:=mem_sdiff.mp s; mem_sdiff.mpr ⟨p h.1,fun t=>h.2 (mem_inter.mpr ⟨t,h.1⟩)⟩
 refine ⟨Medal.prodP Z _ _ (fun i q=> (g i q).merit.stretchB (hz i q) inter_subset_left (hx i (hz i q))) w,?_⟩; intro i l; rw [Finset.prod_apply] at l; have hp(y:Aura n)(p:y∈ Z):= (g y p).loaf i (fun g=>l (prod_eq_zero p g))
 constructor
 · intro x k; obtain ⟨j,hj,z⟩:=halo_spec.mp k; obtain ⟨a,h,u⟩:=mem_biUnion.mp (e hj); exact hz a h ((hp a h).1 (halo_spec.mpr ⟨j,mem_inter.mpr ⟨hj,u⟩,z⟩))
 intro j y; obtain ⟨a,h,u⟩:=mem_biUnion.mp (e y); exact (hp a h).2 (mem_inter.mpr ⟨y,u⟩)
end
variable (F:Aura n→Support (More n)→ Copy n)(r: Aura n→ Support (More n)→ℝ)(hF:∀ X:Aura n,∀ D⊆ X.val,Fray P h δ X D (F X D) (r X D))
variable (K:Rinse (Seat n) (Copy n))(z:Aura n→ℝ)
-- `tax` kernel consumed local.Y. all gauges.Y masks. value EXACT always even if δ-tight invalid.U=0. No tag symmetry yet
structure Pitch (P:BudgetPoint)(h:ℝ)(d:ℕ)(K:Rinse (Seat n) (Copy n))(C:Aura n→ℝ)(M:Orbit n→ Aura n→ FC (Dwell n)) :Prop where
 dice :0≤C
 start:∀ X D Y,K X D Y 0=0
 plays:∀ (X: Aura n),∀ D⊆X.val,∀ Y:Aura n,Y.val⊆X.val→∀ v:ℝ,∀ F:Copy n,Fray P h d X D F v→Fray P h d X D (K X D Y F) (C Y*v)
 edge:∀ i Y,Fock.Sector (camp (n:=n) Y.val) false (M i Y)
 body:∀ (X Y:Aura n)(i: Orbit n),Rue.FleetS P.threshold i.1→Y.val⊆X.val→∀ C:ℝ,∀ F:Copy n,let D:=flags P.threshold i.1 ∩ X.val; Fray P h d X D F C→ (K X D Y F i).val=Sault.rind (M i Y*(F i).val)
variable {M:Orbit n→Aura n→ FC (Dwell n)}(T:Pitch P h δ K z M)
local notation "Q"=> Cadre.chip K F
local notation "N"=> Cadre.chip (cribR z) r
local notation "Qd"=> nutL K F
local notation "Nd"=> nutL (cribR z) r
variable (w:0≤h)
open PowerSeries
lemma crest(X Y:Aura n)(Z: Hk)(D:Support (More n))(n':ℕ)(p: Z∈drum X Y D)(g:∀ i∈Z,∀ j≤n',Fray P h δ i (D∩i.val) (coeff j (Q i (D∩i.val))) (coeff j (N i (D∩i.val))))(w:0 ≤ h):Fray P h δ X D (coeff n' (∏ i∈Z,Q i (D∩i.val))) (coeff n' (∏ i∈Z,N i (D∩i.val))):=by
 rw [coeff_prod,coeff_prod]; apply Fray.sumP; intro k u; exact Fray.vert Z p _ _ (fun i t=> g i t _ ((single_le_sum (fun j _=> Nat.zero_le (k j)) t).trans_eq (mem_finsuppAntidiag.mp u).1)) w
include T
lemma bondR (X Y:Aura n)(D:Support (More n))(u:D⊆ X.val)(n':ℕ)(G:Finset Hk)(g:∀ X:Aura n,∀ D⊆X.val,∀ i≤n',Fray P h δ X D (coeff i (Q X D)) (coeff i (N X D)))(w:0 ≤ h):Fray P h δ X D (coeff n' (rill K Q G X D Y)) (coeff n' (rill (cribR z) N G X D Y)):=by
 rw [rils,rils]; apply Fray.sumP; intro i v; have hx: i∈ drum X Y D:= (mem_inter.mp v).1; exact T.plays _ _ u _ (by rw [(drum_p ..|>.mp hx).2.2]; exact subset_union_left) _ _ (crest F r K z X Y i D n' hx (fun a b=> g _ _ inter_subset_right) w)
include w hF
lemma fed(X:Aura n)(D:Support (More n))(u:D⊆ X.val)(i:ℕ):Fray P h δ X D (coeff i (Q X D)) (coeff i (N X D)):=by
 induction i using Nat.strong_induction_on generalizing X D with
 |h i ih=>
    cases i with
    |zero=> rw [Cadre.peg,Cadre.peg]; exact hF _ _ u
    |succ i=>
       nth_rw 1 [Cadre.peel]; nth_rw 1 [Cadre.peel D (cribR z)]; rw [sprig,sprig]; -- tune
       unfold Cadre.stepL; rw [map_sum,map_sum]; rw [show ∀ v:ℝ,((i:ℝ)+1)⁻¹ • v= ‖((i:ℝ)+1)⁻¹‖*v from fun v=> by rw [smul_eq_mul,Real.norm_of_nonneg (by positivity)]]
       apply Fray.smulF; apply Fray.sumP; intro y _; exact bondR F r K z T X y D u i _ (fun j D' l i' m=>ih i' (Nat.lt_succ_of_le m) _ _ l) w
lemma deck(X:Aura n)(D:Support (More n))(u:D⊆X.val)(i:ℕ):Fray P h δ X D (coeff i (Qd X D)) (coeff i (Nd X D)):=by
 cases i with
 |zero=> rw [tick_r,tick_r]; exact ⟨Medal.zeroT,(fun i p=>False.elim (p rfl))⟩ -- tune
 |succ i=> rw [nutL,nutL,sprig,sprig,front,front,map_sum,map_sum]; rw [show ∀ v:ℝ,((i:ℝ)+1)⁻¹ • v= ‖((i:ℝ)+1)⁻¹‖*v from fun v=> by rw [smul_eq_mul,Real.norm_of_nonneg (by positivity)]]; apply Fray.smulF; apply Fray.sumP; intro y _; exact bondR F r K z T _ _ _ u _ _ (fun j D l i' _=> fed F r hF K z T w j _ l i') w
end YM.CF.Stax
