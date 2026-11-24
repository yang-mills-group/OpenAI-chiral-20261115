import YM.CF.Pso.Fume
import YM.CF.BProof.Floral.Crest
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}
open Vow Salt
variable (P:BudgetPoint)(s:Sweep n)
local notation "Ta"=> actY s
local notation "HQ"=> (hail_Q s).val
local notation "Φg"=> (Finset (Dwell n))
open Vow Larch
open Bake Lilt Rue Trees
open YM.CF.Floral
open scoped YM.CF.Mew
private lemma additive {E F:Type*}[AddCommGroup E][AddCommGroup F](L:E→ F)(p:∀ x y,L (x+y)=L x+ L y)(x y:E): L (x-y)= L x-L y:= (eq_sub_of_add_eq (by rw [←p,sub_add_cancel]))
local notation "w_"=> P.supportExponent+1+1
variable (κ:Ids n)(p:1≤h)
lemma suit_subΩ {R R':RegBudget n}(t:Sym_P (numbD R))(u:Sym_P (numbD R')): Sym_P (numbD (R-R')):=by
 have ht:numbD (R-R')= numbD R-numbD R':=by
    funext i v; change R i v-R' i v- wage_Q 2 (R i v-R' i v)= (R i v-wage_Q 2 (R i v))-(R' i v-wage_Q 2 (R' i v)); rw [additive (E:=Cipher n) (F:=Cipher n) (wage_Q 2) (plus_Y 2)]; abel
 rw [ht]; intro s; rw [additive (E:=RegBudget n) (F:=RegBudget n) (base_Q s) (plus_k s),t,u]
include p
lemma regular_xray {R R':RegBudget n}(t:Sym_P (numbD R))(u:Sym_P (numbD R')){N N':Pax n}(t0:Sym_a N)(u0:Sym_a N')(t1:Turf N)(u1:Turf N')(w:Books P (R-R') h c)(W: Binder P h (P.supportExponent+1+1) (N-N') b): Books P ((writ_E R+cast_E N κ)-(writ_E R'+cast_E N' κ)) h (wren_K P.order P.power*c+reserveT P.power P.order P.B 1*b):=by
 let F:= R-R'; let Z:=N-N'; let h₀:=zero_le_one.trans p
 obtain ⟨i,g,v⟩:=beauty.mp W
 have hx:= worth_R P Z κ (fun s A x=> by change N _ _- N' _ _= suit_Y s _; rw [t0 s A,u0 s A]; exact (map_sub ..).symm) (fun i v w=>congrArg₂ (·-·) (t1 i v w) (u1 i v w)) h₀ g v
 have ht:= addT P (cup_R P (R-R') w (suit_subΩ t u) h₀) hx
 have he:cast_E Z κ=cast_E N κ-cast_E N' κ:= by funext i v; exact smul_sub (bassH (lagE i)) (N (lagE i) (v,κ)) (N' (lagE i) (v,κ))
 have hz:writ_E (R-R')+cast_E Z κ=writ_E R+cast_E N κ-(writ_E R'+cast_E N' κ):=by rw [additive (E:=RegBudget n) (F:= RegBudget n) writ_E writ_k,he]; abel
 rw [←hz]; exact ⟨ht.weight,fun _ g=>g.elim⟩
lemma heats_xray {K K':Cusp n} (t:Mono_W K)(u:Mono_W K'){g f:Aura n→ℝ}(pV: Heats P h (P.supportExponent+1+1) (K-K') c)(s:HiveQ (fun i=> ‖g i-f i‖) P (P.supportExponent+1+1) b): Heats P h (P.supportExponent+1+1) (writ_K K+nextE g-(writ_K K'+nextE f)) (pack_Q P.order*c+b):=by
 let h₀:=zero_le_one.trans p
 obtain ⟨A,T,S⟩:= Heats.iff_anuk.mp pV
 have m:Mono_W (K-K'):=by intro i D d v x; change wage_Q 2 (K i D x-K' i D x)= K i D x-K' i D x; rw [additive (E:=Cipher n) (F:=Cipher n) (wage_Q 2) (plus_Y 2), t i D d v, u i D d v]
 have he:= memo_P (K-K') A P T m h₀
 have hg: Heats P h (P.supportExponent+1+1) (writ_K (K-K')) (pack_Q P.order*c):= Heats.iff_anuk.mpr ⟨_,he,fun i=>family_Q A S _ i⟩
 have hh: Heats P h (P.supportExponent+1+1) (nextE g-nextE f) b:=by
    refine beauty.mpr ⟨_,fun i=> ⟨norm_nonneg _,fun j v=>?_⟩,s⟩
    have hx:(nextE g i j-nextE f i j)= -(g i-f i) • (1:Copy n):= funext fun v=>by
       change -(g i • (1:Cipher n)) - -(f i • 1)=(-(g i-f i)) • (1:Cipher n); rw [_root_.neg_smul,_root_.sub_smul]; abel
    change Medal P _ _ (nextE g i j-nextE f i j) _ _; rw [hx]; exact (Medal.oneT.rum _).big (by rw [norm_neg,mul_one])
 have hz:writ_K (K-K')=writ_K K-writ_K K':=by
    unfold writ_K; simp_rw [show ∀ (s:Sweep n),force_V s (K-K')=force_V s K-force_V s K' from fun s=>funext fun i=> funext fun j=>funext fun v=>map_sub (suit_Y s⁻¹) _ _,sum_sub_distrib,smul_sub]
 rw [hz] at hg; rw [show writ_K K+nextE g - (writ_K K'+nextE f)= writ_K K-writ_K K'+(nextE g-nextE f) from (by abel)]; exact hg.plus hh
end YM.CF.Ione
