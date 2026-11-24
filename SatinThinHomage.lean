import SatinThinCarve
set_option autoImplicit false
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.QuadClock
open Neon
open Py
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
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich Stake Pail Pail.Dew
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew
variable {N n B:Side}{P:BudgetPoint}{h A C d Q:ℝ}{L:ℕ}

section
variable (x y z:Site n) (s:Sweep n)
open Classical
abbrev fromHere(x y:Site n): Finset (Sweep n):=univ.filter (fun s=>s∈cycleSweep n ∧ Earlier s x y)
lemma fromHere_iff : s∈ fromHere x y ↔ s∈cycleSweep n ∧ Earlier s x y:=by simp [fromHere]
lemma anyFrom : (fromHere x y).Nonempty:=⟨Sweep.mk 1 (x-y) false,(fromHere_iff ..).2 ⟨quad_id,earlier_translate ..⟩⟩
abbrev refund (x y:Site n) :ℝ:= ((fromHere x y).card:ℝ)⁻¹
lemma refund_pos : 0< refund x y:= inv_pos.mpr (by exact_mod_cast card_pos.mpr (anyFrom x y))
lemma refund_pr (r:ℝ) : refund x y*((fromHere x y).card * r)=r:= inv_mul_cancel_left₀ (by exact_mod_cast (card_pos.mpr (anyFrom x y)).ne') _
lemma sameFrom (g:s∈cycleSweep n)(w: Earlier s x y) (j:Sweep n): j ∈ fromHere y z ↔ s*j∈ fromHere x z:=by
 rw [fromHere_iff,fromHere_iff]; constructor; exact fun k=> ⟨(cycleSweep n).mul_mem g k.1,w.prod k.2⟩
 intro t; rw [← inv_mul_cancel_left s j]; exact ⟨(cycleSweep n).mul_mem ((cycleSweep n).inv_mem g) t.1,w.backward.prod t.2⟩
lemma refund_eq (g:s∈cycleSweep n)(w: Earlier s x y): refund y z=refund x z:=by
 rw [refund,refund,card_equiv (Equiv.mulLeft s)]; intro i; exact sameFrom x y z s g w i -- check
end
namespace Waxy
variable {V:Type*}[AddCommGroup V][Module ℝ V](P:Sweep n→ V →ₗ[ℝ] V)
  (multE:∀ s t:Sweep n,∀ k:V,P (s*t) k= P s (P t k)) (x y z:Site n)
  (L: V)
abbrev avenue (P:Sweep n→ V→ V)(D:V): Site n→ V:=fun i=> refund i y • ∑ s∈ fromHere i y,bandSign s • P s D
noncomputable abbrev hailQ : Site n→V:= avenue y (fun s=>P s) L
section
include multE
/- With reference y. -/
lemma hail_c (s:Sweep n)(p:s∈cycleSweep n)(q: Earlier s x z): P s (hailQ P y L z)= bandSign s • hailQ P y L x:=by
 rw [hailQ,avenue,refund_eq x z y s p q,map_smul,map_sum]; simp_rw [map_smul]; rw [smul_comm (bandSign s),Finset.smul_sum (r:=bandSign s)]
 refine congrArg (fun v:V=> refund x y • v) (sum_equiv (Equiv.mulLeft s) (sameFrom x z y s p q) (fun i (_:i∈fromHere z y)=>?_)); rw [← multE]; change _= bandSign s • bandSign (s*i) • _; rw [band_mul,smul_smul,←mul_assoc,tax_sq,one_mul]; rfl
end
#check hail_c

def Bent (P:Sweep n→ V →ₗ[ℝ] V) (a:Site n→ V): Prop:=∀ s∈cycleSweep n,∀ x y, Earlier s x y→ P s (a y)=bandSign s • a x
lemma hail_owned (a:Site n→V)(h:Bent P a) : hailQ P y (a y)=a:=by
 funext i; unfold hailQ avenue; have q:(fromHere i y).card • a i=∑ s∈fromHere i y,bandSign s • P s (a y):=by
    rw [←sum_const]; refine sum_congr rfl fun j (_r:j∈fromHere i y)=>?_ ; obtain ⟨l,p⟩:=(fromHere_iff ..).mp _r; rw [h j l i y p,smul_smul,tax_sq,one_smul]
 rw [show (fun s: Sweep n=> ((P s): V→ V))=fun s v=>P s v from rfl] -- tune redundant
 rw [←q]; unfold refund; rw [←Nat.cast_smul_eq_nsmul ℝ]; exact inv_smul_smul₀ (by exact_mod_cast (card_pos.mpr (anyFrom i y)).ne') _

-- instances of rotations, S:F etc
abbrev Eρ (s:Sweep n): RegBudget n→ₗ[ℝ]RegBudget n where
 toFun:=base_Q s
 map_add':=plus_k s
 map_smul' c k := funext₂ fun _ _=>map_smul (suit_Y s⁻¹) c _
abbrev Fρ (s:Sweep n): Copy n→ₗ[ℝ] Copy n where
 toFun:=turn_V s
 map_add' _ _ :=funext fun _=>map_add ..
 map_smul' c k :=funext fun _=>map_smul (suit_Y s⁻¹) c _
abbrev Kρ (s:Sweep n): Cusp n→ₗ[ℝ] Cusp n where
 toFun:=force_V s
 map_add' _ _ :=funext fun i=>funext fun j=>funext fun k=>map_add ..
 map_smul' c w :=funext fun i=>funext fun j=>funext fun k=>map_smul (suit_Y s⁻¹) c _
abbrev tρ (s:Sweep n):ℂ→ₗ[ℝ]ℂ:=(phaseB s).toLinearMap
lemma offsetWt (s:Sweep n)(z:ℂ): tρ s z=Spire.payZ s⁻¹ z:=castT ..
lemma hail_E (o: Site n)(z:RegBudget n): Bent Eρ (hailQ Eρ o z):=by
 apply fun s h x y t=> hail_c Eρ (fun s t x=> ?_) x o y z s h t
 funext i U; change suit_Y _ (x (moveHub _ i) (flashA _ U))=suit_Y _ (suit_Y _ _); rw [moon_Y,mul_inv_rev]; simp only [Function.comp_apply,step_k,lights] -- step index order s,t
lemma hail_F (o: Site n)(z:Copy n): Bent Fρ (hailQ Fρ o z):=by
 apply fun s h x y t=> hail_c Fρ (fun s t x=> ?_) x o y z s h t
 funext U; change suit_Y _ (x (yellA _ U))=suit_Y _ (suit_Y _ _); rw [moon_Y,mul_inv_rev]; simp only [Function.comp_apply,yell_t]
lemma hail_K (o: Site n)(z:Cusp n): Bent Kρ (hailQ Kρ o z):=by
 apply fun s h x y t=> hail_c Kρ (fun s t x=> ?_) x o y z s h t
 funext i D U; change suit_Y _ (x (moldA _ i) (actY _ D) (yellA _ U))=suit_Y _ (suit_Y _ _); rw [moon_Y,mul_inv_rev]; simp only [hush_k,tape_B,Function.comp_apply,yell_t]
lemma hail_t (o: Site n)(z:ℂ): Bent tρ (hailQ tρ o z):=by
 apply fun s h x y t=> hail_c tρ (fun s t x=> ?_) x o y z s h t
 simp only [offsetWt]; rw [mul_inv_rev,←warX]; unfold Spire.payZ; cases wageZ s⁻¹<;>cases wageZ t⁻¹<;>rfl -- unfolds? simplify

lemma nobody_t (o: Site n)(z:ℂ) : hailQ tρ o z=0:=by
 funext q; let b:=Pec.X (Equiv.swap 0 1)*Signed.mirror 0; have hx:detX b=false:=by unfold b; rw [det_p,detSwap 0 1 (by decide),det_t]; rfl
 obtain ⟨s,r,v,g⟩:=poseAll b q q; have hp:=hail_t o z s (cycleQ _|>.mpr (r.symm ▸ quad_swap_lo.mul (quad_mirror 0))) q q g; let J:=hailQ tρ o z q; unfold bandSign at hp; rw [tρ,ContinuousLinearMap.coe_coe,phaseB,wageInv,castT, show wageZ s=false from (by unfold wageZ; rw [r,v,hx]; rfl),r, show tax b= -1 from (by unfold b; rw [tax_m,tax_mi,tax_s 0 1 (by decide),mul_one]),neg_one_smul] at hp
 have hc:J+J=0:=eq_neg_iff_add_eq_zero.mp hp; rw [←two_mul] at hc; exact (mul_eq_zero.mp hc).resolve_left (by norm_num)
end Waxy
end YM.CF.QuadClock
