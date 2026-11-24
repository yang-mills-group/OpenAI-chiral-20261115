import YM.CF.Ione.Mesh
import YM.CF.Hype.Yom
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
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
variable (R E:RegBudget n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
lemma feed(n:Side)(v:ℝ): plight_C n * ((Fintype.card (Sweep n):ℝ)*v)=v:=by rw [plight_C,inv_mul_cancel_left₀ (by positivity)]
lemma oath_r(n:Side){E:Type*}[AddCommGroup E][Module ℝ E](p:E): plight_C n • (∑ _:Sweep n,p)= p:=by rw [sum_const]; simpa [plight_C, Nat.cast_smul_eq_nsmul ℝ] using (show _= p from inv_smul_smul₀  (show (Fintype.card (Sweep n):ℝ)≠0 from by positivity) p) -- tune nsmul
abbrev writ_E(R:RegBudget n):RegBudget n:= plight_C n • (∑ i:Sweep n,base_Q i R)
lemma step_k(t:Sweep n)(i:Hz):moveHub t (moveHub s i)=moveHub (s*t) i:=by
 refine Subtype.ext (Prod.ext ?_ (tape_B s t _)); change (boxA t).symm ((boxA s).symm i.val.1)= (boxA (s*t)).symm i.val.1; apply (boxA (s*t)).injective; simp [step_V]
lemma spin_E: Sym_P (writ_E R):=by
 intro i; apply funext; intro x; apply funext; intro Z; unfold base_Q; change step_F _ (writ_E R _) Z=(writ_E R x Z); simp only [writ_E,Pi.smul_apply,Finset.sum_apply,base_Q,step_F,Function.comp_apply,map_sum,map_smul, Spire.lights, moon_Y,step_k]; refine congrArg _ ?_; conv_rhs=>rw [←Equiv.sum_comp (Equiv.mulLeft i)]
 refine sum_congr rfl fun j _=>?_ ; rw [show Equiv.mulLeft i j=i*j from rfl]; rw [mul_inv_rev] -- `(i*j)^-1=j^-1*i^-1`
lemma sure_c (v:Sym_P R):writ_E R=R:=by unfold writ_E; simp_rw [v]; exact oath_r n _
abbrev Utrue : Sweep n→Prop:= fun _=>True
lemma spin_m (F:RegBudget n)(p:IncX (fun _=>False) F P h a)(q:Sym_P F):IncX Utrue F P h a:=by
 refine ⟨p.weight,fun i _ U g X V=>?_⟩; let s:=suit_Y i; have ht(x): s (suit_Y i⁻¹ x)=x:=by unfold s; rw [moon_Y,inv_mul_cancel,toon_Q]
 rw [←show FrameR i U _= _ from rfl]; rw [tama i _ g,←congrFun (congrFun (q i) X) V]; exact (ht _).symm -- tune syntax
lemma zero_r(x:Orbit n):exponentL P (0: RegBudget n) x.1=0:=by simp [exponentL,numbE]
lemma plus_k:base_Q s (R+E)=base_Q s R+base_Q s E:= funext fun _=> funext fun _=> map_add ..
lemma writ_k:writ_E (R+E)=writ_E R+writ_E E:=by unfold writ_E; simp_rw [plus_k,sum_add_distrib,smul_add]
variable (F':RegBudget n→Prop)
lemma thin_P (x:ℝ)(u:IncX (fun _=>False) R P h a):IncX (fun _=>False) (x • R) P h (|x| * a):=by
 obtain ⟨V,v,t⟩:=u.weight; refine ⟨⟨fun i=> |x| * V i,fun i=>scale_E P (v i) x,fun i=>?_⟩,fun _ v=>v.elim⟩
 apply le_trans _ (mul_le_mul_of_nonneg_left (t i) (abs_nonneg _)); rw [mul_sum]; apply le_of_eq; apply sum_congr rfl; intro j _; split; exact mul_left_comm _ _ _; simp -- tune
lemma ton_W (F:T0→ RegBudget n)(g:T0→ℝ)(p:∀ i, IncX (fun _=>False) (F i) P h (g i))(z:Finset (Sweep n)): IncX (fun _=>False) (∑ i∈z,F i) P h (∑ i∈z,g i):=by
 induction z using Finset.induction_on with
 | empty=> rw [sum_empty,sum_empty]; refine ⟨⟨0,fun i=>Vale.rinse ..,fun i=>?_⟩, fun _ v=>v.elim⟩; simp [BudgetPoint.mass]
 | insert i x v h=> rw [sum_insert v,sum_insert v]; exact Larch.add_v _ _ _ (p i) h
lemma harp_D(p:IncX (fun _=>False) R P h a):IncX (fun _=>False) (numbD R) P h a:=by obtain ⟨F,u,z⟩:=p.weight; exact ⟨⟨F,fun i=> post_C P (u i),z⟩, fun _ v=> v.elim⟩
abbrev wren_K(k p:ℕ):ℝ:= 1+terra_C k p
lemma cup_R (p:IncX (fun _=>False) R P h a)(v:Sym_P (numbD R))(t:0 ≤ h): IncX Utrue (writ_E R) P h (wren_K P.order P.power*a):=by
 refine spin_m P _ ?_ (spin_E R); have hx:numbD R+tree_C R=R:= funext fun i=>funext fun j=>sub_add_cancel ..
 nth_rw 1 [←hx]; rw [writ_k,sure_c _ v, wren_K,add_mul,one_mul]; refine add_v P _ _ (?_:IncX (fun _=>False) (numbD R) P h a) ?_ -- tune
 · exact harp_D P R p
 let K:= terra_C P.order P.power*a; let Z:= tree_C R
 have hu:= ton_W P (F:=fun s:T0=>base_Q s Z) (g:=fun _=>K) (fun i=> earth_F P i p t) univ
 have hp:= thin_P P _ (plight_C n) hu; rw [abs_of_pos (envy n),sum_const,card_univ,nsmul_eq_mul,feed] at hp; exact hp -- tune
lemma loan_v (U:Pane n)(Q: BudgetPoint)(x:Hz)(V:InkD n)(Y:Orbit n)(p:U=Y.1): numbE Q.threshold x.val.2 V U= if pingS Q.threshold x.val.2 U then V U else 0:=by subst U; rw [numb_b]; rfl
lemma force_r(V:Orbit n): suit_Y s (exponentL P (base_Q s R) V.1)= exponentL P R (flashA s V.1):=by
 unfold exponentL; rw [map_sum]; conv_rhs=>rw [←Equiv.sum_comp (scope_q s)]
 apply sum_congr rfl; intro j _
 rw [loan_v _ P j _ V rfl,loan_v _ P (scope_q s j) _ (yellA s V) rfl,show (pingS P.threshold (scope_q s j).val.2 (yellA s V).1) ↔_ from glowA _ _ _ _]; split; swap; exact map_zero (suit_Y s)
 change suit_Y s (suit_Y s⁻¹ _)= _; rw [moon_Y,inv_mul_cancel,toon_Q]; rfl
lemma light_D(V:Orbit n): exponentL P (writ_E R) V.1= plight_C n • (∑ i:T0,suit_Y i⁻¹ (exponentL P R (flashA i V.1))):=by
 simp_rw [←force_r P _ R V,moon_Y,mul_inv_cancel,toon_Q]; unfold exponentL; rw [smul_sum]; simp_rw [smul_sum]; rw [sum_comm (s:=(univ:Finset T0))]; refine sum_congr rfl fun i _=>?_ ; simp only [loan_v V.1 _ _ _ V rfl]; split; next h=> simp only [Finset.sum_apply, Pi.smul_apply];
 next h=>simp
end YM.CF.Ione
