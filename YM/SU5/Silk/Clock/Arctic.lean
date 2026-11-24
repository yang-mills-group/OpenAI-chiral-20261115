import YM.SU5.Silk.Clock.Lane
import YM.SU5.Silk.Clock.Medal
import YM.SU5.Silk.Clock.Stater
import YM.CF.Brood.Tips
import YM.CF.Ione.Tape
import YM.CF.Hype.Ace
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Trails
import YM.ProjectorNext.PROJECTOR_EQUIVARIANCE.Links
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Ione.Clock
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
open Bake Lilt Rue Trees Taxi Moto Neon Haro Tap Py
open Hove Mew Larch
variable (s:Sweep n)
abbrev dashK(s:Sweep n)(K:Cusp n):= force_V s⁻¹ K
lemma y_rev(s:Sweep n)(U:Orbit n): yellA s⁻¹ (yellA s U)=U:=by
 refine Prod.ext (revB ..) ?_
 exact tuftT s U.2
lemma dash_apply(s:Sweep n)(K:Cusp n)(i:Aura n)(D:Support (More n))(v:Orbit n): dashK s K (moldA s i) (actY s D) (yellA s v)=suit_Y s (K i D v):=by
 unfold dashK force_V turn_V; simp only [Function.comp_apply, inv_inv,y_rev,tape_C, show moldA s⁻¹ (moldA s i)=i from Subtype.ext (tape_C s i.val)]
lemma dash_Ek(s:Sweep n)(q:Orbit n)(R:RegBudget n):exponentL P (dashF s R) (flashA s q.1)=suit_Y s (exponentL P R q.1):=by
 have h:= force_r P s⁻¹ R (yellA s q); change suit_Y s⁻¹ _=exponentL P R (yellA s⁻¹ (yellA s q)).1 at h; rw [y_rev] at h; rw [←h,moon_Y,inv_mul_cancel,toon_Q]
lemma dash_Ck(s:Sweep n)(q:Orbit n)(R:Cusp n):fuelV P (dashK s R) (yellA s q)=suit_Y s (fuelV P R q):=by
 have h:= bean_H P s⁻¹ R (yellA s q); rw [y_rev] at h; rw [←h,moon_Y,inv_mul_cancel,toon_Q]
lemma suit_cost(s:Sweep n)(z:ℂ)(q:Cipher n):suit_Y s (z • q)=Spire.payZ s z • suit_Y s q:=by
 apply Subtype.ext; let U:= siteU (castX s) s.charge (spinU s.charge s.s) n; change Scree.sauce _ _ U (z • q.val)=Spire.payZ s z • _; unfold Scree.sauce; rw [singT,win_c,twist_scalar]<;>rfl
lemma orbital_phase(s:Sweep n)(z:ℂ):‖Spire.payZ s z‖=‖z‖:=by unfold Spire.payZ; cases wageZ s<;>simp [cSignX]
variable {N B:Side}
local notation "mH"=> mid N B
local notation "aH"=> Aura mH
variable (q:Sweep (mid N B))(g:q∈ Whirl (mid N B))(o:Site (mid N B))(V T:Copy (mid N B))(E:RegBudget (mid N B))(K:Cusp (mid N B))(A:ArcΦ)(t:ℂ)(u v w c':ℝ)
variable (hi:∀ x:Orbit (mid N B),T (yellA q x)=suit_Y q (V x))
variable (hn:∀ i:Scree.Hub (mid N B),chose m P i→Nonwrapping i.val.2 i.val.1)(hx:4≤ (More (mid N B)).val)
variable (hg:duty_Q P.order P.power ≤ c')(hv:strive_E P.order≤c')(U:UNI SpinIdx)(ht:JetS q.s false (detX q.s) U)
local notation "W"=> dashK q K
local notation "Z_"=> dashF q E
local notation "C_"=> P.supportExponent+1+1
lemma iceBoat (z:0≤h)(u0:0≤u)(i:Ice m (mPath q o) P h u v w V E K t A)(hn:∀ i:Scree.Hub (mid N B),chose m P i→Nonwrapping i.val.2 i.val.1)(hx:4≤ (More (mid N B)).val)(g:q∈Whirl (mid N B))(hg:duty_Q P.order P.power ≤ c')(hv:strive_E P.order≤c')(U:UNI SpinIdx)(ht:JetS q.s false (detX q.s) U)(hi:∀ x:Orbit (mid N B),T (yellA q x)=suit_Y q (V x)): Ice m o P h (c'*u) (c'*v) w T (dashF q E) (dashK q K) (Spire.payZ q t) (arc_s q.s U A):=by
 -- choose
 refine ⟨turf_A m o P _ _ _ _ (mul_le_mul_of_nonneg_right hg u0) (facetAx q g E A o i.axle z hn hx U ht), ?_,?_,?_,?_⟩ -- replace
 · rw [orbital_phase]; exact i.phase
 · intro x p
   let Y:=moldA q⁻¹ x; have he(u:Seat mH)(h:u∈Y.val): (boxA q⁻¹) u∈x.val:=Finset.mem_map_equiv.mp h
   have hp:node (mPath q o)∉ Y.val:=fun v=>p (by specialize he _ v; rw [nodeA,sitU,Equiv.symm_apply_apply] at he; exact he)
   funext D s; change suit_Y (q⁻¹)⁻¹ _=0; rw [show K Y=0 from i.stout _ hp,Pi.zero_apply]; exact map_zero _
 · obtain ⟨Q,hQ,fQ,vQ⟩:=i.grant; let L:= c'; have hc: 0≤ L:= le_trans (by unfold strive_E composeCost; positivity) hv; let J:= L • (zeal_F q⁻¹ Q)
   refine ⟨J,⟨fun x=>mul_nonneg hc (hQ.1 _),fun x D u p=>?_⟩,fun x=>?_,fun x p=>?_⟩
   · let E:=moldA q⁻¹ x
     have hk:= full_medal P x.val D q⁻¹ (inv_mem g) (hQ.2 E _ (map_nonempty.mpr u) (map_subset_map.mpr p)) z; exact hk.big (mul_le_mul_of_nonneg_right hv (hQ.1 E))
   · unfold J; rw [tall_s]; apply mul_le_mul_of_nonneg_left _ hc
     have h:=call_Q (k:=P.B) (a:=C_) q⁻¹ Q ((boxA q⁻¹).symm x); rw [Equiv.apply_symm_apply] at h; exact h.trans_le (fQ _)
   let T:=moldA q⁻¹ x; obtain ⟨hv,gx⟩:=vQ T fun q=>p (by change L*Q T=0; rw [q,mul_zero]); have hx:coverNumber P.B T.val= _:= glow_q q⁻¹ P.B x.val
   refine ⟨hx ▸ hv,?_⟩; have hp:(boxA q⁻¹) _∈ x.val:= Finset.mem_map_equiv.mp (show node (mPath q o) ∈ actY q⁻¹ x.val from gx); rw [nodeA,sitU,Equiv.symm_apply_apply] at hp; exact hp
 intro x p; let Z:=yellA q⁻¹ x; have he:yellA q Z=x:= by have h:= y_rev q⁻¹ x; rwa [inv_inv] at h
 have hp:= skew_V q⁻¹ x.1 _ p
 rw [←he,hi,i.wear Z hp, map_add,map_add]; simp only [suit_cost,map_one]; rw [show exponentL P _ _= _ from dash_Ek q Z E, dash_Ck] -- heavy
lemma ice_sc_real (s:ℝ)(z:0≤h)(i:Ice m o P h u v w V E K t A): Ice m o P h (‖s‖*u) (‖s‖*v) (‖s‖*w) (s • V) (s • E) (s • K) (s • t) (s • A):=by
 refine ⟨?_,(norm_smul s t).trans_le (mul_le_mul_of_nonneg_left i.phase (norm_nonneg _)),fun x p=>?_,?_,fun x p=>?_⟩
 · have h':= charge_ν (s:ℂ) m o E A P u z i.axle; rw [Complex.norm_real] at h'; exact h' -- tune rfl
 · rw [Pi.smul_apply,i.stout _ p,smul_zero]
 · obtain ⟨q,h,g,k⟩:= i.grant;
   refine ⟨‖s‖ • q,⟨smul_nonneg (norm_nonneg s) h.1,fun x D u p=>(h.2 _ _ u p).rum s⟩,fun x=>?_,fun x p=> k x fun b=>p (by rw [Pi.smul_apply,b,smul_zero])⟩
   rw [tall_s]; exact mul_le_mul_of_nonneg_left (g _) (norm_nonneg _)
 rw [Pi.smul_apply,i.wear _ p,smul_add,smul_add, show exponentL P (s • E) x.1= _ from voc_E P (s:ℂ) E x, show fuelV P (s • K) x= _ from cul_z P (s:ℂ) K x]; rw [smul_assoc]<;>rfl -- tune implicit
variable {ι:Type}[DecidableEq ι]
lemma ice_sum (S:Finset ι)(F:ι→ Copy mH)(E:ι→RegBudget mH)(K:ι→Cusp mH)(X:ι→ArcΦ)(t:ι→ℂ)(u v w:ι→ℝ)(p:∀ i∈S,Ice m o P h (u i) (v i) (w i) (F i) (E i) (K i) (t i) (X i))(z:0≤ h): Ice m o P h (∑ i∈S,u i) (∑ i∈S,v i) (∑ i∈S,w i) (∑ i∈S,F i) (∑ i∈S,E i) (∑ i∈S,K i) (∑ i∈S,t i) (∑ i∈S,X i):=by
 refine ⟨wave_F S E X u P m o (fun i v=> (p i v).axle) z, (norm_sum_le ..).trans (sum_le_sum fun i v=>(p i v).phase),fun x v=> ?_,?_,fun x v=> ?_⟩
 · rw [Finset.sum_apply]; apply sum_eq_zero; exact fun i u=>(p i u).stout _ v
 · choose! q l₀ l₁ l₂ using fun i u=>(p i u).grant; refine ⟨(∑ i∈S,q i),⟨sum_nonneg fun i u=> (l₀ i u).1,fun x D e f=>?_⟩,fun x=>?_,fun x p=>?_⟩
   · rw [Finset.sum_apply,Finset.sum_apply, Finset.sum_apply]; exact Medal.sumP _ _ _ fun i u=>(l₀ i u).2 x _ e f
   · refine (Eq.le ?_).trans (sum_le_sum (f:=fun i=> tallB (q i) P.B C_ x) fun i u=>l₁ i u x); unfold tallB; simp_rw [Finset.sum_apply,sum_mul]; exact sum_comm
   rw [Finset.sum_apply] at p; obtain ⟨i,s,h⟩:= Finset.exists_ne_zero_of_sum_ne_zero p; exact l₂ i s x h
 rw [Finset.sum_apply,e_s_K,τlump, Finset.sum_smul,← Finset.sum_add_distrib, ←Finset.sum_add_distrib]; exact sum_congr rfl fun i w=>(p i w).wear _ v
end YM.CF.Ione.Clock
