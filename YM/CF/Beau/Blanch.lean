import YM.CF.Beau.Clin
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Beau
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
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Ione Larch
open Taxi Geo RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup
local notation "Hz"=> Scree.Hub n
open Trees
open Salt
variable(P:BudgetPoint)(T:RegBudget n)(s:Sweep n)
local notation "I"=> scope_q s
local notation "V'"=> suit_Y s
lemma terrain (X₀:Hz):stateT (scope_q s X₀)= scope_q s (stateT X₀):=by
 refine Subtype.ext (Prod.ext rfl ?_); let o:= moveHub s X₀; change villa o=(villa X₀).map (boxA s).symm.toEmbedding
 ext x; rw [Finset.mem_map_equiv]; unfold villa; rw [mem_union,mem_union,halo_spec,halo_spec]; refine or_congr ?_ ?_; exact Finset.mem_map_equiv
 simp only [mem_singleton,exists_eq_left]; rw [(chart_p s X₀).1, ←sitA,Equiv.symm_symm,sitT]
lemma task_h(A: RegBudget n)(X:Hz)(V:Pane n):cut_V (porch A X V)=0:=oqua _
lemma hail_F(U:RegBudget n)(X:Hz)(V:Pane n): cut_V (mowR U X V)=cut_V (U X V):=by unfold mowR; rw [Pi.sub_apply, Pi.sub_apply,map_sub,map_sub, task_h]; change cut_V _-0- cut_V (bankT _ _ _)= _; rw [show cut_V (bankT U X V)= 0 from oqua _,sub_zero,sub_zero]
variable(q:∀ (s:Sweep n) X V,T (moveHub s X) (flashA s V)= suit_Y s (T X V))
include q
lemma urn_k: Sym_P (head_L (Coil T)):=by
 intro s; apply funext; intro X; apply funext; intro U; let o:=moveHub s X; let V:=flashA s U
 change suit_Y s⁻¹ (cut_V ((∑ i:Hz with stateT i=o,mowR T i) V))=cut_V ((∑ i:Hz with stateT i=X,mowR T i) U)
 simp only [Finset.sum_apply,map_sum,hail_F]; symm; refine sum_equiv (scope_q s) ?_ ?_ -- notation issue shadow section
 · intro i; simp only [mem_filter,mem_univ,true_and]; rw [terrain]; change _ ↔ (scope_q s) _=(scope_q s) _; exact (scope_q s).injective.eq_iff.symm
 intro i p; rw [show T (scope_q s i) V= _ from q s i U]; change blind_E _= suit_Y s⁻¹ (blind_E _); rw [show blind_E (suit_Y s _)= _ from sanct_E ..,moon_Y,mul_inv_cancel,toon_Q]
lemma mote_X(X:Hz)(D:Support (More n))(i:Xo)(V: Orbit n):cut_V (say_t T X D i V)=0:=by
 unfold say_t; split; exact map_zero cut_V
 unfold oV page; rw [mon_v]; exact oqua _
lemma palp_V (X:Hz)(D: Support (More n))(U: Orbit n):cut_V (Taxi.peelR T X D U)= if Disjoint D X.val.2 then cut_V (T X U.1) else 0:=by
 unfold peelR; rw [Pi.sub_apply,Pi.sub_apply,Finset.sum_apply,map_sub,map_sub,map_sum,sum_eq_zero (fun j _=> mote_X T q X D j U),sub_zero]; unfold oV Vow.flick; rw [task_h,sub_zero]; split_ifs; rfl; exact map_zero cut_V -- tune
lemma order_B:Sym_M (veil_M (voids T)):=by
 intro s; apply funext; intro i; apply funext; intro D; apply funext; intro V; let U:=actY s D; let W:= moldA s i; let h:= yellA s V; change suit_Y s⁻¹ (cut_V ((∑ j:Scree.Hub n,pamE T j) W U h))= cut_V ((∑ j:Scree.Hub n,pamE T j) i D V)
 simp only [Finset.sum_apply,map_sum]; symm; refine sum_equiv (scope_q s) (fun j=> by simp) fun j x=>?_ ; let H:= scope_q s; let z:=H j
 have hp: pur (stateT z)= moldA s (pur (stateT j)):= by rw [show stateT z=H _ from terrain s j]; rfl
 by_cases v:i=pur (stateT j); swap; · unfold pamE chasmR; rw [Pi.single_eq_of_ne v,Pi.single_eq_of_ne (show W ≠ pur (stateT z) from fun k=> v ((moldA s).injective (k.trans hp)))]; change cut_V 0= suit_Y s⁻¹ (cut_V 0); rw [map_zero,map_zero]
 rw [show pamE T j i=peelR T j from (by unfold pamE chasmR; rw [v,Pi.single_eq_same])]
 have ht:pamE T z W=peelR T z:=by unfold pamE chasmR; rw [show W=pur (stateT z) from (congrArg (moldA s) v).trans hp.symm, Pi.single_eq_same]
 rw [ht, palp_V T q,palp_V T q]; split_ifs with y k k
 · rw [show T z h.1=suit_Y s (T j V.1) from q s j V.1]; change blind_E _=suit_Y s⁻¹ (blind_E _); rw [show blind_E (suit_Y s _)= _ from sanct_E ..,moon_Y,mul_inv_cancel,toon_Q]
 · exact False.elim (k ((Finset.disjoint_map _).2 y))
 · exact False.elim (y ((Finset.disjoint_map _).1 k))
 rw [map_zero]
end YM.CF.Beau
