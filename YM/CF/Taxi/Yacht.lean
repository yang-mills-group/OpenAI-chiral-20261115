import YM.CF.Taxi.Camp
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
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
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations StressFlux AnalyticBridge.VerifiedReset Push.Local
open Vow Rue
variable(T:RegBudget n)(F:InkD n)(X0: Scree.Hub n){U':Scree.Hub n→ℝ}
variable (p: Pant T)
local notation "Tx"=> (T X0)
local notation "N"=> (Single n)
local notation "Gp"=> SU.group
local notation "Xr"=> X0.val.2
local notation "o"=> X0.val.1
local notation "W_"=> villa X0
variable (g:∀ X, PressB P X (T X) h (U' X))(hw: 0≤h)(A:DayT P.order a)(ha:0≤a)(ht:60 < (More n).val)
abbrev pur (S:Scree.Hub n): Vow.Aura n:=⟨S.val.2,⟨_,S.property⟩⟩
-- masked scalar share paid on footprint.X.Al all. protect Site threshold separately even if outside flag marker. neg α path.
abbrev page(i:Site (More n))(U:Pane n): Cipher n:= moldV n (fuelC X0 (realH T X0) i U)
abbrev say_t(X:Scree.Hub n)(D:Support (More n))(i:Site (More n)): Copy n:= if i∈D then 0 else oV (page T X i)
def peelR (X:Scree.Hub n)(D: Support (More n)): Copy n:= Vow.flick (pur X) (oV (T X)) D - oV (porch T X) - ∑ i: Site (More n), say_t T X D i
def pamE(X:Scree.Hub n): Cusp n:= Vow.chasmR (pur (stateT X)) (peelR T X)
include p ht g A ha hw
private lemma sailC (i:Site (More n)) (V: Pane n):page T X0 i V=moldV n (motto X0.val.1 i* counter (fluxP X0 (realH T X0)) i V):=rfl
private lemma poolC(V:Pane n): (∑ i: Site (More n), page T X0 i V)=bankT T X0 V:=by
 unfold page bankT payout; rw [Finset.sum_apply,←map_sum (moldV n)]; exact mon_v ..
omit p ht
private lemma costPL(i: Site (More n)): AnalyticBridge.VerifiedReset.Bill P i (Healthy P.threshold {i}) (motto o i*tollV P (‖Complex.reCLM‖*U' X0)) (fuelC X0 (realH T X0) i):=by -- Op not defined; Taxi.Mile cost_p private. adapt
 let L:= realH T X0; have hx:=cashR Tx X0 (g X0) hw Complex.reCLM ‖Complex.reCLM‖ le_rfl
 have hp:AnalyticBridge.VerifiedReset.Bill P i (Healthy P.threshold {i}) (tollV P (‖Complex.reCLM‖*U' X0)) (counter (G:=SU.group) (fluxP X0 L) i):=by
    let C:= ‖Complex.reCLM‖*U' X0; apply AnalyticBridge.VerifiedReset.Bill.le (counter_bill (G:=SU.group) i (fluxP X0 L) P); unfold tollV; refine mul_le_mul_of_nonneg_left ?_ (by norm_num);
    have he :∑ i:PlaqAxes,∑ j:PlaqAxes,C*pairBill SU.group P=(Fintype.card PlaqAxes:ℝ)*((Fintype.card PlaqAxes:ℝ)*(C*pairBill SU.group P)):=by simp
    refine (sum_le_sum fun i _=>sum_le_sum fun j _=>?_).trans he.le; rw [mul_comm (pairBill SU.group P),← mul_assoc,mul_comm |fluxP X0 L _ _|]; exact mul_le_mul_of_nonneg_right (payC X0 hx _ _) (pair_nonneg ..)
 have ht:=AnalyticBridge.VerifiedReset.Bill.mul_left (motto o i) hp; rw [abs_of_nonneg (mot_l ..)] at ht; exact ht
-- count preserving via fee paid through normalized flags any.D; porch const when F-Flags
private lemma scale_u {C:ℂ}(i:Site (More n))(h:i∉D)(u:motto o i ≠0): ThemeR W_ (oV (page T X0 i)):=by
 let H:= holdS (F:=realH T X0) X0 i (P:=P); let L:=moldV n; let Q:=fuelC X0 (realH T X0) i
 refine ⟨fun t v h y=> congrArg L (H.sites t.1 v.1 h),fun i=>?_ ,L.continuous.measurable.comp (H.borel.comp measurable_fst),fun V U=>?_⟩ -- tune binders
 · change Flour _ (moldV n (Q i.1)).val; rw [mon_v]; exact Flour.grainE.smul _
 change L (Q (Lattice.gauge U V.1)) = paintR false false (tradew n U) (L (Q V.1)); rw [show Q _=Q _ from H.symmetry U V.1]; change _ = paintR false false _ ((Q V.1) • (1:Cipher n)); rw [map_smul,map_one]; rfl
private lemma mentor_j (i:Site (More n)) : Vow.Medal P W_ D (say_t T X0 D i) h ((P.order+1:ℝ)*liteV P (a*(motto o i*tollV P (‖Complex.reCLM‖*U' X0)))):=by
 let Q:=fuelC X0 (realH T X0) i; let C:=motto o i*tollV P (‖Complex.reCLM‖*U' X0); let G:=a*C; let Z:=liteV P G; let V':= (P.order+1:ℝ)*Z; have hp:= costPL T X0 g hw A ha i; have hv:0 ≤ V':=mul_nonneg (by positivity) (mint_p _ _ (mul_nonneg ha hp.nonneg)); unfold say_t; split; exact Vow.Medal.zeroT.big hv
 rename_i t; by_cases w:motto o i=0; · rw [show oV (page T X0 i)=0 from funext fun x=> (by change moldV n _= _; unfold fuelC; simp_rw [w,zero_smul,Pi.zero_apply,map_zero])]; exact Vow.Medal.zeroT.big hv
 have hh:i∈ W_:= shipT _ _ w (halo_subset 2 {i} (mem_singleton_self _)) -- tune
 refine ⟨scale_u T X0 g hw A ha i (C:=0) t w, Pi.single ∅ V',fun i=>by rw [Pi.single_apply]; split_ifs; exact hv; exact le_rfl ,fun i' p Y m=>?_,?_⟩ -- targets
 · have he : Healthy P.threshold {i} i'.1:= ping_le (grow_b (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨hh,t⟩)) p); let V:=i'.1; let U:= ((Complex.ofRealCLM ∘ Q) ∘ pressQ P Y V); have hw:Allows P.order U 0 Z:= mintK _ _ _ (A _ _ _ _ _ _ hp rfl V he); have hk:= Rue.bare_p _ _ hw; refine (Woody.chit (∅:Finset (Dwell n)) hk).germ ?_; filter_upwards with x; change _= (moldV n (Q (pressQ _ _ _ x))).val; rw [mon_v]; unfold Pastry.poke; rw [Poly.tag_void]; rfl
 simp [joinV,Pi.single_apply,mul_ite,stake,V',Z,G,C]
def blazeP (P:BudgetPoint)(q x:ℝ):= (2:ℝ)*Vow.chi_f P.order*x+(P.order+1:ℝ)*liteV P (q*tollV P (‖Complex.reCLM‖*x)) -- Porch.Pq $T with flags.App Expense tricky: porch `V constant` even if V flagged.Port.Coordinate requires extension within Ω.H^_D: use const.W.U receipt.
lemma pearlZ (D: Support (More n)): Vow.Medal P (villa X0) D (peelR T X0 D) h (blazeP P a (U' X0)):=by
 let K:= U' X0; let C:= Vow.chi_f P.order*K
 have hx: Vow.Medal P W_ D (oV (porch T X0)) h C:=by
    obtain ⟨V,c,h,p⟩:= (Vow.rimR (pureP T X0 g hw) hw).pays; let W:= oV (porch T X0); refine ⟨((Vow.rimR (farther_v T _ X0 g hw (stateT X0) (s:=pureP T X0 g hw) Finset.subset_union_left rfl) hw).toThemeR),V,c,fun i p Y m=>?_ ,p⟩ -- Wrong. can stretch Theme only then const. rewrite.
    exact h (1,i.2) (by simpa only [sdiff_empty] using ping_f P Xr) (empty_subset Y)
 unfold peelR; rw [sub_eq_add_neg,sub_eq_add_neg]
 let L:=Vow.flick_M (pur X0) (pur (stateT X0)) Finset.subset_union_left hw (Vow.rimR (g X0) hw) D
 apply Vow.Medal.big ((L.plus hx.negT).plus (Vow.Medal.sumP _ _ _ (fun i _=> mentor_j T X0 g hw A ha i)).negT); -- tune syntax
 let B:=a*tollV P (‖Complex.reCLM‖*K)
 rw [Finset.sum_congr rfl (fun i u=> show ((P.order+1:ℝ)*liteV P (a*(motto o i*tollV P (‖Complex.reCLM‖*K))))=motto o i*((P.order+1:ℝ)*liteV P B) from (by rw [mul_left_comm a,scaleV,mul_left_comm])),←Finset.sum_mul,mot_b,one_mul]; change (C+C)+(P.order+1:ℝ)*liteV P B ≤ (2:ℝ)*chi_f P.order*K+_; unfold B C; exact le_of_eq (by unfold K; ring)
include p ht
local notation "tP"=> P.threshold
variable(U₁:Skye.Orbit n)(uF:FleetS P.threshold U₁.1)
local notation "Ω"=>flags P.threshold U₁.1
abbrev CoatL(T:RegBudget n)(P:BudgetPoint)(x:Skye.Orbit n)(i: Scree.Hub n):= Vow.march P (pur (stateT i)) (oV (mowR T i)) x
include uF
-- point by point. Kernel/R conservation. Low shape canonical.Budget.
lemma erosion_v : Vow.march P (pur X0) (oV Tx) U₁= porch T X0 1+ (∑ i:Site (More n), if Healthy tP {i} U₁.1 then page T X0 i U₁.1 else 0)+ fuelV P (pamE T X0) U₁+CoatL T P U₁ X0:=by
 have hxT(i:Site (More n))(p:motto X0.val.1 i=0):page T X0 i U₁.1=0:=by unfold page fuelC; rw [p, zero_smul]; exact map_zero _
 let M:= pur (stateT X0); let D:= Ω ∩ M.val; unfold CoatL pamE; simp_rw [Vow.march_f U₁ uF, shade_t]; by_cases h:Disjoint M.val Ω
 · rw [if_neg (show ¬fuelH Ω M from not_not.mpr h),if_pos h.symm, if_pos (Disjoint.mono_right (show Xr⊆M.val from Finset.subset_union_left) h.symm)] -- tune
   have hp(i:Site (More n))(v: i∈ M.val):Healthy tP {i} U₁.1:= Disjoint.mono_left (singleton_subset_iff.mpr v) h; rw [sum_congr rfl (fun i t=> ?_),poolC T X0 p g hw A ha ht U₁.1]
   · change Tx U₁.1= porch T X0 U₁.1+ bankT T X0 U₁.1+0+((Tx U₁.1-porch T X0 U₁.1)-bankT T X0 U₁.1); abel
   split; rfl
   rename_i v'; symm; refine hxT i (by_contra fun u=>?_); exact v' (hp _ (shipT _ _ u (halo_subset 2 _ (mem_singleton_self _))))
 rw [if_neg (show ¬Disjoint Ω M.val from fun l=>h l.symm),if_pos (show fuelH Ω M from h)]; unfold peelR; simp only [Pi.sub_apply,Finset.sum_apply,add_zero]
 have he(i:Site (More n)): say_t T X0 D i U₁ = if Healthy tP {i} U₁.1 then page T X0 i U₁.1 else 0:=by
    unfold say_t; split
    next p=>rw [if_neg]; rfl; exact fun q=> Finset.disjoint_left.mp q (mem_singleton_self _) (mem_inter.mp p).1
    next p=>split; rfl
            next v=> refine hxT i (by_contra fun u=>?_); have hp:i∈M.val:=shipT X0 i u (halo_subset 2 _ (mem_singleton_self _)); exact p (mem_inter.mpr ⟨by simpa [Healthy] using v,hp⟩)
 rw [sum_congr (f:=fun i=> say_t T X0 D i U₁) rfl (fun i _=>he i)]; let V:=fun i:Site (More n)=> if Healthy tP {i} U₁.1 then page T X0 i U₁.1 else 0; let R:=∑ i,V i
 have hv: Disjoint D X0.val.2 ↔ Disjoint Ω X0.val.2:=by
    constructor
    · intro h; exact Finset.disjoint_left.mpr fun i p v=> Finset.disjoint_left.mp h (mem_inter.mpr ⟨p,mem_union_left _ v⟩) v
    exact fun q=>Disjoint.mono_left Finset.inter_subset_left q
 unfold Vow.flick
 split_ifs with y v v
 · change Tx U₁.1=porch T X0 1+ R+((Tx U₁.1-porch T X0 1)-R); abel
 · exact False.elim (v (hv.2 y))
 · exact False.elim (y (hv.1 v))
 change 0=porch T X0 1+ R+((0-porch T X0 1)-R); abel
-- header aggregate
lemma outflow : (∑ x:Scree.Hub n,Vow.march P (pur x) (oV (T x)) U₁)= (∑ i:Scree.Hub n,porch T i 1)+moldV n (lureC (realH T)*∑ i:Site (More n),AnalyticBridge.VerifiedReset.heads P i U₁.1) + ∑ i:Scree.Hub n, (fuelV P (pamE T i) U₁+CoatL T P U₁ i):=by
 rw [sum_congr (s₁:=univ) rfl (fun i _=> erosion_v T i p g hw A ha ht U₁ uF)]; simp only [sum_add_distrib]; rw [← add_assoc]; congr 2; rw [sum_comm,Finset.mul_sum,map_sum]; congr 1; apply sum_congr rfl; intro i _; by_cases h: Healthy tP {i} U₁.1
 · simp only [if_pos h,page,← map_sum]; apply congrArg; rw [gloryT T p hw g ht]; rw [AnalyticBridge.VerifiedReset.heads, masked_eq _ _ _ _ h]
 simp only [if_neg h,AnalyticBridge.VerifiedReset.heads, masked_ne _ _ _ _ h,mul_zero,map_zero,sum_const_zero]
end YM.CF.Taxi
