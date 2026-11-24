import YM.CF.Pso.Fume
import YM.CF.Ione.Lean
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
variable (E:Pax n)(F:Pax n)(K:Cusp n)
local notation "T0"=> Sweep n
local notation "Γ"=> (plight_C n)
local notation "Hz"=> Scree.Hub n
local notation "B'"=> P.B
local notation "P'"=> (P.supportExponent+1+1)
structure Trim_P(P:BudgetPoint)(F:Pax n)(K:Cusp n)(h Lc dK dt γ:ℝ)(a:ℝ)(R':RegBudget n)(Z:Cusp n):Prop where
 render: ∃ (A v:Aura n→ℝ)(C:blazeK n), Ready Palot.stern P.B A (P.supportExponent+1+1) γ 1 (degreePrice P.B γ 1) ∧ (∀ X, Medal P X.val ∅ (F X) h (A X)) ∧ Anuk Z v P h ∧ (∀ i:Seat n,tallB v P.B (P.supportExponent+1+1) i ≤ Lc) ∧ ZealQ Z ∧ Sym_a F ∧ ZealQ K ∧ ArmsK P K C h ∧ (∀ i:Seat n,tallB (Vow.hymn C) P.B (P.supportExponent+1+1) i ≤ dK) ∧ IncX Utrue R' P h dt ∧ ∀ V:Orbit n,FleetS P.threshold V.1→ coldE P (FeeD P F) V= owed_E n a+exponentL P R' V.1+fuelV P Z V
variable {γ e q α γ' KU:ℝ}{wisp0 c':ℝ}{K':Cusp n}{L:blazeK n}{Q:Aura n→ℝ} (Wp:Wisp P F E h γ c d) (T:ArmsK P K L h)(R:RegBudget n)(u:∀ V:Orbit n,FleetS P.threshold V.1→exponentL P R V.1+fuelV P K' V=coldE P E V)(η0:1≤h)
variable(hU:Sym_P (numbD R))(hk: Mono_W K')(hp:Sym_a F)(ht: ZealQ K)(pc:Sym_a E)
variable(hQ:Anuk K' Q P h)(KB:∀ i:Seat n,tallB Q P.B (P.supportExponent+1+1) i ≤ α)(KK:∀ i:Seat n,tallB (hymn L) P.B (P.supportExponent+1+1+1) i ≤ KU)
variable(v:IncX (fun _=>False) R P h c')
include u pc Wp T η0 hQ v KB KK hU hk hp ht
lemma zeal_t (τ:Ids n): Trim_P P F K h (pack_Q P.order*α+(c+3*d)) KU (wren_K P.order P.power*c'+reserveT P.power P.order P.B 1*(6*d)) γ (∑ i:Aura n,curr_r P E F (1,τ) i) (writ_E R + cast_E (curr_X P E F (1,τ)) τ) (writ_K K'+ nextE (curr_r P E F (1,τ))):=by
 obtain ⟨A,C,LL,q,uF,uG,hW,hL,hC,hv,wU,hh⟩:=(foam P E F Wp η0 hp pc (1,τ) rfl).shape; let PF:=curr_r P E F (1,τ); let W:=curr_X P E F (1,τ); have he(s:Sweep n)(i:Aura n):PF (moldA s i)=PF i:=tally_F s _ i -- variable uses P' reserved notation
 let V:=writ_K K'; let Y:=(pony_R P.order Q); have hA:= memo_P K' Q P hQ hk (zero_le_one.trans η0); let S:= V+ nextE PF
 let Zr:= ∑ i:Aura n,PF i; let hν:=zero_le_one.trans η0; have hx: Anuk S (Y+LL) P h:= by refine ⟨add_nonneg hA.1 (fun i=> (uG i).wage hν),fun i D p t=>?_⟩; exact (hA.2 i D p t).plus (nom_F η0 P i _ (uG i) D)
 have hτ(o:Seat n): tallB (Y+LL) P.B (P.supportExponent+1+1) o≤ pack_Q P.order*α+(c+3*d):=by rw [tall_add]; exact add_le_add (family_Q Q KB _ o) (hL o)
 let R' := writ_E R + cast_E W τ
 refine ⟨⟨A,Y+LL,L,q,uF,hx,hτ,?_,hp,ht,T,?_,Ione.addT P (cup_R P R v hU hν) (worth_R P W τ hh wU hν hW hC),?_⟩⟩ -- ht shadow rename
 · intro s V p i D t v; let g:=tree_y _ (spin_M K') s V i D t v; have hy:nextE PF (moldA s i) (actY s D) (yellA s V) = suit_Y s (nextE PF i D V):=by rw [nextE,he s]; change _=suit_Y s (-(PF i•1)); rw [map_neg,map_smul,map_one]
   exact (congrArg₂ (·+·) g hy).trans (map_add ..).symm
 · intro i; apply (tall_m (b:=P.supportExponent+1+1+1) (Vow.hymn L) _ (le_add_of_nonneg_right zero_le_one) i).trans (KK i); exact fun i=>sum_nonneg (fun j v=> (T.price _ _ (mem_filter.mp v).2.1 (mem_filter.mp v).2.2).wage hν)
 intro V t; have he:coldE P (FeeD P F) V=coldE P (cashV PF+E+W) V:=sum_congr rfl fun i q=>hv _ _ (hates (by rw [sdiff_empty]; exact (mem_filter.mp q).2)); have ht':∑ i:Aura n,owed_E n (PF i)= owed_E n Zr:= (Finset.sum_smul ..).symm; have hP: owed_E n Zr+fuelV P (nextE PF) V=coldE P (cashV PF) V:=by rw [←ht']; exact tall_K P PF V t -- order?
 change coldE P (FeeD P F) V= owed_E n Zr+exponentL P R' V.1+fuelV P S V
 rw [he,crep,crep, ←ironP P E R u pc V t, ←ocean P W τ wU V]; unfold R' S; rw [ripe_H P V _ _,←hP,toast]; abel
end YM.CF.Ione
