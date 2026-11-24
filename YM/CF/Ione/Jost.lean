import YM.CF.Ione.Cover
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
-- compensate shift arcs and transfer Mask. Spin lift. kernel-oriented supports.
abbrev force_V(s:Sweep n)(K:Cusp n): Cusp n:= fun i D=> turn_V s (K (moldA s i) (actY s D))
abbrev Sym_a(F:Pax n):Prop:=∀ s:Sweep n,∀ X:Aura n,∀ V:Orbit n,F (moldA s X) (yellA s V)= suit_Y s (F X V)
abbrev Sym_M(K:Cusp n):Prop:=∀ s:Sweep n,force_V s K=K
abbrev Mono_W(K:Cusp n):Prop:=∀ (X:Aura n) (D:Support (More n)),D.Nonempty→ D⊆X.val→∀ v:Orbit n,wage_Q 2 (K X D v)=K X D v -- binder tune implicit
abbrev writ_K(K:Cusp n):Cusp n:=plight_C n • (∑ s:Sweep n,force_V s K)
variable (v:Aura n→ℝ)
abbrev zeal_F(s:Sweep n)(v:Aura n→ℝ):Aura n→ℝ:= v ∘ moldA s
lemma call_Q(o:Seat n):tallB (zeal_F s v) k a (boxA s o)=tallB v k a o:=by
 unfold tallB; refine sum_equiv (moldA s) ?_ ?_
 · intro i; change _ ↔ _; simp [moldA,actY] -- tune cast shadow
 intro i _; unfold zeal_F Trees.currency; rw [show coverNumber k (moldA s i).val= _ from glow_q s k i.val]; rfl
lemma hush_k(s t:Sweep n)(p:Aura n): moldA t (moldA s p)=moldA (s*t) p:=Subtype.ext (tape_B ..)
lemma spin_M: Sym_M (writ_K K):=by
 intro s; apply funext; intro i; apply funext; intro D; apply funext; intro V; unfold writ_K; simp only [force_V,turn_V,Pi.smul_apply, Finset.sum_apply,Function.comp_apply, map_smul,hush_k,tape_B, yell_t,map_sum,moon_Y]; refine congrArg _ ?_; conv_rhs=>rw [←Equiv.sum_comp (Equiv.mulLeft s)]
 refine sum_congr rfl fun i _=>?_ ; rw [show Equiv.mulLeft s i=s*i from rfl,mul_inv_rev]
open AnalyticBridge.GaussianFieldAlignment Locations
lemma skew_V(U:Pane n)(x:ℝ)(p:Rue.FleetS x U): FleetS x (flashA s U):=by
 intro i; let s':=s.s; let b:=(assembly n).embed s.b; let V:= pull s.s b U
 let Z:=shiftFaces s.s b; have he : Pressure.toll V i=Pressure.toll U (Z i):=Face.send_price U i s.s b _ SU.group.chord_inv fun u w=> SU.group.chord_conj w u
 have hp: Pressure.toll (flashA s U) i=Pressure.toll U (Z i):=by rw [revoke]; generalize s.charge=q; cases q; exact he; exact (Rink.mint_b V i).trans he -- tune
 change Pressure.toll _ _≠_; rw [hp]; exact p _
local notation "Vs"=> yellA s
variable (Z:Orbit n)
lemma flame_P(X:Aura n):fuelH (flags P.threshold (Vs Z).1) (moldA s X) ↔ fuelH (flags P.threshold Z.1) X:=by
 unfold fuelH; change ¬Disjoint _ _ ↔ _; change ¬Disjoint _ (flags P.threshold (flashA s Z.1)) ↔_ ; rw [flagsA]; exact not_congr (Finset.disjoint_map _)
lemma bean_H : suit_Y s (fuelV P (force_V s K) Z)=fuelV P K (yellA s Z):=by
 unfold fuelV; rw [map_sum]; refine sum_equiv (moldA s) (fun i=>by simp only [mem_filter,mem_univ,true_and]; exact (flame_P P s Z i).symm) (fun i x=>?_) -- tune order
 let X:= flags P.threshold Z.1; let U:= X∩i.val; let Y:= moldA s i; have hp: flags P.threshold (Vs Z).1 ∩ Y.val=actY s U:=by rw [show flags P.threshold _= _ from flagsA s Z.1 P.threshold]; exact (Finset.map_inter ..).symm -- orientation intersection order
 unfold force_V turn_V; simp only [Function.comp_apply,moon_Y,inv_mul_cancel,toon_Q]; rw [hp]
lemma polar_k : fuelV P (writ_K K) Z= plight_C n • (∑ i:T0,suit_Y i⁻¹ (fuelV P K (yellA i Z))):=by
 simp_rw [← bean_H P _ K Z,moon_Y,mul_inv_cancel,toon_Q, ←tunes Z]; unfold fuelV; rw [smul_sum]; exact sum_congr rfl fun i _=>rfl -- tune implicit
lemma poles_s(p:Sym_a F) : coldE P F (Vs Z)= suit_Y s (coldE P F Z):=by
 symm; unfold coldE; rw [map_sum]; refine sum_equiv (moldA s) (fun i=>by simp only [mem_filter,mem_univ,true_and]; exact (glowA ..).symm) fun i _=> (p _ _ _).symm
abbrev pack_Q(r:ℕ):ℝ:=(fare_T 2:ℝ)*strive_E r
abbrev pony_R(k:ℕ)(v:Aura n→ℝ):=plight_C n • (pack_Q k • (∑ s:Sweep n,zeal_F s v))
lemma memo_P (v:Aura n→ℝ)(P:BudgetPoint)(p:Larch.Anuk K v P h)(t:Mono_W K)(hx:0≤h): Larch.Anuk (writ_K K) (pony_R P.order v) P h:=by
 let E:= ∑ s:Sweep n,zeal_F s v; have hu:0≤pack_Q P.order:= by unfold pack_Q strive_E composeCost; positivity
 refine ⟨smul_nonneg (envy n).le (smul_nonneg hu (sum_nonneg fun s _ i=>p.1 (moldA s i))),fun i D x p'=>?_⟩
 unfold pony_R; rw [Pi.smul_apply,Pi.smul_apply, smul_eq_mul,smul_eq_mul, Finset.sum_apply,mul_sum]; let J:= ∑ s:Sweep n,force_V s K
 have hf(s:Sweep n): Medal P i.val D (force_V s K i D) h (pack_Q P.order * zeal_F s v i):=by
    let T:=moldA s i; let X:= actY s D; let W:= K T X; have ht:X.Nonempty:=map_nonempty.mpr x; have hQ:X ⊆ T.val:= map_subset_map.mpr p'; have hp: W=feast_C W:=funext fun V=>(t _ _ ht hQ _).symm
    change Medal P i.val D (turn_V s W) h _; rw [hp]; exact (by rw [pack_Q,mul_assoc]; exact medal_Q P i.val D s (p.2 T X ht hQ) hx)
 have hk:=Medal.sumP univ (fun s:Sweep n=> force_V s K i D) _ (fun i _=>hf i)
 let Z:= hk.rum (plight_C n); rw [Real.norm_of_nonneg (envy n).le] at Z; unfold writ_K; rw [Pi.smul_apply,Pi.smul_apply,Finset.sum_apply,Finset.sum_apply]; exact Z
lemma family_Q (u:∀ i:Seat n,tallB v k a i≤c)(l:ℕ)(o:Seat n): tallB (pony_R l v) k a o≤pack_Q l*c:=by
 have hp:0≤ pack_Q l:=by unfold pack_Q strive_E composeCost; positivity
 unfold pony_R; rw [tall_s,tall_s]; have hx:tallB (∑ i:Sweep n,zeal_F i v) k a o=∑ i:Sweep n,tallB (zeal_F i v) k a o:=by unfold tallB; simp_rw [Finset.sum_apply,sum_mul]; exact sum_comm
 rw [hx]; have ht(i:Sweep n): tallB (zeal_F i v) k a o≤c:=by apply le_trans _ (u ((boxA i).symm o)); exact le_of_eq (by rw [←call_Q (k:=k) i v ((boxA i).symm o), Equiv.apply_symm_apply])
 refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=>ht i)) hp) (envy n).le) ?_; simp only [sum_const,card_univ,nsmul_eq_mul]; rw [mul_left_comm, feed]
end YM.CF.Ione
