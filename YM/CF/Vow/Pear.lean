import YM.CF.Vow.Face
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Vow
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
-- second grade corrections.L General receipt.One-ball log-tail. split off constants or scalar portal. reserve α budgeting.
open Trees Ursell Push.AbsoluteSums.Graph
variable(X:Aura n)(V:Orbit n) {F G U':Pax n}{A:Aura n→ℝ} {B:ℕ} {z u γ δ q:ℝ}
private lemma mass_t (i:Tuple (Aura n) 0):coefficient Palot.gRule i=1:=by
 let R:= SongQ 0; have he : pot gRule i=∅:=eq_empty_iff_forall_notMem.mpr fun j p=> by have hv:= (potential_mem .. |>.mp p).1; have h:=Finset.card_le_univ j; simp only [hv,Fintype.card_option,Fintype.card_fin] at h; omega
 unfold coefficient; rw [he]; unfold Push.AbsoluteSums.Graph.mass connectedGroups; rw [powerset_empty, sum_filter,sum_singleton, if_pos]; simp [alternating]; intro i j; obtain hj : i=j :=Subsingleton.elim ..; rw [hj] -- tune
lemma sheerH(F:Pax n):funge X F 0 0= F X:=by
 have hx(i:Tuple (Aura n) 0):i=(fun _=>i none):=funext fun j=> congrArg i (Subsingleton.elim ..)
 have ht(i:Tuple (Aura n) 0):tideU ⟨0,i⟩=i none:=by nth_rw 1 [hx i]; apply Subtype.ext; change unionOf _ _= _; ext x; simp [unionOf, Palot.stern] -- tune
 unfold funge; let i:Tuple (Aura n) 0:=fun _=>X
 rw [sum_eq_single i, sta,if_pos ⟨(ht i).symm,le_rfl⟩]; swap; · intro j _ g; apply if_neg; exact fun l=>g (by ext x : 1; exact (congrFun (hx j) x).trans (l.1.trans (ht j)).symm)
 rotate_left; · simp
 unfold guava; dsimp only; rw [mass_t]; simp [Fintype.prod_option,i]
variable(t:Ready stern B A c γ δ q)(hy:1≤h)(g:∀ X, Medal P X.val ∅ (F X) h (A X))(p:0≤c)
include t hy g p
lemma raid_r(m:ℕ)(u:visible P X.val ∅ V.1): Summable (fun i=>funge X F m i V):=by
 have hp':= glomM (m:=m) X t p; apply lend (P:=P) (h:=h) (u:=fun i=>∑ j:Tuple (Aura n) i,sepV A X m ⟨i,j⟩) _ _ hy V u; exact fun i=> Medal.sumP _ _ _ (fun j _=> ponder X ⟨i,j⟩ hy g m); simpa using hp'.sigma -- tune unresolved C
lemma past (u:visible P X.val ∅ V.1): FeeD P F X V= F X V+funge X F 0 1 V +spinD P X F 2 V:=by
 unfold FeeD spinD lasting zenS; rw [if_pos u,if_pos u]
 have he:= raid_r X V t hy g p 0 u; have hx:= raid_r X V t hy g p 2 u; dsimp only; rw [← he.sum_add_tsum_nat_add 2,←hx.sum_add_tsum_nat_add 2]
 have ht(i:ℕ): funge X F 0 (i+2)=funge X F 2 (i+2):=by simp [funge,sta]; -- tune nat
 have hr(i:ℕ)(h:i<2): funge X F 2 i=0:=by simp [funge,sta,h.not_ge]
 simp only [ht,sheerH X, Finset.sum_range_succ,hr 0 (by omega),hr 1 (by omega), Pi.zero_apply,sum_range_zero,zero_add] -- rw order sets
-- For any diff at order 2, scaled η: if WV fields BOTH paid by A and F-G by L^-1 small, capture. (applies to F= f from ℓ ledger, G pure constants with HUGE mantle).
omit g
include t p hy
variable (hf:∀ X,Medal P X.val ∅ (F X) h (A X))(hg:∀ X,Medal P X.val ∅ (G X) h (A X))(K:ℝ) (hk:0 < K)(w:∀ X,Medal P X.val ∅ (F X-G X) h (K*A X))
omit t p
include hf hg hk w
lemma sweatL (i: Tuple (Aura n) 1): Medal P X.val ∅ (sta F X 0 (⟨1,i⟩)-sta G X 0 ⟨1,i⟩) h (2*K*sepV A X 1 ⟨1,i⟩):=by
 unfold sta sepV; simp only [Nat.zero_le,le_refl,and_true]; split_ifs with z; swap; · rw [sub_zero,mul_zero]; exact Medal.zeroT
 let y:=i none; let t:=i (some 0); let D:=X.val; have he(j): (i j).val ⊆ D:=by have hp:(i j).val⊆ (tideU ⟨1,i⟩).val:= rimY ⟨1,i⟩ j; unfold D; exact z.symm ▸ hp
 let a:= A y*A t; let U:=F y; let Tz:=F t; let V:=G y; let Y:=G t; have hl :Medal P X.val ∅ (U*Tz-V*Y) h (2*K*a):=by
    have ht:= (hf t).stretchB (he _) (Subset.refl _) (show t.val\ ∅⊆X.val\∅ from by rw [sdiff_empty,sdiff_empty]; exact he _); have hp:= (hg y).stretchB (he _) (Subset.refl _) (show y.val \ ∅ ⊆ X.val \∅ from by simp only [sdiff_empty]; exact he _)
    have hu(d:Option (Fin 1)): Medal P X.val ∅ (F (i d)-G (i d)) h (K*A (i d)) :=(w _).stretchB (he _) (Subset.refl _) (by rw [sdiff_empty,sdiff_empty]; exact he _)
    have h:=zero_le_one.trans hy; rw [show U*Tz-V*Y=(U-V)*Tz+V*(Tz-Y) from (by ring), show 2*K*a= _ from (by unfold a; exact (show _= (K*A y)* A t + A y * (K*A t) from by ring))]; exact Medal.plus ((hu _).cross ht h) (hp.cross (hu _) h)
 unfold guava Ursell.clusters; dsimp only; simp only [Fintype.prod_option,Fin.prod_univ_succ, Fin.prod_univ_zero,mul_one]; rw [←smul_sub]; refine (hl.rum _).big ?_; rw [norm_div,Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]; exact le_of_eq (by unfold a y t; ring)
include t p
lemma tenderH : Medal P X.val ∅ (funge X F 0 1-funge X G 0 1) h (2*K*spanD X A 1):=by
 unfold funge; rw [←sum_sub_distrib]; apply (Medal.sumP _ _ _ (fun i _=> sweatL X hy hf hg K hk w i)).big; rw [←mul_sum]; refine mul_le_mul_of_nonneg_left ?_ (by positivity); have hp:= glomM (m:=1) X t p
 rw [spanD,hp.tsum_sigma]; let Z(i:ℕ):=∑ j:Tuple (Aura n) i, sepV A X 1 ⟨i,j⟩; simp_rw [tsum_fintype]; have hb:Summable Z:=by simpa only [tsum_fintype] using hp.sigma
 exact hb.le_tsum 1 (fun i _=> sum_nonneg (fun j _=> by unfold sepV; split; exact clusters_nonneg gRule t.2.2.2.2.1 _; exact le_rfl))
end YM.CF.Vow
