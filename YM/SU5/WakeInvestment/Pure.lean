import YM.SU5.WakeInvestment.Richly
import YM.SU5.WakeInvestment.PriceOnLeaf
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
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

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph

variable {z A c:ℝ}
set_option quotPrecheck false
local notation "L"=> P.R.L
local notation "D"=> P.K.j
local notation "shx" s:max => hat L P.x s
local notation "vℓ" s:max => shieldC (hat L P.x s)
local notation "Ω" s:max i:max => (side Y i s)
local notation "Gξ" s:max i:max k:max => RootBook Y i k s
local notation "ℂk" s:max i:max => (Y.voyage i).CapeT s

open WakeInvestment
local notation "ℰ" s:max => Worth.meterC (shx s)


variable (s i k : ℕ)
local notation "flatP" => spar P.K.j (RootBook Y i k s).J.M (1:Pane (side Y i s))
local notation "N" s:max i:max => side Y i s
local notation "ηP" s:max => Worth.gateC (shx s)
local notation "ptQ" s:max i:max k:max => ((RootBook Y i k s).p)
open Rous


attribute [local instance] opCStarAlgebra

open Lamour.Bridge Celeste Clock Hookah
open Cliplet
open Window
lemma noble_linear (F: FC (Single (side Y i s))) : noble Y s i k F= Lamour.alleyR (mateK (side Y i s)) (flatSea Y s i k) F:=by
 unfold noble; rw [div_eq_mul_inv,mul_comm]; rfl
lemma noble_unit : noble Y s i k 1=1:=by
 let h:=preparedFlat Y s i k; rw [onTicket,(flatShear ..).glow_nil]; let v:=flatSea Y s i k; change inner ℂ v (acts 1 v)=1; rw [act_one,inner_self_eq_norm_sq_to_K]; have hp: ‖v‖=1:=h.2; rw [hp]; norm_num
lemma noble_bound (F: FC (Single (side Y i s)))(t:ℝ) : ‖noble Y s i k F‖ ≤ ‖(WakeInvestment.weighted flatP t (flatShear Y s i k)).glow F‖ := by
 let q:= flatSea Y s i k; rw [onTicket,←flat_part _ (flat_post Y s i k) (flatShear Y s i k) (flatSea Y s i k) (preparedFlat Y s i k) F t]; exact (grain_cap _ _).trans (by rw [(preparedFlat Y s i k).2]; simp)
-- Present 0-error in real part in these *actual* poses.
variable {M B p:ℕ}{C E : ℝ}
structure Hammer (A : Hookah (side Y i s))(m : ℕ)(C:ℝ)(r:ℕ) : Prop where
 owner: AtSupport false A.S A.x
 span: A.S.card ≤ r
 weld: covariant A.x
 literal(x:Fields (side Y i s)) : A.x x=A.x (1,1)
 quiet: noble Y s i k (A.x (1,1))=1
 issue: Cadre (modesIn _ A.S) m C (A.x (1,1)-1)
variable {A:Hookah (side Y i s)} {r : ℕ}
abbrev evenPose := HaloTw P.K.j (side Y i s)
lemma Hammer.turn (p:Hammer Y s i k A M C r)(q:evenPose Y s i)(a:Axis)(z:ℤ) : Hammer Y s i k (A.twistL a z) M C r := by
 let F':=A.twistL a z
 refine ⟨p.owner.refl a z,(card_image_le).trans p.span,covariant_reflected p.owner p.weld z a,fun x=>?_,?_,?_⟩
 · exact congrArg (theta (carR a z (side Y i s))) ((p.literal _).trans (p.literal _).symm)
 · change noble Y s i k (reflMark a z A.x (1,1))=_; rw [noble_linear,mirror_fare a z q (preparedFlat Y s i k) (preparedFlat Y s i k),←noble_linear,p.quiet,star_one]
 change Cadre (modesIn _ _) _ C (theta (carR a z (side Y i s)) (A.x (reflFields a z (1,1))) - 1); rw [pane2]; let U:=carR a z (side Y i s); have ht:= p.issue.march U (refl_modes a z A.S); rw [theta_sub,theta_one] at ht; exact ht
lemma Hammer.replica (p:Hammer Y s i k A M C r)(q:evenPose Y s i){G: Hookah (side Y i s)}(h:Foil A G):Hammer Y s i k G M C r:=by induction h with|base=> exact p|mirror h i z ih=> exact ih.turn Y s _ k q i z

abbrev modeCap (r:ℕ) := r * Fintype.card (SpinIdx × SU.Slot)
lemma mode_cap {n:Side}{S:Finset (Seat n)}{r:ℕ}(p:S.card≤ r) : (modesIn n S).card ≤ modeCap r:=by -- adapt Selle.knode
 apply le_trans (b:=modeCap S.card) _ (Nat.mul_le_mul_right _ p); let T:=modesIn n S; let J(i:T) : S × SpinIdx × SU.Slot := (⟨node i.val.1.1,(modes_at ..).mp i.property⟩, i.val.1.2,i.val.2)
 change T.card ≤_; unfold modeCap; rw [← Fintype.card_coe T,← Fintype.card_coe S, ←Fintype.card_prod]; apply Fintype.card_le_of_injective J; intro i j v; exact Subtype.ext (Prod.ext (Prod.ext (Tenant.needle (congrArg (fun i:S×SpinIdx×SU.Slot=> i.1.val) v)) (congrArg (fun i=>i.2.1) v)) (congrArg (fun i=> i.2.2) v))

abbrev sizeRent (m r:ℕ) : ℝ := ((modeCap r:ℝ)+1)^m
lemma size_issue {n:Side}{S:Finset (Seat n)}(h:S.card≤ r)(M:ℕ): ((modesIn n S).card+1:ℝ)^M ≤ sizeRent M r := by unfold sizeRent; gcongr; exact mode_cap h
lemma hammer_can {H:Real.exp 1≤P.x}(T:Hammer Y s i k A M C r)(R : evenPose Y s i)
   (X:Defog (H:=H) Y s i k E M B 1)
   (u:C*sizeRent M r ≤ chip (shx s) (-199))
   (b:∀ j,cows j (Lattice.halo p A.S) B) : StripProof Y s i k H p B M A (chip (shx s) (-204)) := by
 constructor; exact T.owner; exact b
 intro L' t _; let G:=shadeY Y s i k 0 (ηP s); refine ⟨fun _=>0,Filter.Eventually.of_forall fun x=>?_,?_,?_⟩
 · let f:= strips Y s i L'; let F i:= (L'.get i).x; let σ:= fun j:Fin L'.length=> modesIn _ (L'.get j).S; let Z:= fun i:Fin L'.length=> f i (1,1)
   constructor; swap; · exact fun i' j=> strip_comm Y s i t i' j _
   have ht(i:Fin L'.length):= T.replica Y s _ k R (t.core (L'.get i) (List.get_mem ..)).foil; have hc:0≤ C:= (norm_nonneg _).trans T.issue.price
   have hv(i: Fin L'.length): Lyrics (σ i) M (chip (shx s) (-199)) (Z i):= by
     exact (ht i).issue.output.expend le_rfl ((mul_le_mul_of_nonneg_left (size_issue (ht i).span M) hc).trans u)
   refine ⟨σ,fun i _ j _ v=>?_,Z,fun _=>0,hv,fun j u v w=>?_,?_⟩ -- sort name i
   · have ha: Distant (p+1) (L'.get i).S (L'.get j).S:= ((lt_or_gt_of_ne v).elim (fun v=>t.annex.rel_get_of_lt v) fun p=> Distant.symm (t.annex.rel_get_of_lt p))
     apply Finset.disjoint_left.mpr; intro a e h; have hs:= ha _ ((modes_at ..).mp e) _ ((modes_at ..).mp h); rw [separation_self] at hs; omega
   · let V:=(x.1,(Y.voyage i).CapeT s x); let a:= atFrame Y s i x; let Q:= flatSeat Y s i f j x; let A(i':Fin L'.length):= (L'.get i').x; let E:= twist (quantU (tradew _ a))
     have hQ:Q=Z j:=by
         unfold Q Z; rw [flatSeat, moved_root]; change E (A j V-1)=A j (1,1)-1; rw [map_sub,map_one,show E (A j V)= _ from ((ht j).weld a V).symm, (ht j).literal];-- check
     change ‖(WakeInvestment.weighted flatP u (flatShear Y s i k)).glow Q - _‖ ≤ (0:ℝ) ∧ ‖(WakeInvestment.weighted flatP u (flatShear Y s i k)).glow Q‖ ≤ _; rw [hQ,sub_self,norm_zero]; exact ⟨le_rfl,((hv j).post _ (X.ready.investBook u (abs_le.mpr ⟨by linarith,w⟩)) X.ready.visa).trans X.ready.sizeB⟩
   apply le_trans (Finset.sum_nonpos (fun j _=>?_)) le_rfl; dsimp only; unfold Z; let U:=Lamour.alleyR (mateK (side Y i s)) (flatSea Y s i k);
   rw [noble_linear]; change (U (_-1)).re+0 ≤ 0; rw [map_sub]; have hp:U ((L'.get j).x (1,1))=1:=(noble_linear ..|>.symm).trans (ht j).quiet
   change (U ((L'.get j).x (1,1))-U 1).re+0≤0; rw [hp,show U 1=1 from (noble_linear ..|>.symm).trans (noble_unit Y s i k),sub_self]; simp
 · have h:= X.includesRent; simpa using (shade_prior Y h h.ready h.willing).1
 have h:= X.includesRent; simp only [Real.exp_zero, one_mul]; refine (shade_prior Y h h.ready h.willing).2.trans (Real.exp_monotone ?_); have hz:0≤ chip (shx s) (-204):= (chip_pos ..).le; linarith only [mul_nonneg (Nat.cast_nonneg (α:=ℝ) L'.length) hz]

local notation "θ₀" s:max => leafCost (P:=P) s
/-- Actual spin Mark, no uplift yet. Can use **any** support at this level. -/
structure SpinLeaf {n:Side} (A:Hookah n)(M:ℕ)(C:ℝ)(r:ℕ) : Prop where
 owner: AtSupport false A.S A.x
 span:A.S.card≤r
 weld:covariant A.x
 literal(x:Fields n) : A.x x=A.x (1,1)
 degree: Cadre (modesIn _ A.S) M C (A.x (1,1))
abbrev optPrice {P:Preparation}(E:ℝ)(s:ℕ)(M r:ℕ)(C:ℝ) := leafCost (P:=P) s * (C+C*sizeRent M r* flatTicket E^M)
lemma SpinLeaf.can (T:SpinLeaf A M C r)(w:ℂ)(h:‖w‖=leafCost (P:=P) s) {H:Real.exp 1≤ P.x}{B:ℕ}(q:Defog (H:=H) Y s i k E M B 1):
   let z:=noble Y s i k (A.x (1,1))
   Hammer Y s i k (sleeve A z w) M (optPrice (P:=P) E s M r C) r := by
 intro z; let N1:=side Y i s; let u:= A.x (1,1); let v:= (modesIn _ A.S); let X : Finset (Single N1):=v; let t:=leafCost (P:=P) s
 have hc:0≤ C:=(norm_nonneg _).trans T.degree.price
 have hu: ‖z‖ ≤ C*sizeRent M r* flatTicket E^M:=by
    let F:= WakeInvestment.weighted flatP 0 (flatShear Y s i k)
    apply (noble_bound Y s i k u 0).trans; let V:=flatTicket E
    have hx:1≤V:=q.ready.visa; have hv: Lyrics v M (C*sizeRent M r) u:= T.degree.output.expend le_rfl (mul_le_mul_of_nonneg_left (size_issue T.span M) hc)
    exact hv.post F (q.ready.investBook 0 (by norm_num)) hx
 let J':=sleeve A z w; let f : Mark N1:=1; let G:= u+(-z) • (1:FC (Single N1)); have hx: J'.x (1,1)=1+w • G:=rfl
 change Hammer Y s i k J' M _ r; refine ⟨lease_support T.owner _ _,T.span, fun g x=> ?_,fun x=>?_,?_,?_⟩
 · let U:= twist (quantU (tradew N1 g)); change 1+ w • (A.x _+(-z) • 1)= U (1+w • (A.x x+(-z) • 1)); dsimp only [U]; rw [T.weld, map_add,map_one,twist_scalar,map_add,twist_scalar,map_one]
 · change 1+ w • (A.x x+(-z) • 1)=_; rw [T.literal]; rfl
 · rw [hx,noble_linear]; let π:=Lamour.alleyR (mateK N1) (flatSea Y s i k); change π (1+w • G)=1; unfold G; rw [map_add,map_smul,map_add,map_smul]; have hp:π 1=1:=(noble_linear ..|>.symm).trans (noble_unit Y s i k); rw [hp,show π u=z from (noble_linear ..).symm]; simp
 rw [hx]; have ht:1+w • G-1=w • G:= by abel
 rw [ht]; let C':= C*sizeRent M r* flatTicket E^M; have hz : ‖-z‖*(1:ℝ)≤ C':=by simpa using hu
 have hG: Cadre v M (C+C') G:= .add T.degree (((Cadre.unit (s:=v)).scale (-z)).buy (Nat.zero_le _) hz)
 unfold optPrice; rw [←h]; exact hG.scale w
include Y
lemma pure_fit {H:Real.exp 1≤ P.x} (T:SpinLeaf A M C r)(q: Defog (H:=H) Y s i k E M B 1)(v: evenPose Y s i) (h: optPrice (P:=P) E s M r C * sizeRent M r ≤ chip (shx s) (-199)) (d: optPrice (P:=P) E s M r C ≤1) (p_:∀ j,cows j (Lattice.halo 0 A.S) B): RootV (H:=H) Y s i k 1 0 B M A (noble Y s i k (A.x (1,1))):=by
 let u:= noble Y s i k (A.x (1,1)); let f(a:ℂ):= sleeve A u a
 refine ⟨T.owner,fun a l=> hammer_can Y s i k (T.can Y s i k a l q) v q h p_,fun a l x=>?_⟩
 have hx:= T.can Y s i k a l q; change ‖(f a).x x‖ ≤ _; have hF:Hammer Y s i k (f a) M _ r:= hx; rw [hF.literal]; let X:= (f a).x (1,1);
 apply (norm_le_norm_sub_add X 1).trans; rw [norm_one]; exact (add_le_add hF.issue.price le_rfl).trans ((add_le_add d le_rfl).trans (Real.add_one_le_exp _))
#print axioms pure_fit
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
