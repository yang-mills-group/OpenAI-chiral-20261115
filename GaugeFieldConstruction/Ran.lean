import GaugeFieldConstruction.Dudge
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 140000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
set_option maxHeartbeats 240000
variable (I:Type)[LinearOrder I][Fintype I]
open SeasonH
variable (σ:I→Seat n)(V:Support (More n))(A:Pane n) (M:I→ Boke n I)(F:Fork n I)(r:ℝ)(v:stabH F)
variable (t:Finset I)(e:Vulcan I n)(S:Hubber n)(Q:Boke n I)
-- raw Lattice supports.Z cut zeta
def padS (m:ℕ)(P:BudgetPoint)(a:Bool):Finset (Seat n):= if a then S else if t.card=1 then S ∪ ((t.image σ).biUnion (fun i=> Halo_Plus m i P)) else S
-- reconstruction.Mean.S
variable (m:ℕ)(P:BudgetPoint)
def MarksΥ (a:Bool):Finset (Scree.Hub n):=Finset.univ.filter (fun i=> i.val.2=padS I σ t S m P a ∧ i.val.1 ∈ t.image σ)
def QuotaΥ (a:Bool)(X:Scree.Hub n):ℝ:= if X∈ MarksΥ I σ t S m P a then exp_Plate (MarksΥ I σ t S m P a) else 0
lemma pad_Φ (q:Incζ I σ t e)(p: e.seat=S): SpacePad m P σ e=padS I σ t S m P e.pure:=by
 unfold SpacePad padS; rw [p]; split; exact union_empty _; have hp:e.keys.Nodup:=List.Nodup.of_map _ q.2; have hs:t=e.keys.toFinset:=q.1.symm; have h:t.card=e.keys.length:= by rw [hs,List.toFinset_card_of_nodup hp]
 rw [h]; cases hk:e.keys with
 | nil=> simp
 | cons i l => cases l with|nil=>simp [hs,hk]| cons i l=>simp
lemma Mark_QU (q:Incζ I σ t e) :marksY σ e m P t=MarksΥ I σ t e.seat m P e.pure:=by
 unfold marksY MarksΥ; ext1 i; simp_rw [pad_Φ I σ t e e.seat m P q rfl,mem_filter,mem_univ,true_and]; rw [and_iff_right q.1.symm, and_iff_right q.2] -- tune
variable (x:Scree.Hub n)
lemma Lex_Youth (t₀:Incζ I σ t e):LexS σ e x m P t= QuotaΥ I σ t e.seat m P e.pure x • PinInk e:=by
 unfold LexS QuotaΥ; rw [Mark_QU I σ t e m P t₀]; split; next h=>rw [Complex.coe_smul] -- Scalar InkD ℂ to ℝ type.
 rw [zero_smul]
lemma Lex_blank (t₀:¬ Incζ I σ t e):LexS σ e x m P t=0:=by
 unfold LexS; rw [if_neg (fun h=> t₀ ⟨(mem_filter.mp h).2.1.symm,(mem_filter.mp h).2.2.1⟩)]
abbrev xPad(a:Bool):ℝ:=QuotaΥ I σ t S m P a x
lemma sum_stamp (y:Boke n I) : entryS σ m P y t x = ∑ S:Hubber n, let z:=cacheS I σ t S (foli y); let F:=cacheS I σ t S y; if t.card=1 then (QuotaΥ I σ t S m P true x) • z+(QuotaΥ I σ t S m P false x) • (F-z) else (QuotaΥ I σ t S m P true x) • F:=by
 induction y with
 | nil=> simp [Lee,entryS,foli,cacheS,pre_g,skimQ]
 | cons i Q h=>
    rw [show entryS σ m P (i::Q) t x=LexS σ i x m P t+entryS σ m P Q t x from consA ..,h] -- mismatch RHS
    let F:=cacheS I σ t; by_cases T: Incζ I σ t i; swap
    · rw [Lex_blank I σ t i m P x T,zero_add]; have h1(X): F X (i::Q)=F X Q:=by simp [F,cacheS,pre_g,skimQ,T]
      have h2(X): F X (foli (i::Q))=F X (foli Q):=by
         unfold foli; rw [List.filter_cons]; split; simpa [F,cacheS,skimQ,T]; rfl
      exact sum_congr rfl fun x u=>by dsimp only; rw [show cacheS I σ t x (foli (i::Q))=cacheS I σ t x _ from h2 x, show cacheS I σ t x (i::Q)=cacheS I σ t x Q from h1 x]
    let Z0:=i.seat; let sF(S:Hubber n):InkD n:= if Z0=S then (QuotaΥ I σ t S m P i.pure x) • PinInk i else 0
    have he:LexS σ i x m P t=∑ i,sF i:=by rw [Lex_Youth I σ t i m P x T]; unfold sF; rw [Finset.sum_ite_eq]; simp [Z0]
    rw [he,←sum_add_distrib]; refine sum_congr rfl fun S _=> ?_
    have hx:∀y,F S (i::y)=if i.seat=S then PinInk i+F S y else F S y:=by
       intro y; unfold F cacheS skimQ pre_g; rw [List.filter_cons,if_pos (decide_eq_true T),List.filter_cons]; by_cases h:i.seat=S
       · rw [if_pos (decide_eq_true h),if_pos h,consA]
       rw [if_neg,if_neg]; exact h; simpa [h]
    dsimp only [sF]; change (if Z0=S then _ else _)+ (if t.card=1 then _ else _)=(if t.card=1 then _ else _)
    -- establish a weights; solve cases
    by_cases p:i.seat=S; swap
    · have hg: i.seat≠ S:=p; simp_rw [if_neg (show Z0≠S from p),zero_add, show cacheS I σ t S (i::Q)=F S Q from (hx _).trans (if_neg p)]; rw [show cacheS I σ t S (foli (i::Q))=F S (foli Q) from ?_]; unfold foli; rw [List.filter_cons]; split; exact (hx _).trans (if_neg p); rfl
    rw [if_pos (show Z0=S from p),show cacheS I σ t S (i::Q)=PinInk i+cacheS I σ t S Q from (hx _).trans (if_pos p)]; by_cases b:t.card=1; swap
    · rw [if_neg b,if_neg b,smul_add]; cases v:i.pure
      · rw [show QuotaΥ I σ t S m P false x=QuotaΥ I σ t S m P true x from (by simp only [QuotaΥ,MarksΥ,padS,b,Bool.false_eq_true,↓reduceIte])] -- tune Bool
      rfl
    rw [if_pos b,if_pos b]; unfold foli; rw [List.filter_cons]; cases v:i.pure
    · rw [if_neg Bool.false_ne_true, show PinInk i+_ - _ = PinInk i+(F S Q-F S (List.filter (fun a=>a.pure) Q)) from add_sub_assoc .., smul_add]; abel
    rw [if_pos rfl,show cacheS I σ t S _=_ from (hx _).trans (if_pos p),smul_add]; unfold F; abel -- tune
#print axioms sum_stamp
end MastTin
end YM.CF.XGarden
end
