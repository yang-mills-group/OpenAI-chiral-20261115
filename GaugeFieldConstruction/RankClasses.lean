import GaugeFieldConstruction.Printed
import GaugeFieldConstruction.F3Reps
import GaugeFieldConstruction.GRank
import GaugeFieldConstruction.FRank
import GaugeFieldConstruction.XRank

/-!
# U1. Class ranks (on all *shell* tests)

Proof through the exact pivot columns of RankSupplement. `scan` is the
greedy independent-column criterion, thus checks the listed ranks/pivots,
not reproducing Python's internals. V ranks `Sym` always use symmetrized
inputs. Lower dimensions accounted in spaces. Use homogeneous d=4 and 5
columns in eliminations; filters commute with H in this computation.

Complex dimensions (one copy). These so far don't count the species
copies, prove R1's Wick pairing price or its approximation/weak bounds.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.U1
open Vouchers Cauchy Row Raw Record Submodule Module Function Certificate

-- Cumulatively include all lower grades in the following definitions; no
-- unit in these centered rows.
def gFour := space evalTg
def gFive := gFour ⊔ space evalG
def fThree := space B
def fFour := fThree ⊔ space evalTf
def fFive := fFour ⊔ space evalF
def xFour : Submodule ℂ (J Row.x) := ⊥
def xFive := space evalX

/-- Standard T/W/V column spaces for a centered row, and the differentiated
 rank calculation. Compute complex rank. -/
def TT {α β : Type*} (R : Record α β) (four : Submodule ℂ (J α)) := R.allowed symAct four
def WW {α β : Type*} (R : Record α β) (five : Submodule ℂ (J α)) := R.allowed Raw.v five
def VV {α β : Type*} (R : Record α β) (five : Submodule ℂ (J α)) := R.allowed vsAct five
variable {α β γ : Type*}

/-- combined map on W,V. Signs as (93) -/
def codiff (R : Record α β) :
    (Axis → J α) × (VS → J α) →ₗ[ℂ] ((Axis × Axis) → J α) :=
  R.divA ∘ₗ LinearMap.snd ℂ _ _ - R.heatP Axis ∘ₗ LinearMap.fst ℂ _ _
lemma rank_space (R : Record α β) (five : Submodule ℂ (J α)) :
    map (codiff R) ((WW R five).prod (VV R five)) = map (R.heatP Axis) (WW R five)⊔map R.divA (VV R five) := by
  ext1 z
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨⟨u,v⟩, ⟨hu,hv⟩,rfl⟩
    exact ⟨_,⟨-u,Submodule.neg_mem _ hu,rfl⟩,_,⟨v,hv,rfl⟩,by simp [codiff,add_comm,sub_eq_add_neg]⟩
  rintro ⟨_,⟨u,hu,rfl⟩,_,⟨v,hv,rfl⟩,rfl⟩
  exact ⟨(-u,v),⟨Submodule.neg_mem _ hu,hv⟩,by simp [codiff,add_comm]⟩

section
open gRanks
lemma t_classG : TT recG gFour=line (pick tMatP tMat) :=
  document_pick readingTg _ g4T_ok _ tMat_verified
lemma w_classG : WW recG gFive=line (pick wMatP wMat) := by
  rw [WW,gFive,gFour, allowed_add readingTg readingG,erase readingTg (B:=Raw.v) (by exact g4W_ok),bot_sup_eq]
  exact document_pick readingG _ g5W_ok _ wMat_verified
lemma v_classG : VV recG gFive=line (pick vMatP vMat) := by
  rw [VV,gFive,gFour, allowed_add readingTg readingG,erase readingTg (B:=vsAct) (by exact g4V_ok),bot_sup_eq]
  exact document_pick readingG _ g5V_ok _ vMat_verified
lemma d_imageG : map recG.divP (TT recG gFour) = line divs := by rw [t_classG,line_map]; rfl
lemma tr_imageG : map trace (TT recG gFour) = line faces := by rw [t_classG,line_map]; rfl
lemma comboG : map (codiff recG) ((WW recG gFive).prod (VV recG gFive))=line ranks := by
  rw [rank_space,w_classG,v_classG,line_map,line_map,← line_combine]; rfl
lemma picked_count (l : List (J α)) (b) (h : Scan0 l b) : line (pick b l) = line l := by
  have e:=accumulated l b ⊥ h; rw [bot_sup_eq, bot_sup_eq] at e; exact e.symm
-- more general
lemma picked_number {M : Type*} [AddCommGroup M] [Module ℂ M] (l : List M) (b) (h : Scan0 l b) :
    finrank ℂ (line (pick b l))=b.count true := by
  have e:=accumulated l b ⊥ h; rw [bot_sup_eq, bot_sup_eq] at e; rw [← e,counted l b h]

theorem g_ranks :
    finrank ℂ (TT recG gFour)=3 ∧ finrank ℂ (map recG.divP (TT recG gFour))=2 ∧
    finrank ℂ (WW recG gFive)=2 ∧ finrank ℂ (VV recG gFive)=20 ∧
    finrank ℂ (map (codiff recG) ((WW recG gFive).prod (VV recG gFive)))=19 ∧
    finrank ℂ (map trace (TT recG gFour))=1 := by
  rw [comboG,d_imageG,tr_imageG,t_classG,w_classG,v_classG,
    picked_number _ _ tMat_verified,picked_number _ _ wMat_verified,picked_number _ _ vMat_verified,
    counted _ _ divs_verified,counted _ _ faces_verified,counted _ _ ranks_verified]
  decide
end

section
open fRanks

def ph := ferm true
lemma fFive_W (B : Labels α) (h : ph.allowed B fFour=⊥) : ph.allowed B fFive=ph.allowed B (space evalF) := by
  have e := allowed_add (C':=B) (reading_add readingB readingTf) readingF
  rw [space_sum] at e
  change ph.allowed B (fFour ⊔ space evalF)=_⊔_ at e
  exact e.trans (by change ph.allowed B fFour ⊔ ph.allowed B _ = _; rw [h]; exact bot_sup_eq _)

lemma t_classF : TT ph fFour=line (pick tMatP tMat) := by
  rw [TT,fFour, fThree,ph,allowed_add readingB readingTf, erase readingB (B:=symAct) (by exact f3T_ok),bot_sup_eq]
  exact document_pick readingTf _ f4T_ok _ tMat_verified
lemma w_classF : WW ph fFive=line (pick wMatP wMat) := by
  rw [WW,fFive_W]
  · exact document_pick readingF _ f5W_ok _ wMat_verified
  rw [ph,fFour,fThree,allowed_add readingB readingTf, erase readingB (B:=Raw.v) (by exact f3W_ok),
    erase readingTf (B:=Raw.v) (by exact f4W_ok), bot_sup_eq]
lemma v_classF : VV ph fFive=line (pick vMatP vMat) := by
  rw [VV,fFive_W]
  · exact document_pick readingF _ f5V_ok _ vMat_verified
  rw [ph,fFour,fThree,allowed_add readingB readingTf, erase readingB (B:=vsAct) (by exact f3V_ok),
    erase readingTf (B:=vsAct) (by exact f4V_ok), bot_sup_eq]
lemma d_imageF : map ph.divP (TT ph fFour) = line divs := by rw [t_classF,line_map]; rfl
lemma tr_imageF : map trace (TT ph fFour) = line faces := by rw [t_classF,line_map]; rfl
lemma comboF : map (codiff ph) ((WW ph fFive).prod (VV ph fFive))=line ranks := by
  rw [rank_space,w_classF,v_classF,line_map,line_map,← line_combine]; rfl

theorem f_ranks :
    finrank ℂ (TT ph fFour)=2 ∧ finrank ℂ (map ph.divP (TT ph fFour))=1 ∧
    finrank ℂ (WW ph fFive)=1 ∧ finrank ℂ (VV ph fFive)=14 ∧
    finrank ℂ (map (codiff ph) ((WW ph fFive).prod (VV ph fFive)))=13 ∧
    map trace (TT ph fFour)=⊥ := by -- tweak
  have ht : map trace (TT ph fFour)=⊥ := by
    rw [tr_imageF]
    haveI := finite_line faces
    apply Submodule.finrank_eq_zero.mp
    rw [counted _ _ faces_verified]; decide
  rw [ht,comboF,d_imageF,t_classF,w_classF,v_classF,picked_number _ _ tMat_verified,
    picked_number _ _ wMat_verified,picked_number _ _ vMat_verified, counted _ _ divs_verified,
    counted _ _ ranks_verified]
  refine ⟨?_,?_,?_,?_,?_,rfl⟩ <;> decide
end
section
open xRanks
lemma w_classX : WW recX xFive=line (pick wMatP wMat) := document_pick readingX _ x5W_ok _ wMat_verified
lemma v_classX : VV recX xFive=line (pick vMatP vMat) := document_pick readingX _ x5V_ok _ vMat_verified
lemma comboX : map (codiff recX) ((WW recX xFive).prod (VV recX xFive))=line ranks := by
  rw [rank_space,w_classX,v_classX,line_map,line_map,← line_combine]; rfl
lemma t_classX : TT recX xFour=⊥ := eq_bot_iff.mpr (by
  intro z h; rw [Submodule.mem_bot]; funext i; change z i=0; have hv : z i∈(⊥:Submodule ℂ _) := h.2 i (Set.mem_univ _); simpa using hv)

theorem x_ranks :
    finrank ℂ (TT recX xFour)=0 ∧ finrank ℂ (map recX.divP (TT recX xFour))=0 ∧
    finrank ℂ (WW recX xFive)=1 ∧ finrank ℂ (VV recX xFive)=6 ∧
    finrank ℂ (map (codiff recX) ((WW recX xFive).prod (VV recX xFive)))=7 := by
  rw [t_classX,Submodule.map_bot, finrank_bot,finrank_bot,comboX,w_classX,v_classX,
    picked_number _ _ wMat_verified,picked_number _ _ vMat_verified,counted _ _ ranks_verified]
  decide
end
end YM.GaugeFieldConstruction.U1
