import YM.SU5.FiniteGaugeData.Poin.Paste
import YM.Work.C08
set_option autoImplicit false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open Filter Function Set OS OS.Semigroup Mink Mink.General Mink.Lorentz Complex Flute MeasureTheory Boundary Probe
open scoped Topology ContDiff NNReal InnerProductSpace
local notation "tt"=>timeAxis
variable {H:Hilbert}{α:Type}(M':Canopy H α)(S: OS.Semigroup H timeAxis)(Ω:Bench S)(hΩ:∀ z:E4,M S z Ω.val=Ω.val)
variable {n:ℕ} (p q:Mink.Poincare)
namespace Canopy
variable (t u:M'.Token)(chip:M'.Chip)(g:Test4)(w:List M'.Token)
local notation "D"=>Bench S
local notation "L"=> M'.Ticket S Ω
local notation "F"=> M'.Model S Ω
variable (x: E4)(Y:Bench S)(A:H.Op)
lemma Tcost (g:Test4): Continuous fun p=> shiftK p g:= by
 let A (p:Mink.Poincare):= p.Λ.sends.symm
 exact _root_.YM.Work.C08.continuous_affine_probe (b:=Mink.Poincare.b) A g Mink.Poincare.continuousB (usual.comp (continuous_inv.comp Poincare.continuousL)) (usual.comp Poincare.continuousL)
lemma chipCt(t:M'.Chip): Continuous (fun p:Mink.Poincare=> M'.dep (M'.βL p.Λ t)) := by
 cases t with | mk a t=> let S:= M'.P a; exact (M'.flash a).continuous.comp (((S.Lc.comp Poincare.continuousL).clm_apply (continuous_const (y:=t))))
lemma v_exp(c:H.Op): valise S (A-c) g= valise S A g-valise S c g:=by
 rw [sub_eq_add_neg, vadd, ← neg_one_smul ℂ c, vscale]; simp [sub_eq_add_neg]
lemma ν_shift {β:Type*}(L':Filter β)(G:β→Test4)(Y:β→ H.Op)(q:Tendsto G L' (𝓝 g))(v:Tendsto Y L' (𝓝 A)): Tendsto (fun i=> valise S (Y i) (G i)) L' (𝓝 (valise S A g)):= by
 let B(i):=valise S (Y i) (G i); let X(i):=valise S A (G i); have h:Tendsto (fun i=> B i-X i) L' (𝓝 0):= by
    rw [tendsto_zero_iff_norm_tendsto_zero]; refine squeeze_zero (fun _=>norm_nonneg _) (g:=fun i=> vial (G i)*‖Y i-A‖) (fun i=>?_) (?_); unfold B X; rw [← v_exp]; exact vnorm ..
    simpa only [Function.comp_def,sub_self,norm_zero,mul_zero] using ( (vialC.tendsto g|>.comp q).mul (v.sub_const A).norm)
 have hv:Tendsto X L' (𝓝 (valise S A g)):= ((apron S A).continuous.continuousAt (x:=g)).tendsto.comp q
 have hp:= h.add hv; rw [zero_add] at hp; exact hp.congr (fun i=> sub_add_cancel (B i) (X i))
lemma empire (n:ℕ) {β:Type*}(L': Filter β) (q:β→M'.Token)(A:H.Op) (g:Test4)
 (_:∀ i:β,M'.grade (q i).fst=n) (v:Tendsto (fun i=> M'.dep (q i).fst) L' (𝓝 A))(h:Tendsto (fun i=>(q i).snd) L' (𝓝 g))(Yp:β→Bench S)(k:pays_to S L' Yp Y) : pays_to S L' (fun i=> M'.horizon S (q i) (Yp i)) (ℑ S A g n Y):=by
 rename_i z -- renames random
 let x(i:β):= (q i).snd; let y(i:β):= M'.dep (q i).fst
 have hp(m:ℕ){J:Test4}(f:β→Test4)(t:Tendsto f L' (𝓝 J)): Tendsto (fun i=> brochure S (y i) m (f i)) L' (𝓝 (brochure S A m J)):= by
    induction m generalizing J f with | zero=>exact ν_shift S _ _ _ f y t v | succ n ih=> exact (ih f t).add ((ih _ ((εpref tt).continuous.continuousAt.tendsto.comp t)).mul tendsto_const_nhds)
 intro m; have he(i:β): M'.grade (q i).fst=n:=by exact z i
 simp_rw [horizon, he, graphN]; exact (show Continuous (fun p:H.Op×H=>p.1 p.2) from continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp ((hp _ x h).prodMk_nhds (k _))
lemma Epic (w:List M'.Token): pays_to S (𝓝 p) (fun i=> M'.bud S Ω (M'.moved i w)) (M'.bud S Ω (M'.moved p w)):= by
 induction w with
 | nil=> exact fun _=> tendsto_const_nhds
 | cons i w ih=> unfold moved; simp_rw [List.map_cons,planeV]; apply empire M' S _ (M'.grade i.fst) _ (fun j=>M'.travel j i) _ _ (fun _=>rfl) ((M'.chipCt i.fst).continuousAt.tendsto) ((Tcost i.2).continuousAt.tendsto) _ ih -- tune order stale
lemma lifting : Continuous (fun p:Mink.Poincare=> M'.Ticket S Ω (M'.moved p w)) := continuous_iff_continuousAt.mpr fun t=> tune_in S _ _ _ (Epic M' S Ω t w)
#print axioms lifting
end Canopy
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin
