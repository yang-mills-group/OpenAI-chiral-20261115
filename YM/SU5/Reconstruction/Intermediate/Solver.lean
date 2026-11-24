import YM.SU5.FiniteGaugeData.LocalLimit.Voyage
/-! # Intermediate high price election. Alternative solving at high REAL material only. No purchases at (or from) higher Expense bins required. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
namespace LocalLimit

open Branch
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
    {d : ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
    {x delay : ℝ} {C R0 : ℝ → ℝ} {N0 k : ℕ} (P : Prescription R B)
    (A : Branch W m k x N0)
local notation "Ω" => cell m B R.L
local notation "Xc" => A.T.a
local notation "Xh" => hat R.L x
local notation "Xs" => A.last.Q
local notation "Xr" => A.loom
local notation "X₀" => A.toSpine.address
local notation "Yb" i => dleaf R.L (hat R.L x i)
local notation "Xm" => A.last.move
namespace Intermediate
abbrev Room (s:ℕ) := Moen.Space.rangeB (Fin s→ℝ) 1
variable (s:ℕ) {D:ℝ→ℝ} {h:ℝ}
def predict (d:ℕ→ℝ) (u:Room s) (i:ℕ) := if p:i<s then u.val ⟨i,p⟩ * d i else 0
variable (D)
def temper (i:ℕ) (u:Room s) : ℝ := A.toSpine.pilot x i + ∑ j∈range i, predict s (D∘(hat R.L x)) u j
local notation "κ" => temper A s D
local notation "Δ" => predict s (D∘Xh)
lemma temp_unit (u:Room s) : temper A s D 0 u=x:= by simp [temper,A.toSpine.pilot_zero]
lemma temp_move (i:ℕ)(u:Room s) : temper A s D (i+1) u + Xm i - predict s (D ∘ hat R.L x) u i = κ i u := by
 rw [temper,temper,A.toSpine.pilot_move i,sum_range_succ]; ring
lemma temp_cont (i:ℕ):Continuous (temper A s D i) := by
 refine continuous_const.add (continuous_finsetSum _ (fun j _=>?_))
 show Continuous fun u:Room s=>Δ u j; by_cases p:j<s; simp only [predict,dif_pos p]; exact ((continuous_apply (⟨j,p⟩:Fin s)).comp (show Continuous (fun v:Room s=> v.val) from continuous_subtype_val)).mul continuous_const
 simp only [predict,dif_neg p]; exact continuous_const

variable {D}
variable (a:Bon J q h D delay A)
include a
lemma predict_bound (i:ℕ)(u:Room s): |predict s (D ∘ hat R.L x) u i| ≤ D (hat R.L x i):= by
 have he:= (a.clocks i).bank
 unfold predict; split_ifs with p; swap; · simpa
 rw [abs_mul, Function.comp_apply,abs_of_nonneg he]; exact mul_le_of_le_one_left he ((pi_norm_le_iff_of_nonneg zero_le_one).mp u.property _)
-- as in Transfer.Downstairs
lemma pilotMargin (i:ℕ): (∑ j∈range i,D (Xh j)) ≤ strip (Xh i)*(1/400):= by
 let t j:=strip (Xh j)
 have p(j) : 0 < t j := strip_pos (a.clocks j).grade
 apply le_trans _ (mul_le_mul_of_nonneg_left (prices_sum a.prices i) (p i).le)
 rw [mul_sum]; refine sum_le_sum fun j hx=>?_; set y:= D (Xh j); have hY:0 ≤ y:=(a.clocks j).bank; let b:=t (j+1); have hx':0<b:=p _
 change y ≤ t i*(y/b); rw [←mul_div_assoc]; exact (le_div_iff₀ hx').2 (le_trans (mul_le_mul_of_nonneg_left ((a.clocks _).increase _ (hat_mono (mem_range.mp hx))) hY) (le_of_eq (mul_comm ..)))
lemma budget (i:ℕ)(u:Room s): |κ i u-A.toSpine.pilot x i| ≤ strip (Xh i) := by
 unfold temper; rw [add_sub_cancel_left]; refine (Finset.abs_sum_le_sum_abs ..).trans ((sum_le_sum (fun j _=> predict_bound A s a j u)).trans ((pilotMargin A a i).trans ?_)); linarith [strip_pos (a.clocks i).grade]
lemma accepted (i:ℕ)(p:i≤k)(u:Room s) : entersReal (Xh i) (κ i u) ∧ enters (Xh i) (κ i u) := (a.clocks i).enroll' (a.pilots i p).1 (a.pilots i p).2 (budget A s a i u)
omit a

variable (D h)
def Qualified (F:Room s→ Corr (cell m B R.L s)): Prop := Cleared W h (dleaf R.L (Xh s)) (Xc s) (Xs s) (k-s) (Xr s) F (temper A s D s) 0
variable {h}
-- genuinely free to use any real STATIC high charged input, not asking for extra costs from the law.
lemma static (F : Corr (cell m B R.L s)) (qF : Charged (Xc s) (Xs s) K.j R.L.val h (dleaf R.L (Xh s)) F): Qualified A s D h (fun _=> F) := by
 refine ⟨fun y _=> ?_, fun _=>qF, ⟨0,fun _=>le_rfl⟩⟩
 apply continuous_dens_raw; · exact continuous_const
 · exact temp_cont A s D s
 · intro i V; exact continuous_const
 intro i V; exact continuous_const
-- stored at zero extra offset. no constraints at other *periods*

variable (F:Room s→ Corr (cell m B R.L s))
abbrev cooled := Cooling.descends P A s F (temper A s D)
local notation "Z" => cooled P A s D F
def Settles (u:Room s) : Prop:=∀ i<s,(cooled P A s D F).posted i u=predict s (D ∘ hat R.L x) u i
variable {D}
variable (C0:Service V U W J q h D C R0 P N0 delay) (p₀:ResponsiveService J q N0 h delay P) (e:s≤k) (hh:1≤ h) (L0:Qualified A s D h F)
include C0 p₀ a e hh L0
lemma earns (i:ℕ) (u:i<s) :
    Cleared W h (dleaf R.L (Xh i) / 1000) (Xc i) (Xs i) (k-i) (Xr i) ((cooled P A s D F).G i) (temper A s D i) ((cooled P A s D F).v i) ∧
    Continuous ((cooled P A s D F).posted i) ∧ Continuous ((cooled P A s D F).wave i) ∧ ∀ t,
      |(Z).posted i t| ≤ D (Xh i) ∧ ‖(Z).wave i t‖ ≤ R0 (Xh i) ∧ |((Z).v i t).re-((Z).v (i+1) t).re| ≤ C (Xh i)*sites (cell m B R.L i) ∧
      ∀ y:Orbit (cell m B R.L i), Rue.FleetS (Xc i).threshold y.1 → denZ ((Z).launch i t) U (A.loom i) y = stove U (A.loom i) ((Z).guess (i+1) t) (A.loom (i+1)) (X₀ i).G ((X₀ i).step V) q J.d ((Z).wave i t).val y := (Z).paid C0 p₀ a e hh (fun j p=>⟨temp_cont A s D _,fun v=> (accepted A s a j (p.trans e) v).2⟩) L0 i u
lemma resources (i:ℕ) (u:i ≤ s) : Cleared W h (dleaf R.L (Xh i)) (Xc i) (Xs i) (k-i) (Xr i) ((cooled P A s D F).G i) (temper A s D i) ((cooled P A s D F).v i) := (Z).charged C0 p₀ a e hh (fun j p=>⟨temp_cont A s D _,fun v=> (accepted A s a j (p.trans e) v).2⟩) L0 i u
lemma match_guess : ∃ t:Room s, Settles P A s D F t := by
 let f(x:Room s)(i:Fin s):=(Z).posted i x / D (Xh (i:ℕ))
 have p (i:Fin s) := earns P A s a F C0 p₀ e hh L0 i i.isLt
 let g (x:Room s) : Room s := ⟨f x,(pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i=>by
     let d':= D (Xh (i:ℕ)); have hd : 0≤d' := (a.clocks _).bank; change |(Z).posted i x / d'| ≤ _; by_cases u:d'=0; rw [u]; simp
     rw [abs_div,abs_of_nonneg hd]; exact (div_le_one ((Ne.symm u).lt_of_le hd)).2 (((p i).2.2.2 x).1)⟩
 obtain ⟨t,u⟩:= Moen.Space.bow zero_lt_one g (Continuous.subtype_mk (continuous_pi (fun i=> ((p i).2.1).div_const _)) _)
 refine ⟨t,fun i j=>?_⟩
 let i':Fin s:=⟨i,j⟩
 rw [predict,dif_pos j, ← congr_fun (show f t=t.val from congrArg Subtype.val u) i',Function.comp_apply]
 unfold f; by_cases hD : D (Xh i)=0
 · have he:= ((p i').2.2.2 t).1; change |(Z).posted i t| ≤ _ at he; rw [hD] at he ⊢; simpa [abs_nonpos_iff.mp he] -- tune
 exact (div_mul_cancel₀ _ hD).symm
omit C0 p₀ a e hh L0 in
lemma Settles.pays {u:Room s} (r:Settles P A s D F u) (i:ℕ) (p:i<s): (cooled P A s D F).launch i u = (Z).guess i u := congrArg (fun x=> construct _ _ _ _ x _ _) (by have he:(Z).posted i u=predict s (D∘hat R.L x) u i:=r i p; exact (congrArg (fun x:ℝ=> κ (i+1) u+Xm i-x) he).trans (temp_move A s D i u)) -- rw [r i p, temp_move])
end Intermediate
end LocalLimit
end YM.CF.Py.Rate
#print axioms YM.CF.Py.Rate.LocalLimit.Intermediate.match_guess
