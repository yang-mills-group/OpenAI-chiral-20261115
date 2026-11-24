import YM.CF.Lor.Kern
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Lor
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Stilo Palot Scion Function Levier Hake Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire Eire
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Lich Corne
open Lich.Muster
attribute [local instance] opCStarAlgebra
local notation "G₅"=> SU.group
open Pressure.Tube
open Vol
variable{c f N B:Side}{d n m l:ℕ}{a b K v v' u D D' κ τ τ' :ℝ}{p:BudgetPoint}{q:Chi}
-- common allowance-target category.Across any Horizon.S.True.N.Anchor.g
variable{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E]
open rates Fief Braid
variable (L:Side)
-- stronger polynomial for log core vs logBeta. 
structure BoreP (A:ℝ→ℝ):Prop where
 pace :∃ C:ℝ,∃ n:ℕ,0≤ C∧∀ᶠ x:ℝ in atTop,|A x| ≤ C*plow x^n
namespace BoreP
variable {A B:ℝ→ℝ}{L}
lemma still(D:ℝ) :BoreP fun _=> D:=⟨|D|,0,abs_nonneg _,Eventually.of_forall fun i=>by simp⟩
private lemma line(x:ℝ):1 ≤ plow x:=Scales.size x
lemma relB:BoreP plow:= ⟨1,1,zero_le_one,Eventually.of_forall fun x=>by rw [abs_of_pos (zero_lt_one.trans_le (line _))]; simp⟩
lemma radius_c:BoreP fun x:ℝ=> (radiusB x:ℝ):=by refine ⟨1,1,zero_le_one,Eventually.of_forall fun i=>?_⟩; unfold plow Scales.b; rw [abs_of_nonneg (Nat.cast_nonneg _),one_mul,pow_one]; linarith
lemma tune (h:BoreP A)(p:∀ᶠ x in atTop,|B x| ≤ |A x|):BoreP B:=by obtain ⟨C,n,h,hv⟩:=h.pace; exact ⟨C,n,h,(hv.and p).mono fun i v=>v.2.trans v.1⟩
lemma join(h:BoreP A)(p:BoreP B): BoreP (fun x=> A x+B x):=by
 obtain ⟨C,m,h,hv⟩:=h.pace; obtain ⟨D,n,hp,hy⟩:=p.pace; refine ⟨C+D,m+n,add_nonneg h hp,?_⟩; filter_upwards [hv,hy] with x p v; rw [add_mul]; have ht:=line x; exact ((abs_add_le ..).trans (add_le_add p v)).trans (by gcongr <;> omega)
lemma grip(h:BoreP A)(p:BoreP B):BoreP fun x=> A x*B x:=by
 obtain ⟨C,m,h,hv⟩:=h.pace; obtain ⟨D,n,hp,hy⟩:=p.pace; refine ⟨C*D,m+n,mul_nonneg h hp,?_⟩; filter_upwards [hv,hy] with x p v; rw [abs_mul,pow_add]; exact (mul_le_mul p v (abs_nonneg _) ((abs_nonneg _).trans p)).trans_eq (by ring)
lemma self (p:BoreP A)(n:ℕ):BoreP fun x=> A x^n:=by induction n with|zero=> simp_rw [pow_zero]; exact still _| succ n ih=>simp_rw [pow_succ]; exact ih.grip p
lemma inert(h:sizeK L 1 A):BoreP A:=(still 1).tune (by
 have ht: Tendsto (fun i=>|A i|) atTop (𝓝 0):=by simpa using (tendsto_zero_iff_norm_tendsto_zero.mp h.spine )
 exact ht.eventually (ge_mem_nhds (by norm_num)))
lemma lento_w (p:BoreP A): Lento (fun i=> Real.exp |A i|):=by obtain ⟨C,n,p,h⟩:=p.pace; refine ⟨C,n,p,?_⟩; filter_upwards [h] with x p; rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_monotone p
variable(L:Side)
lemma creditK (p:BoreP A): sizeK L 0 A:=by obtain ⟨C,n,h,hv⟩:=p.pace; have he:sizeK L 0 plow:=(sizeK.mild L 1).accrue (sizeK.Bcash L); exact ((he.powC n).scale C).cost_d (hv.mono fun _ t=>t.trans (le_abs_self _))
omit L in
lemma nob {T:ℕ→ℝ} (i:ℝ→ℕ)(p:nib T)(h:BoreP fun x=>(i x:ℝ)): BoreP (T∘i):=by
 obtain ⟨C,n,t,hv⟩:= p; have he:BoreP fun x=> (Pad (i x):ℝ):=by unfold Pad; push_cast; first|exact (still _).join h|exact h.join (still _)
 refine ((still C).grip (he.self n)).tune ?_; filter_upwards with x; have ht:0≤(Pad (i x):ℝ):=Nat.cast_nonneg _; rw [comp_apply,abs_of_nonneg (hv (i x)).1,abs_of_nonneg (by positivity:_root_.LE.le (0:ℝ) (C* (Pad (i x):ℝ)^n))]; exact (hv _).2
end BoreP
end YM.CF.Lor
