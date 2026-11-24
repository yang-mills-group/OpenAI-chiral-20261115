import YM.CF.Vp929.Ladder.Base
import YM.CF.Vp929.Ladder.Hop

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
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
open Ione Beau Haro Cascade Fief VolumeRate CF.Mint Graph
open scoped Mew
variable {K : Teller SU.group} {R : Patch} {L : ChartRatio SU.group} {V : Grace K R L}
variable {d h x delay : ℝ} {D C R0 : ℝ → ℝ} {m N B : Side} {U : Grasp V.U B d} {W : GivenX V U} {J : Robes N V W} {q : Chi}
  {P : Prescription R B} {N0 k : ℕ}
namespace Branch
abbrev Rx (x : ℝ) := strip x/8
abbrev stopEarn (T : Month x 1 6 2 N0 V W) := earnings W (T.a 0) (2*x) (dleaf R.L (hat R.L x 0)/1000+dleaf R.L (hat R.L x 0)/1000)
variable (H : Service V U W J q h D C R0 P N0 delay) (hh : 1 ≤ h) {A : Branch W m k x N0} (a : Bon J q h D delay A)
local notation "M" => cell m B R.L
local notation "r" => Rx x
local notation "U'" => ball (0:ℂ) 1
lemma Rx_pos (hx : 1≤x) : 0<Rx x := div_pos (strip_pos hx) (by norm_num)
omit H hh a in
lemma range_scale {x : ℝ} (hx : 1 ≤ x) {t : ℝ} : ((t:ℂ) ∈ (U')) ↔ |t*Rx x| < Rx x := by
  have p:= Rx_pos hx; rw [abs_mul,abs_of_pos p, mem_ball_zero_iff,Complex.norm_real,Real.norm_eq_abs]; nth_rw 2 [←one_mul (Rx x)]; exact (mul_lt_mul_iff_of_pos_right p).symm
include H a
lemma existsSolve {z : ℝ} (hv : |z| < r) : ∃ b, Solved P A z b := by
  obtain ⟨g,hd,hW⟩:= (a.posts H).solve; obtain ⟨_,v,f,_,u⟩:= hW (z:ℂ) (by rw [hat_zero,mem_ball_zero_iff,Complex.norm_real]; exact hv)
  exact ⟨_,⟨⟨v,u rfl⟩, f⟩⟩
include hh
structure Record (A : Branch W m k x N0) (P : Prescription R B) where
  f : ℂ → ℂ
  ana : DifferentiableOn ℂ f (ball 0 1)
  budget : ∀ z ∈ ball (0:ℂ) 1, ‖f z‖ ≤ Real.exp (stopEarn A.T * sites (cell m B R.L 0))
  real (x' : ℝ) : (x':ℂ) ∈ ball (0:ℂ) 1 → ∀ b, Solved P A (x'*Rx x) b → f x' = A.bottom b P

lemma history : Nonempty (Record A P) := by
  have hₜ:1≤x:=(a.prices _ le_rfl).grade; have hp:= Rx_pos hₜ; obtain ⟨g,hd,hW⟩:= (a.posts H).solve
  rw [hat_zero] at hd hW; let F(z:ℂ):=g (z*r); have hf z (u:z ∈ (U')) : z*(r:ℂ) ∈ ball (0:ℂ) r := by
    rw [mem_ball_zero_iff,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]; exact mul_lt_of_lt_one_left hp (mem_ball_zero_iff.mp u)
  have hg : DifferentiableOn ℂ F U' := hd.comp (Differentiable.differentiableOn (by fun_prop)) hf
  let T:= A.T; let X:= A.last.Q 0; let L:= A.loom 0
  let G(z):=A.corr P (F z) 0; let b(z):=(F z).read 0; let φ(z):=cpartition (T.a 0) U X k L (G z) (b z); have pv(z)(u:z∈ (U')):= hW _ (hf z u)
  have hg' : Set.MapsTo F U' (A.BetaArea 3 0):= fun z hz=> (a.posts H).expand_area (pv z hz).2.1 _
  let v:= (a.can.cape 0); let pT:= v.paid
  have hB : ∀ z∈(U'), Both (Cost (T.a 0) h (dleaf R.L (hat R.L x 0)/1000)) (G z) ∧ 0≤ (b z).re ∧ (b z).re ≤ 2*x := by
    intro z hz; have he:= a.entersBet (hg' hz) le_rfl (Nat.zero_le _); rw [hat_zero] at he; have ht : 53/100*x ≤ (b z).re ∧ (b z).re ≤ 7/4*x:=⟨he.1,he.2.1⟩; have u:=a.costs H 0 (by omega) (hg' hz); exact ⟨⟨u.1.toCost,u.2.toCost⟩,by linarith [ht.1],by linarith [ht.2]⟩
  obtain ⟨W,V⟩:= c_beam W (A.last.sound 0) (show Roof _ J.k d J.n L from {pT with paid:=fun i=>(pT.paid i).shrink J.hr.le}) k (J.gran.trans v.size) hh isOpen_ball (F:=G) b (a.corr_holo H _ isOpen_ball hg 0 (by omega) hg') (differentiableOn_pi.mp hg _) (T.a 0) hB
  refine ⟨⟨φ,W,V,fun z hz β v=>?_⟩⟩
  have hv : F (z:ℂ)=β := ((pv _ hz).2.2.2.1 _ v.paid (by exact_mod_cast v.fixp)).symm
  unfold φ b G; rw [hv,a.both_real H v.toRealQ 0 (by omega)]; have he:= cpartition_real (T.a 0) U X k L (A.chargeLevel P β 0) (β.read 0).re (A.offset P β 0); rw [v.toRealQ.coeRe 0 (by omega)] at he; exact he

lemma in_window (hm : m=oYY V N0 J x) {d0 : ℝ} (p : ∀ (X : GramM (cell (oYY V N0 J x) B R.L 0)) (S : Scree.Loom (cell (oYY V N0 J x) B R.L 0)), RoomAt (h:=h) J N0 x X S → d0 ≤ ‖compensated U X S‖) (F : Record A P) : d0 ≤ ‖F.f 0‖ := by
  subst m; obtain ⟨b,s⟩:= existsSolve H (z:=0) a (by rw [abs_zero]; exact Rx_pos (a.prices _ le_rfl).grade)
  have hg : F.f 0= bottom A b P := by simpa using F.real 0 (by simp) b (by simpa using s)
  rw [hg]; apply p
  let Z:= gram P A b 0; let Y:= (a.can.cape 0).paid; have he : Roof _ J.k d J.n (A.loom 0):= {Y with paid:=fun i=>(Y.paid i).shrink J.hr.le}
  have hx:= (a.prices _ le_rfl).leaf; have hp:= (A.T.boot 0).1; have ht:=(a.charged H s.toRealQ _ (Nat.zero_le k)); rw [hat_zero] at hp ht
  refine ⟨hp,rfl,(show (b.read 0).re=x from by rw [Bon.anchor s]; simp), V.L.mood (k-0), Stop.sage _ _ _ he (a.can.pole 0), frostQ (show LotR Z h (dleaf R.L x) (dleaf R.L x) from (ht.toCost.mono (by linarith)).lot _ _) (zero_le_one.trans hh) (A.last.sound 0), hx.le⟩
end Branch
end YM.CF.Py.Rate
