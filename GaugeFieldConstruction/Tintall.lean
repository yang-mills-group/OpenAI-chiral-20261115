import GaugeFieldConstruction.Toman
import GaugeFieldConstruction.Pendant
import YM.CF.Hove.Hood
import GaugeFieldConstruction.Butane
import GaugeFieldConstruction.Vuoto
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
open Lich.Muster Lor
open Jet Vol Rel
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
open Feu Feu.Corset Haro
open Jet Plume Eire.Dress
open Prism Haro Tap
section
open SU FlightFlux TableF Boom Axon Flot Taxi Tap
open Lenten.Bank Lenten.ModuleB Lenten
variable {N:Side}{X Y:TirB N}{T:BookTarget}{p:BudgetPoint}{o:Skye.Seat N}{U:Support (More N)}{M:Tulip.Male}{h c d a:ℝ}{n m:ℕ}
-- C.Measure threshold not used. salary.T const
lemma siphon_t (X:TirB N)(i j:Single N): (fun v=>siphon X v i j)=fun v=> Fock.parity ((true,i):LeanV (Single N)) {(false,j)} * captain X (tray i j) v :=by
 funext p; unfold siphon winsock; rw [Matrix.of_apply, Prism.port_eq,if_neg]; simp -- tune
variable (g:Raid (Dwell N))(u:∀ J, Allows 6 (captain X J) 0 (g J))(v: o∈U)(hk:joinV (Scree.tariff p o h) g≤ c)(hK:0 ≤ h)(hv:brim p n U ≤ a)
include u
lemma compass:Charter N X:=fun i=> (u i).smooth
omit u
lemma frameSpin (K:TirB N)(z:Charter N K) (i j:Single N)(x:Fin m→ tangD N)(v:m≤6): (iteratedFDeriv ℝ m (siphon K) 0 x) i j=Fock.parity ((true,i):LeanV (Single N)) {(false,j)}*iteratedFDeriv ℝ m (captain K (Haro.tray i j)) 0 x:=by
 let V:= siphon K; let Y:Op (Single N)→L[ℝ]ℂ:=LinearMap.toContinuousLinearMap (show _→ₗ[ℝ] _ from ⟨⟨fun x=> x i j,fun _ _=>rfl⟩,fun _ _=>rfl⟩); let r:= Fock.parity ((true,i):LeanV (Single N)) {(false,j)}; let F:ℂ→L[ℝ]ℂ:= r • ContinuousLinearMap.id ℝ ℂ; have h:(m:ℕ∞ω) ≤ 6:= Nat.cast_le.mpr v
 rw [show iteratedFDeriv ℝ m (siphon K) 0 x i j=iteratedFDeriv ℝ m (Y ∘ V) 0 x from ?_, show Y ∘ V= F ∘ captain K (Haro.tray i j) from siphon_t K _ _,F.iteratedFDeriv_comp_left (z _) h]; rfl
 exact (DFunLike.congr_fun (Y.iteratedFDeriv_comp_left (siphon_C K z) h) x).symm
include v
include u hk hK hv
abbrev Coffer(a c:ℝ):= a^2*c+(max (mintPay ((caboose*16)*c)) (mintPay ((caboose*16)*(a*c))))
lemma appraised : HeadX m X p o U M h n book_zero (Coffer a c):=by
 have ht:=compass g u; have hA:1 ≤a:=(verge_p p o U n v).trans hv; have hp:0≤a:= zero_le_one.trans hA; have hc:0 ≤c:= (show 0 ≤ joinV (Scree.tariff p o h) g from sum_nonneg (fun i _=>mul_nonneg (by unfold Scree.tariff; positivity) (u i).nonneg)).trans hk
 have hb(g:Raid (Dwell N))(Z:Op (Single N))(C:ℝ)(p₀:∀i,0 ≤ g i)(H:joinV (Scree.tariff p o h) g≤ C)(t:∀ i j,‖Z i j‖≤g (tray i j)): CostOle (winJ o M h Z)≤ mintPay ((caboose*16)*C):= costmint _ _ _ (upper_far (X:=⟨(o,U),v⟩) Z g p₀ hK H t)
 have he : mintPay ((caboose*16)*c) ≤ Coffer a c:= (le_max_left ..).trans (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) hc)); have hd(i j:Single N): ‖Fock.parity ((true,i):LeanV (Single N)) {(false,j)}‖=1:=by simp [Fock.parity]
 constructor
 · let Z:= siphon X 0; change CostOle (Shorten m (winJ o M h Z) -0) ≤ _; have hc:Shorten m (winJ o M h Z)-0= Shorten m (winJ o M h Z):= sub_zero (Shorten m (winJ o M h Z)); rw [hc]; refine (Short_N m _).trans ((hb g Z c (fun i=> (u i).nonneg) hk (fun i j=>?_)).trans he); unfold Z; rw [congrFun (siphon_t X i j) (0:tangD N),norm_mul,hd, one_mul]; exact (u _).value --- tune name & reduc
 have hz(i:ComG)(p₀:‖i‖ ≤ 1/50): ‖deskC p n o U i‖≤ a:= (manor_v p o U n v _ (formC_life i o p p₀)).trans hv
 have hb₀(x y:tangD N)(p₀:‖x‖≤a)(p':‖y‖≤a): ‖iteratedFDeriv ℝ 2 (captain X ∅) 0 ![x,y]‖ ≤ Coffer a c:=by
    let V:=iteratedFDeriv ℝ 2 (captain X ∅) 0; apply le_trans (V.le_opNorm ![x,y]); have he: ‖V‖≤ c:=by
       apply ((u ∅).norm_le 2 (by decide)).trans; apply le_trans _ hk; let F(i:Finset (Dwell N)):= tariff p o h i*g i; apply le_trans (b:=F ∅); unfold F; simp [Scree.tariff,endL]; exact (single_le_sum (s:=univ) (f:=F) (fun i _=> mul_nonneg (show 0≤tariff p o h i from (by unfold Scree.tariff; positivity)) (u i).nonneg) (mem_univ ∅)) -- tune arguments
    rw [Fin.prod_univ_two]; exact (mul_le_mul he (mul_le_mul p₀ p' (norm_nonneg _) hp) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc).trans ((show c*(a*a)=a^2*c from by ring).le.trans (le_add_of_nonneg_right ((mT_non _ (mul_nonneg (mul_nonneg cab_pos.le (by positivity)) hc)).trans (le_max_left ..))))
 constructor
 · intro i a b v g; unfold book_zero; rw [sub_zero]; exact hb₀ _ _ (hz a v) (hz b g)
 intro i j v₁; constructor
 · intro k w; unfold book_zero; rw [sub_zero]; exact hb₀ _ _ (hz j v₁) ((manor_v _ _ _ _ v _ (formT_life k o p w)).trans hv)
 let y:= deskC p n o U j; let B:= fderiv ℝ (siphon X) 0 y; let F:= fun i:Finset (Dwell N)=> a*g i; have he: joinV (Scree.tariff p o h) F ≤a*c:=by rw [show joinV (Scree.tariff p o h) F= a*joinV (Scree.tariff p o h) g from ?_]; exact mul_le_mul_of_nonneg_left hk hp; unfold joinV; rw [mul_sum]; apply sum_congr rfl; intro j _; exact mul_left_comm _ _ _ -- tune
 change ‖(winJ o M h B).1-0‖≤_; rw [sub_zero]; refine (odeG ..).trans ((hb F B _ (fun j=>mul_nonneg hp (u j).nonneg) he (fun i d=>?_)).trans ((le_max_right ..).trans (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) hc)))) -- parse
 have hh:=frameSpin X ht i d (fun _:Fin 1=>y) (by decide); let t:= tray i d; change ‖B i d‖ ≤_; unfold B; simp only [iteratedFDeriv_one_apply] at hh; rw [hh,norm_mul,hd,one_mul]
 let Uκ:= fderiv ℝ (captain X t) 0; have hξ:‖Uκ‖≤ g t:=by unfold Uκ; rw [←norm_iteratedFDeriv_one]; exact (u _).norm_le _ (by omega)
 exact (Uκ.le_opNorm y).trans ((mul_le_mul hξ (hz _ v₁) (norm_nonneg _) (u _).nonneg).trans_eq (mul_comm ..)) -- tune
omit u hk
variable (wk: Woody 6 X 0 g)
include wk hk
lemma peepers: HeadX m X p o U M h n book_zero (Coffer a ((Nat.factorial 6:ℝ)*c)):=by
 let G(i):=(Nat.factorial 6:ℝ)*g i; refine appraised G (fun i=> (wk.haveP i).pay) v ?_ hK hv; refine (le_trans (b:=(Nat.factorial 6:ℝ)*joinV (Scree.tariff p o h) g) (le_of_eq ?_) (mul_le_mul_of_nonneg_left hk (by positivity))); unfold joinV; rw [mul_sum]; exact sum_congr rfl (fun i _=> mul_left_comm _ _ _)
end
end YM.CF.Oath
end
