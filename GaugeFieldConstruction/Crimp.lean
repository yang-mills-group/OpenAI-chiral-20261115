import GaugeFieldConstruction.Khams
import GaugeFieldConstruction.Fangs
/-! graded operator shape & comparison.-/
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
open Function NormedSpace Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open Tarn Cay Slate Cour Hest
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Fief Jet Vol Rel
open Yaw Pig
open Feu Feu.Corset Haro
section
open Py Riant Lattice Prism Tap FlightFlux TableF Boom Axon Flot Taxi
open Lenten.ModuleB
open Lich.Muster
open Hake Vow Bake Rue Larch
open TableF Lenten.Bank Lenten Lenten.Layout Fren
open Frugal
open scoped YM.CF.Mew
open BellPrice PinRack
open BellPrice PinRack
open Py.Rate.Pitching.Focus
variable {I J:Type}[Fintype I][Fintype J]{N:Side}{L:Side}{P:BudgetPoint}{o:Seat N}{v h f τ μ t b:ℝ}{M:Male}{D:ℕ}
variable {H:I→Zone N}{K:J→Zone N}{V:I→Waves}{G:I→ℕ}
variable (p:Freight (P:=P) o M t μ τ h b D H G L) (hq:∀ i,G i ≤ D) (hs:0<t)(he:0≤h)(hu:0≤μ)(hy:0≤τ)(hQ:PocketL L μ τ D)
variable (bO:I→ℕ)(bP:Planaris bO ΓProj D V τ)
variable (Z:FrameK I→ₗ[ℂ]FrameK I)(e:SwitchP V o P M h t D H L G Z)
abbrev CoatP (Z:FrameK I →ₗ[ℂ] FrameK I)(L:Side)(G:I→ℕ):FrameK I→ₗ[ℂ] FrameK I where
  toFun:=fun x=>Walt L G (Z x)
  map_add':= by intro x y; funext i; unfold Walt; simp only [map_add,Pi.add_apply,mul_add]
  map_smul':=by intro a x; funext i; unfold Walt; simp only [map_smul,Pi.smul_apply]; change _*(a*_)=a*(_*_); ring
abbrev κEye (i:I) : FrameK I:= Pi.single i 1
lemma eye_r (i:I)(X:I→ Waves) : Woof (κEye i) X=X i:=by
 refine (sum_eq_single i ?_ (by simp)).trans ?_
 · intro j _ q; rw [show κEye i j=0 from Pi.single_eq_of_ne q _]; exact (show ∀{E:Type}(P:TPack E),letI:=P.G; letI:=P.S;∀ x:E,(0:ℂ) • x=0 from fun _=> (by rename_i P; letI:=P.G; letI:= P.S; intro i; exact zero_smul ..)) Packs_U _
 rw [show κEye i i=1 from Pi.single_eq_same ..]; exact @one_smul ℂ Waves _ kinnL.toDistribMulAction.toMulAction _ -- tune
lemma Walt_η (z:FrameK I): LoomK z ≤ Rateκ L 0 * LoomK (Walt L G z):=by
 unfold LoomK; rw [mul_sum]; apply sum_le_sum; intro i _; rw [ticket_pay,←mul_assoc]
 exact le_mul_of_one_le_left (norm_nonneg _) (by rw [←div_eq_mul_inv]; exact (one_le_div (Rate_pr ..)).mpr (rate_lt (show 0 ≤ G i by omega))) -- tune
lemma Walt_eng : Bijective (Walt L G):=by
 have h(w:ℂ)(i:I)(x:FrameK I)(t:Walt L G x i=w):x i= (↑(Rateκ L (G i)):ℂ)*w:=by
    have p:(↑(Rateκ L (G i)):ℂ)≠0:=by exact_mod_cast (Rate_pr L (G i)).ne'
    rw [←t]; unfold Walt; simp only [Complex.ofReal_inv]; field_simp
 refine ⟨fun a b p=> funext (fun i=> (h _ i a rfl).trans ?_),fun x=>?_⟩
 · rw [p]; exact (h _ i b rfl).symm
 refine ⟨fun i=> (↑(Rateκ L (G i)):ℂ)* x i, funext fun i=>?_⟩
 have p:(↑(Rateκ L (G i)):ℂ)≠0:=by exact_mod_cast (Rate_pr L (G i)).ne'
 unfold Walt; simp only [Complex.ofReal_inv]; field_simp
-- response holds at actual unnormalized budgets. 
abbrev PickS (Z:FrameK I→ₗ[ℂ]FrameK I)(i:I)(L:Side)(G:I→ℕ):= Walt L G (Z (κEye i))
include p hs he hu hy bP Z e hq hQ
lemma Payout (i:I) : let l:= PickS Z i L G; let q:= W_s H l; LoomK l ≤ (Rateκ L D)⁻¹*κMini L ∧ Basalt P o L.val (L.val+1) q (RamoK L/16*t) 2 (LoomK l*b) h D M ∧ CardT q (KeyUp P) M h o D=(t:ℂ) • V i:=by
 intro ℓ q
 let R:=Z (κEye i); have ht: V i=Woof R (Plug P o M h D H L G t):=(eye_r i V).symm.trans (e _)
 have hx:= CostW p hs he hu hy (V i) R ht.symm
 have hv := mul_le_mul_of_nonneg_left (bP.bounded i) (Chest_nn _ _ hu hy D)
 refine ⟨(Walt_mon _ _ hq).trans (mul_le_mul_of_nonneg_left (hx.budget.trans (hv.trans hQ.feral)) (inv_nonneg.mpr (Rate_pr ..).le)),hx.earns.sharpen ?_ (le_refl _),hx.part⟩
 exact le_trans (mul_le_mul_of_nonneg_right hv (mul_nonneg (PosW hu hy) hs.le)) (by rw [←mul_assoc _ _ t]; exact mul_le_mul_of_nonneg_right hQ.kiosk hs.le)
variable (hG:∀ j:J, Basalt P o L.val (L.val+1) (K j) (Gapμ L μ*(Rateκ L (D+1)*t)) 2 b h D M)
structure InkFr (H:I→Zone N) (K:J→Zone N)(p:BudgetPoint)(o:Seat N)(M:Tulip.Male)(D:ℕ)(V:I→Waves)(t h:ℝ) (Q:J→FrameK I) (Z:FrameK I→ₗ[ℂ]FrameK I)(L:Side)(G:I→ℕ) : Prop where
    beacon :SwitchP V o p M h t D H L G Z
    rill(j:J): Woof (Q j) V= Rate_c o p M h D (K j) t
-- exact definitions. 
abbrev PrizeP (Q:J→ FrameK I)(Z:FrameK I→ₗ[ℂ]FrameK I)(j:J)(L:Side)(G:I→ℕ):=Walt L G (Z (-Q j)) -- negative old principal. before λ
abbrev PrizeZ (U:FrameK I)(K:Zone N)(F:I→Zone N)(D:ℕ)(L:Side):= (GapGain L D:ℂ) • (K+W_s F U)
omit Z e
include hG
lemma Prize_T : ∃ Q Z, InkFr H K P o M D V t h Q Z L G:=by
 obtain ⟨Z,e⟩:= Certified_pc p hs he hu hy bO bP; have hf(i):= Gap_s hs he (hG i)
 choose H h using fun i=>bP.coframe (Rate_c o P M h D (K i) t) (hf i).2; exact ⟨H,Z,e,fun i=>(h i).symm⟩
variable (Q:J→FrameK I)(Z₀: FrameK I→ₗ[ℂ]FrameK I)(hQt: InkFr H K P o M D V t h Q Z₀ L G)
include hQt
lemma Prize_α (j:J): let A:=PrizeP Q Z₀ j L G; let F':= PrizeZ A (K j) H D L;
 LoomK (Q j)≤ LαK L (DimsP (D+1)+2*Alto)∧ LoomK A ≤ LαK L (-1+3*Alto) ∧ Basalt P o L.val (L.val+1) F' (RamoK L/16*t) 2 (GapGain L D*(b+LoomK A*b)) h D M ∧ CardT F' (KeyUp P) M h o D=0:=by
 intro A F'; obtain ⟨a,u,e⟩:= Gap_call p hs he hu hy (hG j) _ (Gap_z_ p hs he hu hy (hG j) Z₀ hQt.beacon _ (hQt.rill j)); have hp := bP.brake (Q j); rw [hQt.rill j] at hp
 exact ⟨hp.trans ((mul_le_mul_of_nonneg_left (Gap_s hs he (hG j)).1 hy).trans hQ.outset), (Walt_mon _ _ hq).trans ((mul_le_mul_of_nonneg_left a (inv_nonneg.mpr (Rate_pr ..).le)).trans hQ.pact),u.sharpen (mul_le_mul_of_nonneg_right hQ.gain hs.le) (le_refl _),e⟩
omit hQt hq hG
include Z e
-- M map actual scanner scaled
abbrev μRoad (F:FrameK I)(p:BudgetPoint)(V:I→Zone N)(o:Seat N)(M:Male)(h t:ℝ)(D:ℕ):= ((↑(t⁻¹)):ℂ) • (Woof F (fun i=>CardT (V i) (KeyUp p) M h o D))
omit p hs he hu hy bP hQ Z e
private lemma Ξt (H:Waves)(z:ℝ)(b:0<z): (↑(z⁻¹):ℂ) • (z:ℂ) • H=H:=by
 apply (show ∀{E:Type}(P:TPack E)(s v:ℂ),s*v=1→ letI:=P.G; letI:=P.S;∀ h:E,s • v • h=h from fun {_} P s v e=> (by letI:=P.G; letI:=P.S; intro h; rw [smul_smul,e,one_smul])) Packs_U
 rw [← Complex.ofReal_mul,inv_mul_cancel₀ b.ne',Complex.ofReal_one]
include p hs he hu hy bP hQ Z e
lemma M_purse : let Y:= CoatP Z L G;
 Bijective Y ∧ (∀ i: FrameK I,μRoad (Y i) P H o M h t D= Woof i V∧ LoomK i ≤ (Rateκ L 0*κMini L) * LoomK (Y i) ∧ LoomK (Z i)≤ κMini L*LoomK i ∧ LoomK i≤ κMini L* LoomK (Z i)):=by
 intro Y; obtain ⟨hY,B⟩:= InZ p hs he hu hy bO bP Z e
 refine ⟨Walt_eng.comp hY, fun i=>?_⟩
 have ht: LoomK i≤ κMini L * LoomK (Z i):=(B i).2.1.trans (mul_le_mul_of_nonneg_right hQ.visage (noLoom (Z i)))
 refine ⟨?_,ht.trans (le_trans (b:=κMini L*(Rateκ L 0*LoomK (Y i))) ?_ (le_of_eq (by ring))),(B i).1.trans (mul_le_mul_of_nonneg_right hQ.feral (noLoom i)),ht⟩; rotate_left; · exact mul_le_mul_of_nonneg_left (Walt_η _) (alpha_nnC ..).le -- tune G infer Y def
 unfold μRoad; rw [show Woof (Y i) (fun j=>CardT (H j) (KeyUp P) M h o D) = _ from wave_spend (L:=L) H _ G D h hs -- tune Wave h implicit t
     , Ξt _ _ hs]; exact (e i).symm -- tune
end
end YM.CF.Oath
end
