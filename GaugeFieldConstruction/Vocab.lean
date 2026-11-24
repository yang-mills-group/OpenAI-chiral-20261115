import GaugeFieldConstruction.MarvelT
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
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
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h:ℝ}(o:Seat n)(M: Male)
open Spectrix
abbrev Glamor (G:Genre)(V:ℝ):Set (Paper n):= {F|∃ (M:Male)(p: BudgetPoint)(W:Waves)(h:ℝ), p.power ≤3∧p.order ≤6∧G.Room W∧0<h∧ ‖W‖≤V∧ F= G.coinB p h • bushMoon M o p h W}
private lemma toll_s (n:Side): Ť n=((Fintype.card (Sweep n):ℝ)⁻¹:ℝ):=by unfold Ť; push_cast; rfl -- issue RHS equality implicit coerces?
lemma curtainZ(r:Sweep n)(k:ℝ)(V: Paper n):Barber r (k • V)=k • Barber r V:=by
 rw [← Complex.coe_smul,born_P,show payZ r (k:ℂ) = (k:ℂ) from ?_, Complex.coe_smul]; unfold payZ cSignX; split; · simp
 rfl
private def curtainL(r:Sweep n):Paper n→ₗ[ℝ]Paper n:= {toFun:= fun V=> Barber r V,map_add':=fun V W=> born_Z .., map_smul':=fun k V=>curtainZ ..}
lemma Glamor_f (G:Genre)(V:ℝ)(w:300<n.val): Odious (Glamor o G V):=by
 let Y(r:Sweep n):Seat n:= sh r⁻¹ o; let I:= Sweep n; let ξ:=tilos*V; let L:= (Fintype.card I:ℝ)⁻¹; let χSC(r:I): Set (Paper n):= {F|∃ f∈ coat_A (Y r) G ξ, F= L • Barber r f}
 have hp(r:I): Odious (χSC r):=by
    apply Od_L (L • curtainL r) (fun i p=>?_) (wool (Y r) G ξ (by omega)); obtain ⟨i,z,t⟩:=p; exact ⟨i,z,t.symm⟩ -- tune
 refine Od_total univ χSC (fun i _=>hp i) ?_; rintro j ⟨M,p,W,h,p0,p1,v,s,g,rfl⟩; let S:= G.coinB p h; let U(r:I):= S • Bush (Y r) M p h (Mason r⁻¹ W)
 refine ⟨fun i=> L • Barber i (U i),fun i _=>⟨U i,⟨Mason i⁻¹ W,p,M,h,(sheen_norm ..).trans (mul_le_mul_of_nonneg_left g (abs_nonneg _)), Genre.trans_B _ _ v,p0,p1,s,rfl⟩,rfl⟩,?_⟩
 unfold bushMoon; rw [toll_s,Complex.coe_smul,smul_comm,smul_sum,smul_sum]; apply sum_congr rfl; intro i _; exact congrArg (L • ·) (curtainZ i S (Bush (Y i) M p h (Mason i⁻¹ W))).symm -- tune
variable {o}
lemma Glamor_votes {V:ℝ}{G:Genre}(p:F∈ Glamor o G V)(w:300<n.val): ∃ (p:BudgetPoint)(h t:ℝ), 0<h∧ p.power≤3∧ p.order≤6∧ TrackD p (Pach o) h F t∧ portable F∧ Tuned F:=by
 obtain ⟨M,p,W,h,p0,p1,r,h2,v,rfl⟩:=p; let K:= G.coinB p h; rw [← Complex.coe_smul]; obtain ⟨x,y,m⟩:= ray_B (o:=o) M W w h2 p0 p1 0; exact ⟨p,h, _, h2,p0,p1,track_h x (↑K),port_m y _, tuning_h (ray_V M _ (by omega) h2 p0 p1) _⟩
abbrev Solon (G:Genre)(F:Paper n): Prop:= match G with
| .gauge=> (∀ i:Pairs n,F (some i)=0) ∧F none 1=0
| .pure => F none=0
| .mixed=> F none=0∧∀ i, F i 1=0
lemma S0(G:Genre): Solon G (0:Paper n):=by cases G<;>simp [Solon]
lemma S2(G:Genre)(p:Solon G F)(u:Solon G H):Solon G (F+H):=by
 cases G with
 | gauge=> refine ⟨fun i=>?_,?_⟩; rw [Pi.add_apply,p.1,u.1,add_zero]; rw [Pi.add_apply,Pi.add_apply,p.2,u.2,add_zero]
 | pure=> change (F+H) none=0; rw [Pi.add_apply,p,u,add_zero]
 | mixed=> refine ⟨?_,fun i=>?_⟩; rw [Pi.add_apply,p.1,u.1,add_zero]; rw [Pi.add_apply,Pi.add_apply,p.2,u.2,add_zero]
lemma Sξ(G:Genre)(p:Solon G F)(a:ℝ): Solon G (a • F):=by
 cases G with
 | gauge=> refine ⟨fun i=>?_,?_⟩; rw [Pi.smul_apply,p.1,smul_zero]; rw [Pi.smul_apply,Pi.smul_apply,p.2,smul_zero]
 | pure=> change (a • F) none=0; rw [Pi.smul_apply,p,smul_zero]
 | mixed=> refine ⟨?_,fun i=>?_⟩; rw [Pi.smul_apply,p.1,smul_zero]; rw [Pi.smul_apply,Pi.smul_apply,p.2,smul_zero]
lemma Ssum(G:Genre){I:Type}[DecidableEq I](T:Finset I)(F:I→Paper n)(p:∀ i∈T,Solon G (F i)): Solon G (∑ i∈T,F i):=by induction T using Finset.induction_on with|empty=>rw [sum_empty]; apply S0|@insert i T H ih=>rw [sum_insert H]; exact S2 G (p i (mem_insert_self ..)) (ih fun i l=>p _ (mem_insert_of_mem l))
lemma Beam (G:Genre)(s:Solon G F)(p:Sweep n): Solon G (Barber p F):=by
 let Y:= Barber p F; have h(V:Pane n)(z): Y z (flashA p V)=∑ i:Wa n, boostX (launchZ p) (Typer p) i z* payZ p (F i V):=by rw [show Y _ _=_ from congrFun (boothK F p V) z,stripeQ]; rfl
 have hp(V:Pane n): Y none (flashA p V)= payZ p (F none V):=congrFun (boothK F p V) none -- tune
 have hv(g:F none=0): Y none=0:= funext fun i=>by nth_rw 1 [←goS p i]; rw [hp,g]; exact pay_i ..
 cases G
 · exact hv s
 · refine ⟨hv s.1,fun i=> ?_⟩; change Y i _= _; nth_rw 1 [← Facet.glacial n p]; rw [h]; apply sum_eq_zero; intro i _; rw [s.2,pay_i,mul_zero]
 refine ⟨fun i=>?_,?_⟩
 · change Y _=_; funext V; nth_rw 1 [←goS p V]; rw [h]; apply sum_eq_zero; intro i _; cases i; exact zero_mul _; rw [s.1,Pi.zero_apply,pay_i,mul_zero]; -- maybe rfl
 change Y none _=0; nth_rw 1 [← Facet.glacial n p]; rw [hp,s.2,pay_i]
lemma bud_E (G:Genre)(W:Waves)(u:G.Room W)(t:0<h)(P:p.power ≤3)(L:p.order≤6)(w:20<n.val): Solon G (Bush o M p h W):=by
 unfold Bush; cases G with
 | gauge=> rw [busF_nil o M u.1 p t.ne' w,busG_nil o M W u t P L w,add_zero,add_zero]; refine ⟨fun i=> by simp [busC,Silex,isolate],?_⟩; change terrace _ _ _ _= _; apply ψ_flat
 | mixed=>
    rw [busC_nil o M u.1 u.2.1,busF_nil o M u.2.2 _ t.ne' w,zero_add,zero_add]; unfold busG; apply Ssum; intro i _; let A:=αGuide o M p W h; let F:=beamer o neutralK (mallet o A p i) h; have he:F 1=0:=by ext j k; unfold F beamer; rw [Layout.tide_p]; simp [modelK,carryU,seed_k]
    change Solon .mixed (plac F true); refine ⟨rfl,fun z=>?_⟩; rcases z with _|⟨b,j,k⟩; rfl; cases b <;> simp [plac,he]
 | pure=>
    rw [busC_nil o M u.1 u.2.1,zero_add]; apply S2
    · unfold busF Pyl; apply Ssum; intro i _; rfl
    unfold busG; apply Ssum; intro i _; rfl -- tune
lemma Glamor_S (w:300<n.val)(V:Genre)(x:ℝ)(F:Paper n)(p:F∈ Glamor o V x): Solon V F:=by
 obtain ⟨M,p,W,h,h0,h1,r,t,y,rfl⟩:=p; apply Sξ; rw [bushMoon,toll_s, Complex.coe_smul]; apply Sξ; apply Ssum; intro i _; exact Beam V (bud_E M _ (Mason i⁻¹ W) (Genre.trans_B _ _ r) t h0 h1 (by omega)) _ -- tune
end ArtCart
end MastTin
end YM.CF.XGarden
end
