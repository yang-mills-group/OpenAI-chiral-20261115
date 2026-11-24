import GaugeFieldConstruction.Mettle
import YM.CF.Roots.Seat
import SatinThinPiers
import YM.CF.Mica.Sleet
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 30000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
local notation "GS"=> SU.group
variable {n:Side}{p: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c:ℝ}
namespace Lenten
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove Moto Tap
namespace Layout
open scoped YM.CF.Mew
open HushP ModuleB Pastry Flot
namespace Fren
open Skye Levier Scroll Spire Ione
open Lattice
open ProjectorNext.Equivariance (bonds pull_increment roll pulledDirection)
-- Point root always moves by pull. x at old.
variable (s:Sweep n)(R:Signed)
open Rush
-- anchor costs on this chart.
open QuadClock Vault
-- transported stencil at finite step. fixed norm and no volume cost.
variable {A B U:InkD n}{v f r:ℝ}
lemma push_sum(S T: Sweep n) : moveHub (S*T) X= moveHub T (moveHub S X):=by
 let H: boxA (S*T)= (boxA T).trans (boxA S):= Equiv.ext (fun i=>step_V S T i); apply Subtype.ext; unfold moveHub; -- proof eq
 apply Prod.ext _ _ <;> simp only [H,Equiv.symm_trans_apply] -- tune
 ext i; simp [(boxA T).symm_apply_eq,(boxA S).symm_apply_eq] -- tune
lemma move_Φ(o:Skye.Seat n): moveHub s (Zhub o)= Zhub (sh s o):=by
 apply Subtype.ext; apply Prod.ext; · rfl
 change (Pax o).map (boxA s).symm.toEmbedding= Pax ((boxA s).symm o); rw [← sitU]; unfold Pax; rw [← paysT]; simp only [Finset.map_singleton, Equiv.toEmbedding_apply] -- tune
lemma shy_z (v:Skye.Seat n): boxA 1 v=v:=by rw [sitA]; change affine 1 ((assembly n).root 0) v=v; rw [map_zero]; simp [affine]
lemma move_1 : moveHub 1 X=X:=by
 apply Subtype.ext; have he: boxA (1: Sweep n)=Equiv.refl _:= Equiv.ext fun v=>shy_z v; unfold moveHub; simp only [he]; apply Prod.ext; · rfl
 change _= X.val.2; ext x; simp -- tune
lemma shiftback(o:Skye.Seat n): sh s⁻¹ (sh s o)=o:=by unfold sh; rw [sitU]; simp
lemma flare_i (A:Pane n) : flashA 1 A=A:=by rw [revoke]; change _∘pull 1 ((assembly n).root 0) A=A; rw [map_zero,Lattice.pull_id]; rfl
lemma flash_k (A:Pane n): flashA s⁻¹ (flashA s A)=A:=by rw [lights,mul_inv_cancel,flare_i]
lemma ride_one(c:ℂ):payZ (1:Sweep n) c=c:=by
 change cSignX (false.xor (detX 1)) c=c
 rw [show detX 1=false from ?_]; rfl
 by_contra H; have G: detX 1=true:=by cases h: detX 1; contradiction; rfl
 have he:= det_p (1:Signed) 1; rw [one_mul,G] at he; contradiction -- tune
lemma scar_y(z:ℂ)(i:Cipher n):suit_Y s (z • i) = payZ s z • suit_Y s i:=by
 apply Subtype.ext; let U:= Levier.siteU (castX s) s.charge (spinU s.charge s.s) n
 change sauce _ _ U (z • i.val)= cSignX _ z • sauce s.charge (detX s.s) U i.val; rw [sauce,singT, win_c,twist_scalar]; rfl -- tune
abbrev WakeQ(A:InkD n):InkD n:= step_F s⁻¹ A
lemma Wake_acts(A:InkD n): Turns s A (WakeQ s A):=by
 constructor; intro x; unfold WakeQ step_F; simp only [Function.comp_apply,flash_k,inv_inv]
lemma T_uni (u: Turns s A B) : B=WakeQ s A:=by
 funext i; let U:=flashA s⁻¹ i; have he: flashA s U=i:=by unfold U; rw [lights,inv_mul_cancel,flare_i]
 rw [←he,u.turns,(Wake_acts ..).turns]
lemma T_comp (t:Sweep n)(u:Turns s A B)(e:Turns t B U):Turns (s*t) A U:= ⟨fun i=>by rw [← lights,e.turns,u.turns,moon_Y]⟩ -- tune
lemma T_rev (u: Turns s A B):Turns s⁻¹ B A:=⟨fun i=>by rw [T_uni _ u]; unfold WakeQ step_F; simp only [Function.comp_apply]; rw [inv_inv,moon_Y,mul_inv_cancel,toon_Q] -- tune invinv!
 ⟩
def monoTwo(F:InkD n): Prop:= ∀ i,∀ k:Finset (Dwell n), k.card≠2→Pastry.crumb (F i).val k=0 -- tune inference
lemma ph_rankH (x:Cover)(k:lotV)(A:Pane n→Pal)(z:ℝ)(o:Skye.Seat n): monoTwo (viewW o k A z):=by
 intro i R p; apply poke_none; intro a b h; exact p (h ▸ (by simp [Haro.tray])) -- tune
lemma gauge_rankH (S:leadF Gem Gem)(G:leadF Gem Sut)(o:Skye.Seat n): sage_L (flowF o S G p)=flowF o S G p:=by
 funext i; apply pimp_Q; intro j; unfold sage_L; rw [Function.comp_apply,price_X]; split; rfl
 rename_i e; have ht:j≠∅:=fun x=>e (by rw [x,card_empty]); unfold flowF; change _= ((_ :ℂ) • (1:FC _)) j ∅; simp [ht]
lemma m2sum {J:Type}(T:Finset J)(F:J→InkD n)(u:∀ i∈T,monoTwo (F i)): monoTwo (∑ i∈T,F i):=by
 classical
 induction T using Finset.induction_on with
 | empty=> rw [sum_empty]; exact fun _ _ _=>rfl
 | @insert i T p ih=> rw [sum_insert p]; intro x k v; change crumb ((F i x).val+(((∑ i∈T,F i) x)).val) k=0; rw [crumb_add,u _ (mem_insert_self ..) x k v,ih (fun i w=>u i (mem_insert_of_mem w)) x k v, add_zero]
lemma restore(U:InkD n)(p:monoTwo U): restK U=U:=funext (fun i=> Ione.up_r (U i) (p i))
lemma spin_h (w:sage_L Q=Q)(g:0 ≤ h) (u: PressB p X Q h c) : PressB p (moveHub s X) (WakeQ s Q) h ((fare_T 0:ℝ) * (duty_Q p.order p.power*c)):=by
 have ht:PressB p (moveHub s⁻¹ (moveHub s X)) Q h c:=by rw [←push_sum,mul_inv_cancel,move_1]; exact u
 exact w ▸ swirl_x _ s⁻¹ _ _ ht g -- tune
lemma spin_p (w:monoTwo Q)(g:0≤h)(u: PressB p X Q h c):PressB p (moveHub s X) (WakeQ s Q) h ((fare_T 2:ℝ)*(duty_Q p.order p.power*c)):=by
 have ht:PressB p (moveHub s⁻¹ (moveHub s X)) Q h c:=by rw [←push_sum,mul_inv_cancel,move_1]; exact u
 have hv:=consume_F p s⁻¹ _ _ ht g; rw [restore Q w] at hv; exact hv
lemma Wake_add (F Q:InkD n): WakeQ s (F+Q)=WakeQ s F+WakeQ s Q:=by funext i; unfold WakeQ step_F; simp only [Function.comp_apply,Pi.add_apply,map_add]
lemma Wake_smul (F:InkD n)(x:ℂ): WakeQ s (x • F)= payZ s x • WakeQ s F:=by funext i; unfold WakeQ step_F; simp only [Function.comp_apply,Pi.smul_apply, inv_inv, scar_y]
variable (V: Waves)(M:Male)(o)
def Turnp(p:BudgetPoint):ℝ:= (fare_T 0:ℝ)*(duty_Q p.order p.power*suitCostH)+(fare_T 2:ℝ)*(duty_Q p.order p.power*Poid)+(fare_T 2:ℝ)*(duty_Q p.order p.power*ρzone)
lemma rent_μ (v:20<n.val)(u:p.power≤3)(w:p.order ≤6)(E:0<h): PressB p (Zhub (sh s o)) (WakeQ s (αPress o M p V h)) h (Turnp p* ‖V‖):=by
 rw [←move_Φ,αPress,Wake_add,Wake_add]; let F:=αPure o M p V h; let Z:=αMixed o M p V h; have hp:monoTwo F:=m2sum _ _ (fun i _=> ph_rankH 0 i _ _ o); have hz: monoTwo Z:=m2sum _ _ (fun i _=> ph_rankH 0 neutralK (mallet o (αGuide o M p V h) p i) h o);
 apply lift_PV (Larch.prop_add _ _ (spin_h s (gauge_rankH ..) E.le (suit_H o E V u w v)) (Larch.prop_add _ _ (spin_p s hp E.le (suit_P o M E V u w v)) (spin_p s hz E.le (suit_M o M E V u w v))))
 unfold Turnp; apply le_of_eq; ring
lemma Window_z (g:300<n.val): Nonwrapping (Pax o) o:=by
 intro i p; obtain ⟨v,p,e⟩:=halo_spec.mp p; rw [mem_singleton.mp p, separation_comm] at e; change _ < n.val*2; omega
abbrev mindChart: BudgetPoint:=⟨3,6,1,48,1,by decide,by decide,zero_lt_one,by decide,zero_lt_one,le_rfl⟩
omit o s M
lemma thought_feast (R:Signed)(b:Bool)(A:Waves): ∃ f:Waves,Thoughts R b A f:=by
 let n:Side:=⟨301,by omega⟩; let v:Waves:=A; let X:Skye.Seat n:= 0; let M:Tulip.Male:=⟨1,odd_one⟩; let s:Sweep n:=⟨R,0,b⟩; let t:= mindChart; let V:=αPress X M t A 1;
 have hd: 300 <n.val:=by change 300<301; norm_num -- tune
 have he:20<n.val:=lt_trans (by norm_num) hd; have hp: t.power ≤3:= le_rfl; have ht:t.order≤6:=le_rfl; let ζ:=brace_C X M zero_lt_one A hp ht he; -- lean inf h? maybe inferred T from hp. charge zero_lt_one meta
 have hT:=brace_M X M zero_lt_one A hp ht he; have hμ:= rent_μ (h:=1) X s A M he hp ht zero_lt_one;
 have hw: sh s X=(moveHub s (Zhub X)).val.1:=rfl; let W:= exportM (sh s X) M hμ zero_le_one rfl; have hv:=export_full (sh s X) M hμ zero_le_one rfl; refine ⟨W,?_⟩
 exact lives s M ζ (move_Φ s X|>.symm ▸ hμ) (Wake_acts ..) zero_le_one A W hT hv (lt_trans (by norm_num) hd) (Window_z X hd) -- tune
end Fren
end Layout
end Lenten
end YM.CF.TableF
end
