import SatinThinJetlag
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance
variable (i k:ℕ) {P' V: Side} {f r v m a:ℕ}
local notation "L"=>P.R.L
local notation "B"=> P.block
local notation "D"=> P.K.j
local notation "VO"=> Y.voyage i
local notation "Ω" s:max => side Y i s
local notation "Gξ" s:max=> Vale.apt (Y.ir i) P.block P.R.L s
/- Actual-path Lease of Parliament: convoy and roots. Any number of supports. No stencils in cutoff budgets before size. -/
-- arithmetic delivery & Versions
local notation "XP" s:max=> RootBook Y i k s
local notation:max "SZ" s:max=> (VO).CapeT s
/- Parliament finances. -/
variable {I:Type} [Fintype I] [LinearOrder I]
local notation:max "Rn" s:max=> slotFee P s
local notation "Ξ"=> Article I
local notation "Υ"=> Key (Article I)
local notation "ΞM"=>List (Article I)
-- first downward power. `Loyalty` reports exact density on the SAME sharp tape.
variable (o:I→Site (side Y i f))
local notation "Ƶ" s:max=> morning Y i k s
local notation "Πξ" p:max=>upRoot Y i p
local notation "Ξν" s:max =>nightSet Y i s (I:=I)
local notation "ΞV" s:max=> rideSet Y i s (I:=I)
local notation:max "flightY" p:max=>convoy Y i k p
local notation "µ" s:max=> city (Ω s)
variable {E:nightSet (I:=I) Y i f}{F:rideSet (I:=I) Y i f}
variable (p:f≤v)
local notation "ψξ"=> artwork Y i k E F
local notation "ϕ" b:max=> principal Y i k p b
local notation "δ" s:max=> mark_cost Y i k s
/- Open at f with tickets independent of all positions. Match open keys in `spray`. -/
variable {u A: ℝ} 
local notation:max "αq"=> openingCost o (Rn f) (RootBook Y i k f).p
local notation "Φ"=> artwork Y i k E F
local notation "ψx"=> artwork Y i k (openTabs (RootBook Y i k f) o (slotFee P f) E) (F∘unison)
local notation "𝜔"=> Orbit (side Y i f)
local notation:max "Rτ" l:max z:max=> (artwork Y i k E F l z)
-- spent keys as List I (only a gap usage can spend). w/spare rule tests ensure existing prefix accum. `S` opener works on both even if mixed.
local notation:max "mt" s:max l:max=> chapterRead (E:=E) (F:=F) Y i k o s l
local notation "τ" s:max=> ((s).map (principal Y i k p u ∘ o)).prod -- hygiene s binder
local notation "Rt" s:max=> ((s).map (chamber Y i k ∘ o)).prod
local notation "Qt" s:max=> ((s).map ((convoy Y i k p) ∘ chamber Y i k ∘ o)).prod
local notation:max "αt"=> stageInset Y i k o p u
local notation "χ" s:max=> ((s).map (stageInset Y i k o p u)).prod
variable (U:Loyalty Y i k o p u E F)(v':v≤ Y.uv k)(x:(Y.voyage i).kick ≤ k) (z:Beyond P ℓ o 12)
local notation:max "principal_row" s:max=> principal Y i k p u (o s)
-- commute P with ALL in operand
lemma center_compass (F:Mark (side Y i v))(j:I): Commute (principal_row j) F:=route_scalar ..
lemma root_owns (i':I): AtSupport false univ (principal_row i' ):=(route_owns Y _ _ _ u _).mono (subset_univ _)
include v' x in
lemma stageSet (j:Ξ): AtSupport false univ (αt j):=by
 unfold stageInset; split; exact root_owns ..
 rename_i ht; let q:= chamber Y i k (o (QuadClock.host j)); let Q':= flightY p q
 have hv:= convoy_all Y i k x p v' ((chamber_bill Y i k (o (QuadClock.host j))).mono (subset_univ _))
 rw [sub_eq_add_neg]; exact (root_owns ..).addM ((neg_one_smul ℂ Q') ▸ (hv.smulM (-1))) -- ambiguity ..
lemma stage0 (j:I): αt (Prin j)=principal_row j:=by unfold stageInset; simp only [show layer (Prin j)=0 from rfl,ite_true]; rfl
lemma stage1 (j:I) : αt (Astr j)=principal_row j - convoy Y i k p (chamber Y i k (o j)):=by unfold stageInset; simp only [if_neg (show layer (Astr j)≠0 from by show (1:Fin 2)≠0; decide)]; rfl
-- spent costs
include x v'
lemma budget_cross (j:I) : AtSupport false univ (convoy Y i k p (chamber Y i k (o j))):= convoy_all Y i k x p v' ((chamber_bill Y i k (o j)).mono (subset_univ _))
-- separate list acc qualification instead of requiring Append/disjoint; keeps order. (acc lists may even overlap for documented lemma; only gap to gain uses them.)
def Joined (l:ΞM)(s:List I):Prop := (s++l.map QuadClock.host).Nodup
include z U
lemma volume_flight (l:ΞM)(s c:List I)(κ:Joined l s)(κ':Joined l c) : markedRead (Rt c) (SZ f) (mt s l)= mark_cost Y i k v ((Qt c * τ s)*χ l):=by
 induction l generalizing s c with
 | nil=>
    rw [show mt s []= Φ (s.map Prin) from funext fun x=>by simp [chapterRead,QuadClock.spray],U.grant s (by simpa [Joined] using κ) (Rt c) (receipt_word (F:=chamber Y i k ∘ o) (fun i=>chamber_bill Y _ _ (o i)) _ (fun i _=> subset_univ _))]; rw [List.map_nil,List.prod_nil,mul_one]; rw [convoy_product Y i k o (chamber Y i k ∘ o) x p v' z (fun j=> chamber_bill Y _ _ (o j)) c (by simpa [Joined] using κ')] -- parameters order p x? 
 | cons j l ih=>
    refine art_fork (p:=fun j=> Joined (j::l) s→ Joined (j::l) c→ markedRead (Rt c) (SZ f) (mt s (j::l))= mark_cost Y i k v ((Qt c*τ s)*χ (j::l))) ?_ ?_ j κ κ'
    · intro j hc hw; rw [chapter_term0]; specialize ih (s++[j]) c (enrol l j s hc).2 (enrol l j c hw).1; rw [ih]; apply congrArg; rw [List.map_append,List.prod_append,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one,List.map_cons,List.prod_cons,stage0 Y i k o p]; simp only [Function.comp_apply]; noncomm_ring -- Commute across Qt? because Qt c * τ s * + P(j) ok
    intro j hs ht
    let X':= τ s; let G':=Qt c; let H':= Rt c; let L_:Mark (side Y i v):= χ l; let Pj:=principal_row j; let Cj:= convoy Y i k p (chamber Y i k (o j))
    have h:= enrol l j s hs; have h':=enrol l j c ht; let P':=morning_safe Y i k x v'
    let Rκ:= chapter_sky (u:=u) Y i k o p U s l h.1; let Rχ:= chapter_sky Y i k o p U (s++[j]) l h.2
    have h1:AtSupport false univ G':=receipt_word (fun j=>budget_cross Y i k o p v' x j) _ (fun _ _=>Finset.Subset.refl _)
    have h2:AtSupport false univ X':=receipt_word (fun i' => root_owns Y i k o p (u:=u) i') s (fun _ _=>Finset.Subset.refl _)
    let h3:= (Yoke.BudgetSum Y i (f:=v) αt (fun j=> stageSet Y i k o p (u:=u) v' x j) l)
    have comm:Commute X' Cj:=by -- cannot with Cj non-pure? X' product. use Commute Prod
       suffices he: ∀ v:List I, Commute (τ v) Cj from he s
       intro v; induction v with|nil=>exact Commute.one_left _|cons i v j'=> exact Commute.mul_left (center_compass _ _ _ _ _ _ _) j' -- params
    rw [chapter_term1,ring_plus Y i _ (receipt_word (F:= chamber Y i k ∘ o) (S:= (univ:Support (More (Ω f)))) (fun j=> chamber_bill Y i k (o j)) c (fun _ _=>subset_univ _)).env (multV (a:=-1) (prodV (fee_safe Y i k (o j)) Rκ)) Rχ, ring_scale Y i, ring_toll Y i k (o j), show ((Rt c)*chamber Y i k (o j)) = Rt (c++[j]) from ?_, ih s (c++[j]) h.1 h'.2, ih (s++[j]) c h.2 h'.1, List.map_append,List.prod_append,List.map_append,List.prod_append]; swap; · simp only [List.map_append,List.map_cons,List.map_nil,List.prod_append,List.prod_cons,List.prod_nil,mul_one]; rfl
    rw [List.map_cons,List.prod_cons,List.map_cons,List.prod_cons,List.map_cons,List.prod_cons,stage1 Y i k o p]; simp only [List.map_nil,List.prod_nil,mul_one];
    change (-1:ℂ) • mark_cost Y i k v (((G'* Cj)* X') *L_)+ mark_cost Y i k v ((G'*(X'*Pj))*L_)=mark_cost Y i k v ((G'*X')*((Pj-Cj)*L_))
    -- ordering commutation only at THIS point
    let a:=(((G'* Cj)* X') *L_); let b':=(G'*(X'*Pj))*L_; have ht':a= G'*X'*Cj *L_:=by unfold a; rw [mul_assoc G',←comm.eq,mul_assoc G' X' Cj]
    rw [show ((G'*X')*((Pj-Cj)*L_)) =( (-1:ℂ) • a)+ b' from (by rw [neg_one_smul,ht']; unfold b'; noncomm_ring)]; change _ = markedRead _ _ _; rw [palm_plus (f:=v) Y i _ ?_ ?_ P',palm_scale Y i]
    exact (((h1.mulM (budget_cross Y i k o p v' x j)).mulM h2|>.mulM h3).smulM _).env
    exact ((h1.mulM (h2.mulM (root_owns Y i k o p j))).mulM h3).env
#print axioms volume_flight
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
