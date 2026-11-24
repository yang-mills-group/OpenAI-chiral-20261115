import YM.CF.Vp929.Contour.Accounts
import YM.CF.Vp929.Contour.Ascent
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Py.Rate
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate
open Forge Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Vow Salt
open Ione Beau Haro Cascade
open scoped Mew
open Mew
variable {X Y:Type*}{n:Side}{P:BudgetPoint}{h v w:ℝ}{F:RegBudget n}{K:ForceBudget n}{t:Cusp n}
open Pressure
open Ascent Wray Jet
open Display (regPrice markPrice Fink Rink)
-- use pointwise hypotheses on all configs; weak outside payment sets.
variable [NormedAddCommGroup Y][NormedSpace ℂ Y]
abbrev Glimpses : Looks (X→Y):= fun S f=> ∀ x, Holo S (fun z=> ((f z).1 x, (f z).2 x))
abbrev Dues (p:BudgetPoint)(t:Scree.Hub n)(h:ℝ) : Book (InkD n):=fun x=> PressB p t x h
abbrev ForceDues (p:BudgetPoint)(t:Force n)(h:ℝ) : Book (Copy n):=fun x=> ForceB p t x h
abbrev MedalDues (p:BudgetPoint)(X T:Support (More n))(h:ℝ): Book (Copy n):=fun x=> Medal p X T x h
variable (t₀:Scree.Hub n) (t':Force n)(T D:Support (More n))(u:1≤ h)
local notation "D'"=> Finset (Dwell n)

private lemma esteem [Sub X] (c:Book X)(w:Looks X)(T:Set (Pane n))(hr:IsOpen T)(A:X→ Pane n→ℂ)(V:Pane n)(v: V∈T)(e:ℝ)(h:0<e)(B:Finset (Bond (More n))) (k:ℕ)(K:∀ C:ℝ,∃ b:ℝ,0≤ b ∧ ∀ x,c x C→ ∀ V∈ T, Allows k (recur B e (A x) V) 0 b)(p:∀ x y, A (x-y)=A x-A y)(pL:∀ S f,w S f→∀ U,Holo S (fun z=> (A (f z).1 U,A (f z).2 U)))(i:ℕ)(g:i≤k)(l:Fin i→ tangD n)(p':ℂ→L[ℝ]ℝ): (fun x=> p' (iteratedFDeriv ℝ i (recur B e (A x) V) 0 l))∈accounts c w := by
 refine ⟨fun x y t u=>?_ ,fun S f t=>?_ ⟩
 · obtain ⟨v',z⟩:= t; obtain ⟨t',z'⟩:= u; have hh u t g':= (K t).choose_spec.2 u g' V v; rw [p,show recur B e (A x-A y) V=recur B e (A x) V-recur B e (A y) V from rfl, iteratedFDeriv_sub_apply ((hh _ _ z).smooth.of_le (by exact_mod_cast g)) ((hh _ _ z').smooth.of_le (by exact_mod_cast g))]; exact map_sub ..
 obtain ⟨hs,t,C,r⟩:= t; obtain ⟨b,hb,q⟩:= K C; exact (sureHolo hr V v h hb k (fun z hz u t=>⟨q _ (r _ hz).1 u t,q _ (r _ hz).2 u t⟩) hs (fun x _=> pL _ _ t x) i g l).form hs p'
-- projected forces indeed cost at appointed tests. embark
include u
private lemma spend (o:Seat n)(D: Finset (Dwell n)→ℝ)(p:0≤ D)(j:D')(s:(∑ j:D',Scree.tariff P o h j * D j) ≤ v): D j ≤ v:= by
 have hx(i:D'):1≤Scree.tariff P o h i:= by unfold Scree.tariff; apply one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_add_of_nonneg_right (by positivity))) (one_le_pow₀ u)
 exact (le_mul_of_one_le_left (p j) (hx j)).trans ((single_le_sum (f:=fun i=> Scree.tariff P o h i*D i) (fun i _=> mul_nonneg (zero_le_one.trans (hx i)) (p i)) (mem_univ j)).trans s)
private lemma buyer (o:Scree.Hub n)(V:InkD n)(w:PressB P o V h v)(i:D')(U:Pane n)(g:pingS P.threshold o.val.2 U): Signs P o.val.1 (fun x:tangD n=> crumb (V (increment U x)).val i) |v|:= by obtain ⟨D,t,p,r⟩:=w.worth; let W:=p _ g i; exact ⟨abs_nonneg _,W.paid,fun i p d q=>(W.token i p d q).trans ((spend u _ _ t _ r).trans (le_abs_self _))⟩
local notation "Ψ" x:max T:max U:max=> recur univ 1 (chipV x ∘ T) U
omit u
lemma whole_chart (U:Pane n)(T:InkD n)(x:D'): Ψ x T U= fun y:tangD n=> crumb (T (increment U y)).val x:=by
 funext y; rw [recur, one_smul,gyrate,comp_apply, comp_apply,show Forge.wakeB univ y=y from funext fun i=> by rw [steadyB,if_pos (mem_univ _)]]; rfl
include u
-- public jet grant all paid orders
lemma registered (V:Pane n)(p:pingS P.threshold t₀.val.2 V)(i:D')(j:ℕ)(t:j≤P.order)(l:Fin j→ tangD n)(g:ℂ→L[ℝ]ℝ): (fun T:InkD n=> g (iteratedFDeriv ℝ j (fun y:tangD n=>crumb (T (increment V y)).val i) 0 l))∈ accounts (Dues P t₀ h) Glimpses:= by
 have ht:∀ c:ℝ,∃ b:ℝ,0≤b∧∀ x:InkD n,Dues P t₀ h x c → ∀ U∈ Rink P t₀.val.2, Allows P.order (Ψ i x U) 0 b:= fun v=> ⟨composeCost P.order |v| ‖Prism.silo P t₀.val.1‖,by unfold composeCost; positivity,fun x l u' k=> by rw [whole_chart]; exact Rue.price_s (buyer u _ _ l i u' k)⟩
 simp_rw [←whole_chart (n:=n)]; exact esteem _ _ _ ping_o (fun F=>chipV i ∘ F) V p 1 zero_lt_one univ _ ht (fun a b=> funext (fun V=> map_sub ..)) (fun S f u V=> (u V).probe (chipV i)) j t l g
lemma registerPass : Portfolio (Dues P t₀ h) Glimpses := Display.rolls t₀ (zero_lt_one.trans_le u) (fun V p=> registered t₀ u V p)
private lemma forced (o:Force n)(V: Copy n)(w: ForceB P o V h v)(i:D')(U:Orbit n)(g: U∈ Fink P (o.val.1.val.2\o.val.2)): Signs P o.val.1.val.1 (fun x:tangD n=> crumb (V (increment U.1 (openG P o.val.2 x),U.2)).val i) |v|:= by obtain ⟨D,t,p,r⟩:=w.costP; let W:=p _ g i; exact ⟨abs_nonneg _,W.paid,fun i p d q=>(W.token i p d q).trans ((spend u _ _ t _ r).trans (le_abs_self _))⟩
local notation "W'" x:max T:max U:max=> chipV x (T U)
local notation "ΦF" x:max T:max U:max=> (fun y:Pane n=> W' x T (y,U))
omit u
lemma rare_chart (U:Orbit n)(J:Force n)(T:Copy n)(x:D'): recur (unrest J.val.2 P.B) 1 (fun y:Pane n=> chipV x (T (y,U.2))) U.1= fun d:tangD n=> crumb (T (increment U.1 (openG P J.val.2 d),U.2)).val x:=by
 funext y; rw [recur,one_smul,gyrate,comp_apply,padP]; rfl
include u
lemma recordRare : markPrice (accounts (ForceDues P t' h) Glimpses) id P (Fink P (t'.val.1.val.2 \ t'.val.2)) (fun U d => increment U.1 (openG P t'.val.2 d)):= by
 intro U p i j t v g; let X:=t'.val.1.val.2\ t'.val.2; let Pq:=Rink P X; let o:=t'.val.1.val.1; let b:= unrest t'.val.2 P.B
 have ht:∀ c:ℝ,∃ C:ℝ,0≤C∧∀ x: Copy n,ForceDues P t' h x c → ∀ U'∈ Pq, Allows P.order (recur b 1 (ΦF i x U.2) U') 0 C:=by
    intro c; refine ⟨composeCost P.order |c| ‖Prism.silo P o‖,by unfold composeCost; positivity,fun x l y k=>?_ ⟩; exact rare_chart (P:=P) (y,U.2) t' x i |>.symm ▸ Rue.price_s (forced u _ _ l i (y,U.2) k)
 simp only [id_eq]; simp_rw [←rare_chart (P:=P)]; exact esteem _ _ Pq ping_o _ U.1 p 1 zero_lt_one _ _ ht (fun a b=> funext (fun V=> map_sub ..)) (fun S f u V=> (u (V,U.2)).probe (chipV i)) j t v g
lemma registerForce : Portfolio (ForceDues P t' h) Glimpses:=Display.rarest t' (zero_lt_one.trans_le u) (recordRare t' u)
lemma recordPrize (Q:Support (More n))(p:D ⊆ Q): markPrice (accounts (MedalDues P T D h) Glimpses) id P (Fink P (T \ D)) (fun U d=> pressQ P Q U.1 d) := by
 intro U t i j g w v; let L:= Rink P (T \D); let b:= unrest Q P.B
 have ht:∀ c:ℝ,∃ C:ℝ,0≤C ∧ ∀ x:Copy n,MedalDues P T D h x c → ∀ V∈ L,Allows P.order (recur b P.threshold (ΦF i x U.2) V) 0 C:= by
    intro c; refine ⟨P.order.factorial*|c|,by positivity,fun x l y k=>?_ ⟩; obtain ⟨_,S,H,y',r⟩:= l; have hK(e:D'):1 ≤ stake h e:= one_le_pow₀ u
    apply ((y' (y,U.2) k p).haveP i).pay.mono; refine mul_le_mul_of_nonneg_left ?_ (by positivity); exact (le_mul_of_one_le_left (H i) (hK i)).trans (((single_le_sum (f:=fun i=> stake h i*S i) (fun j _=> mul_nonneg (zero_le_one.trans (hK j)) (H j)) (mem_univ i)).trans r).trans (le_abs_self _))
 exact esteem _ _ L ping_o _ U.1 t P.threshold P.threshold_pos _ _ ht (fun a b=> funext (fun V=> map_sub ..)) (fun S f u V=> (u (V,U.2)).probe (chipV i)) j g w v
lemma registerPrize : Portfolio (MedalDues P T D h) Glimpses:= Display.award T D (zero_lt_one.trans_le u) (recordPrize T D u)
end YM.CF.Py.Rate
