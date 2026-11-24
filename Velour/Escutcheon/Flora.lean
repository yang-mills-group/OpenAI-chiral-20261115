import Velour.Organza.Nursery
import YM.SU5.FiniteGaugeData.Poin.Pole
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 2800
noncomputable section
namespace YM.OS.Semigroup
open Function Set Filter Complex Analysis MeasureTheory
open scoped NNReal ENNReal Topology BigOperators ContDiff InnerProductSpace ComplexOrder
variable {H : Hilbert} {a : Axis} (S:Semigroup H a)


open Boundary Probe
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld
open _root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin

/-- The extra data is bought by Cashable. -/
structure Livery (κ:Type) where
 Q : κ→ℝ≥0→H.Op
 Y : κ→S.Detector
 m : κ→ℕ
 G : κ→H.Op
 Ω : S.muslin
 vacE (t:ℝ≥0): S.E t Ω.val=Ω.val
 vacU (x:E4): S.unit.translation x Ω.val=Ω.val
 sewn (i:κ): S.Instates (Q i) (Y i)
 prepaid (i:κ): S.Prepaid (Q i) (m i) (G i)

lemma Livery.buy {κ:Type} (Q:κ→ℝ≥0→H.Op) (Y:κ→S.Detector)
 (Ω:S.muslin)(j:∀ t:ℝ≥0,S.E t Ω.val=Ω.val)(v:∀x:E4,M S x Ω.val=Ω.val)
 (g:∀i,S.Cashable (Q i))(h:∀i,S.Instates (Q i) (Y i)):
 ∃L:S.Livery κ,L.Q=Q ∧ L.Y=Y ∧ L.Ω=Ω:=by
 choose m G p using fun i=> S.cashed (g i)
 exact ⟨⟨Q,Y,m,G,Ω,j,v,h,p⟩,rfl,rfl,rfl⟩


local notation "R"=> S.gauze
local notation "γ"=> saucer S
local notation "D"=> S.muslin
local notation "W"=> Bench S

lemma gauze_eq_saucer : R=γ:=by
 let f:= fun u:ℝ=> Real.exp (-u) • S.E u.toNNReal
 have h: ContinuousOn f (Ioi 0):=(Real.continuous_exp.comp continuous_neg).continuousOn.smul S.contHeat
 have g: IntegrableOn f (Ioi 0):=
     (integrableOn_exp_neg_Ioi 0).mono' (h.aestronglyMeasurable measurableSet_Ioi)
       (ae_of_all _ fun u=> by
           simp only [f,norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
           exact mul_le_of_le_one_right (by positivity) (S.shrinks _))
 ext1 x
 rw [saucer_apply]
 change (ContinuousLinearMap.apply ℂ H.space x) (∫u in Ioi (0:ℝ), f u)=_
 rw [←(ContinuousLinearMap.apply ℂ H.space x).integral_comp_comm g]
 rfl


def toBench (y:D): W:= ⟨y.val,by
  exact (bench S _).2 fun n=>⟨(S.weight n y).val,
     show (γ ^ n) _ = _ from by rw [← S.gauze_eq_saucer, weight_cancel]⟩⟩

lemma toBench_pay (n:ℕ)(y:D): S.toBench (S.weight n y)=hill S n (S.toBench y):=by
 apply Subtype.ext
 change (S.weight n y).val=hall S n _
 apply cache_I S n
 rw [releases,Cache,←S.gauze_eq_saucer,weight_cancel]
 rfl
lemma shop_toBench(X:H.Op)(m:ℕ)(f:Test4)(y:D):
 S.toBench (S.hatch X m f y)=ℑ S X f m (S.toBench y):=by
 change S.toBench (S.weight m (S.labelled _ _ _))= hill S m (ℑ₀ S X f _)
 rw [S.toBench_pay]
 congr 1
 apply Subtype.ext
 change (S.rasp _ _ (S.weight m y).val)=valise S _ _ (hill S m _).val
 rw [←S.toBench_pay]
 rfl

variable {S}{κ:Type} (L:S.Livery κ){n:ℕ}(u:Fin n→κ)
namespace Livery
local notation "Ω"=> L.Ω
local notation "Y"=> L.Y
local notation "F"=> L.G
local notation "v"=> L.m

def brim (f:Fin n→Test4):ℂ :=
 inner ℂ (Ω).val (( ((Each n).map (fun i=>Y (u i) (f i))).prod) Ω).val

lemma hatched (x:κ): Y x=S.hatch (F x) (v x):=
 (L.sewn x).common (S.hatch_welcome (L.prepaid x)) Filter.EventuallyEq.rfl
lemma panel_join (z:S.muslin)(f:Fin n→Test4):
 Rail (panels S (F ∘ u) (v ∘ u) f) (Omit S) (S.toBench z)=
 S.toBench ((((Each n).map (fun i=>Y (u i) (f i))).prod) z):=by
 induction n  with
 | zero=>rfl
 | succ n ih=>
   have h:s1 n (Omit S)=1:=by cases n <;> simp only [s1P,s1S]
   rw [Rail_step,h,mul_one,show Each (n+1)= _ from List.finRange_succ]
   rw [List.map_cons,List.prod_cons,List.map_map]

   let g:=Fin.tail u; let t:=Fin.tail f
   -- use Module.End.mul_apply on Rail? Bench is LinearMap composition monoid≡Module.End
   change ℑ S (F (u 0)) (f 0) (v (u 0))
     ((Rail (panels S (F ∘ g) (v ∘ g) t) (Omit S)) (S.toBench z))
    =S.toBench (Y (u 0) (f 0) ((((Each n).map fun i=>Y (g i) (t i)).prod) z))
   rw [hatched,shop_toBench]
   exact congrArg _ (ih (Fin.tail u) (Fin.tail f))


lemma maps_traverse (f:Fin n→Test4)(A:ℕ→Bin n H.Op)
 (p:Solution S (v ∘ u) A):
 Tendsto (fun i=>∫x,concert S (Ω).val (Ω).val (F ∘ u) (A i) f x)
  atTop (𝓝 (L.brim u f)):=by
 have q:=traverse S (F ∘ u) (v ∘ u) (S.toBench Ω) f A p
     (show saucer S (S.toBench Ω).val=_ from still S _ L.vacE)
 rw [L.panel_join u] at q; exact q

lemma recaps (b:Cross a) (A:Shelf S b)(α β:ℕ→Fin n→ℂ)
 (p:∀i,Radial (α i) (β i))(q:∀x,Tendsto (fun i=> α i x) atTop (𝓝 0))
 (w:∀x,Tendsto (fun i=> β i x) atTop (𝓝 0))
 (f:Fin n→Test4) :
 Tendsto (fun i=>∫x,concert S (Ω).val (Ω).val (F ∘ u)
       (_root_.YM.CF.Buffered.Afterglow.Hierarchy.Seld.Poin.rise S b A (α i) (β i) (v ∘ u)) f x)
  atTop (𝓝 (L.brim u f)):=L.maps_traverse u _ _ (rise_g S b A _ α β p q w)
#print axioms recaps

