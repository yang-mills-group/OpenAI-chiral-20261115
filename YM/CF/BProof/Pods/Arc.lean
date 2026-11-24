import YM.CF.BProof.Pods.Envelope

/- default state Solar, Ready for contour tests. Need comparisons at <=I(Exc) to determine
true fields. Fresh only requires probability-one fresh everywhere. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 26000
noncomputable section
namespace YM.CF.BProof.Pods.Brick
open Function Filter MeasureTheory Relation Finset RG Law
open Lattice Prox Grid Angular Angular.Yard Release Payment Mapping
open House Cube Lat Wilson Skye Charge Gauss Garden Pricing
open Contour Contour.Season Contour.Battery Tower
open scoped Topology BigOperators Classical ENNReal Hearth
variable {m N:Side}(Y:Yard (More N))(g:Ratio m (More N))(y:ℝ)
local notation "s"=> More N
local notation "B"=> Block Y m
local notation "G"=> SU.group
variable (h:Solid y Y.short g.count.val)
instance : StandardBorelSpace SU.E:=by
 haveI : PolishSpace SU.E := by letI:= TopologicalSpace.metrizableSpaceMetric SU.E; infer_instance
 infer_instance
instance preBoren : StandardBorelSpace (Spire.Sweep N):= by letI : TopologicalSpace (Spire.Sweep N):=⊥; letI : DiscreteTopology (Spire.Sweep N) :=⟨rfl⟩; letI : BorelSpace (Spire.Sweep N):=⟨borel_eq_top_of_discrete.symm⟩; infer_instance
instance (b:B) : StandardBorelSpace (PadKey Y g b):=by unfold PadKey Pad; infer_instance
instance (b:B) : StandardBorelSpace (PadBit Y g b):=by unfold PadBit Pad; infer_instance
instance (b:B) : StandardBorelSpace (PadMile Y g b):=by unfold PadMile Pad; infer_instance
instance (b:B) : StandardBorelSpace (PadTube Y g b):=by unfold PadTube Pad; infer_instance
instance (b:B) : StandardBorelSpace (PadDust Y g b):=by unfold PadDust Pad; infer_instance
instance (b:B) : StandardBorelSpace (PadIds Y g b):=by unfold PadIds Pad; infer_instance
instance (b:B) : StandardBorelSpace (PadY Y g b):=by unfold PadY Pad; infer_instance
instance (b:B) : StandardBorelSpace (PadZ Y g b):=by unfold PadZ Pad; infer_instance
instance (b:B) : StandardBorelSpace (PadYZ Y g b):=by unfold PadYZ meet; infer_instance
instance (b:B) : StandardBorelSpace (PadTags Y g b):=by unfold PadTags meet; infer_instance
instance (b:B) : StandardBorelSpace (PadBook Y g b):=by unfold PadBook meet; infer_instance
instance (b:B) : StandardBorelSpace (PadStream Y g b):=by unfold PadStream meet; infer_instance
instance (b:B) : StandardBorelSpace (PadHall Y g b):=by unfold PadHall meet; infer_instance
instance (b:B) : StandardBorelSpace (PadBits Y g b):=by unfold PadBits meet; infer_instance
instance (b:B) : StandardBorelSpace (PadTotal Y g b):=by unfold PadTotal meet; infer_instance -- tune p
abbrev shake := buzz (PadTotal Y g) (baseC Y g y)
lemma wake_vis : Vis (shake Y g y):= buzz_m (PadTotal Y g) (baseC Y g y) (base_m Y g y)
include h
def prep : Pot (PadTotal Y g):= by letI:= probTotal Y g y h.h; exact soup _ _ _ (dawning Y g y h)
lemma acc_def(b:B): (prep Y g y h).μ b= accept _ (lawTotal Y g y) (baseC Y g y) b:=rfl
lemma exc_def(b:B): (prep Y g y h).ν b= reject _ (lawTotal Y g y) (baseC Y g y) b:=rfl
abbrev fresh(x:Pawn Y): Prop:=hot.Fares Y y x.gauss ∧ ∀ i, SU.group.chord (x.dust i)≤xi y
-- helper proof convenience ae
lemma soft_seat : ∀ᵐ x∂chase Y y,hot.Fares Y y (uncurry x.2.1)∧ ∀ i,SU.group.chord (x.2.2.1 i)≤xi y:=by
 let p:=h.h; haveI:=cloud_unit G (xi y) (coin_pos ..) p; haveI:= chase_p Y y p
 let C:=Cloud s y; let T:= C.prod (petals N); let V:=(pixels Y y).prod T; haveI:IsProbabilityMeasure C:=by unfold C Cloud; infer_instance
 haveI:IsProbabilityMeasure T:=by unfold T; infer_instance
 haveI:IsProbabilityMeasure V:=by unfold V; infer_instance
 have hv:MeasurePreserving Prod.snd (chase Y y) V:= measurePreserving_snd
 have hu:= (measurePreserving_fst (μ:=pixels Y y) (ν:=T)).comp hv
 have hp := ((measurePreserving_fst (μ:=C) (ν:=petals N)).comp (measurePreserving_snd (μ:=pixels Y y) (ν:=T))).comp hv
 have hx:∀ᵐ x∂pixels Y y, hot.Fares Y y (uncurry x) := Day.city _ _ _ (sq_pos_of_pos (sq_pos_of_pos (coin_pos ..)))
 apply Filter.Eventually.and; exact hu.quasiMeasurePreserving.tendsto_ae hx; exact hp.quasiMeasurePreserving.tendsto_ae (multicloud G _ (coin_pos ..) p) -- tune multicloud
lemma story : Solar (prep Y g y h) (shake Y g y) (fun x=>fresh Y y (flats Y g x).1) := by
 let v:=lawTotal Y g y; haveI:=probTotal Y g y h.h; let q:=shake Y g y
 have hv:∀ᵐ x∂Measure.pi v,fresh Y y (flats Y g x).1:=by
    haveI:=chase_p Y y h.h; let gg(u: Manual.Disney Y) := fresh Y y (Manual.box Y u).1; refine (wetTotal Y g y h.h).quasiMeasurePreserving.tendsto_ae (show ∀ᵐ x∂Manual.name Y y, gg x from ?_) -- shadow
    exact (Measure.quasiMeasurePreserving_snd (μ:=(Measure.count.prod Measure.count:Measure (Manual.Marbles Y))) (ν:=chase Y y)).tendsto_ae (soft_seat Y g y h) -- tune param args
 refine ⟨wake_vis Y g y,fun i=>?_ ⟩ -- Solar.makes? Structure not Prop sort? constructor
 exact (waking (PadTotal Y g) v (baseC Y g y) (base_m Y g y) (dawning Y g y h) i).and (remain _ v (baseC Y g y) (base_m Y g y) (dawning Y g y h) _ hv i)
lemma valueF(F:Sphere Y→ℂ)(p:Envelope F)(t:∀ x:Sphere Y,¬Manual.Marked Y x.1.mood → F x=0): let L:= kilo _ (lawTotal Y g y) (baseC Y g y);
                                                                                                 (∫ x,F x ∂globe Y y)= L.toReal • Battery.stock (P:=prep Y g y h) (F ∘ flats Y g):=by
 intro; rw [house Y g y h.h F p t]; letI:= probTotal Y g y h.h; exact checks (PadTotal Y g) (lawTotal Y g y) (baseC Y g y) (base_m Y g y) (dawning Y g y h) (F ∘ flats Y g) (Law.pull p (flats_m ..))
lemma value_bill : Real.exp (-(Fintype.card B:ℝ)) ≤ (kilo _ (lawTotal Y g y) (baseC Y g y)).toReal:=by
 unfold kilo; rw [ENNReal.toReal_prod]; let L(b:B):= (copper Y g y b).toReal; change _≤ ∏ b:B,L b
 have he(i:B): Real.exp (-1)≤ L i:= by refine le_trans ?_ (site_bill Y g y i h); rw [Real.exp_neg,inv_eq_one_div]; apply one_div_le_one_div_of_le (by norm_num) (by have := Real.add_one_le_exp 1; linarith)
 calc
   _ = ∏ i:B,Real.exp (-1):= (by rw [←Real.exp_sum]; simp)
   _ ≤ _:= prod_le_prod (fun i _=> (Real.exp_pos _).le) (fun i _=> he i)
end YM.CF.BProof.Pods.Brick
