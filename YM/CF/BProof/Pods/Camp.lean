import YM.CF.BProof.Pods.Manual

/- product fibers in B. exact House state. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
noncomputable section
namespace YM.CF.BProof.Pods.Brick
open Function Filter MeasureTheory Relation Finset RG Law
open Lattice Prox Grid Angular Angular.Yard Release Payment Mapping
open House Cube Lat Wilson Skye Charge Gauss Garden
open scoped Topology BigOperators Classical ENNReal Hearth
variable {m N:Side}(Y:Yard (More N))(g:Ratio m (More N))(y:ℝ)
local notation "s"=> More N
local notation "B"=> Block Y m
local notation "G"=> SU.group
variable (h:xi y≤1)

abbrev PadKey : B→Type:= Pad (fun _:Y.Col=>Fin 5) (hide Y g)
abbrev lawKey : (b:B)→Measure (PadKey Y g b) := pool (fun _:Y.Col=>Fin 5) (hide Y g) (fun _=> Measure.count)
def fieldKey : ((b:B)→PadKey Y g b)≃ᵐ Manual.Key Y:=Pods.tape (fun _:Y.Col=> Fin 5) (hide Y g)
instance probKey(b:B) : IsFiniteMeasure (lawKey Y g b):= by
    unfold lawKey pool; infer_instance
lemma wetKey : MeasurePreserving (fieldKey Y g) (Measure.pi (lawKey Y g)) (Measure.count):=by
    rw [←count_pi (X:=fun _:Y.Col=> Fin 5)]
    exact wet (fun _:Y.Col=>Fin 5) (hide Y g) (fun _=> Measure.count)
abbrev PadBit : B→Type:= Pad (fun _:Y.Col=>Bool) (hide Y g)
abbrev lawBit : (b:B)→Measure (PadBit Y g b) := pool (fun _:Y.Col=>Bool) (hide Y g) (fun _=> Measure.count)
def fieldBit : ((b:B)→PadBit Y g b)≃ᵐ Manual.Cart Y:=Pods.tape (fun _:Y.Col=> Bool) (hide Y g)
instance probBit(b:B) : IsFiniteMeasure (lawBit Y g b):= by
    unfold lawBit pool; infer_instance
lemma wetBit : MeasurePreserving (fieldBit Y g) (Measure.pi (lawBit Y g)) (Measure.count):=by
    rw [←count_pi (X:=fun _:Y.Col=> Bool)]
    exact wet (fun _:Y.Col=>Bool) (hide Y g) (fun _=> Measure.count)
abbrev PadMile : B→Type:= Pad (fun _:Y.Col=>Locale.Place Y) (hide Y g)
abbrev lawMile : (b:B)→Measure (PadMile Y g b) := pool (fun _:Y.Col=>Locale.Place Y) (hide Y g) (fun _=> Pub.lobby G Y.Apt)
def fieldMile : ((b:B)→PadMile Y g b)≃ᵐ Release.Locale.House Y:=Pods.tape (fun _:Y.Col=> Locale.Place Y) (hide Y g)
instance probMile(b:B) : IsProbabilityMeasure (lawMile Y g b):= by
    unfold lawMile pool; infer_instance
lemma wetMile : MeasurePreserving (fieldMile Y g) (Measure.pi (lawMile Y g)) (Locale.lobby Y):=by
    exact wet (fun _:Y.Col=>Locale.Place Y) (hide Y g) (fun _=> Pub.lobby G Y.Apt)
abbrev PadTube : B→Type:= Pad (fun _:Y.Col=>Roll.Place Y → ℝ) (hide Y g)
abbrev lawTube : (b:B)→Measure (PadTube Y g b) := pool (fun _:Y.Col=>Roll.Place Y → ℝ) (hide Y g) (fun _=> Day.mark (hot.trunc y) (Roll.Place Y))
def fieldTube : ((b:B)→PadTube Y g b)≃ᵐ hot.Field Y:=Pods.tape (fun _:Y.Col=> Roll.Place Y → ℝ) (hide Y g)
instance probTube(b:B) : IsProbabilityMeasure (lawTube Y g y b):= by
    haveI P1 : IsProbabilityMeasure (Day.mark (hot.trunc y) (Roll.Place Y)):= Day.prob _ _ (sq_pos_of_pos (sq_pos_of_pos (coin_pos ..)))
    unfold lawTube pool; infer_instance
lemma wetTube : MeasurePreserving (fieldTube Y g) (Measure.pi (lawTube Y g y)) (pixels Y y):=by
    haveI P1 : IsProbabilityMeasure (Day.mark (hot.trunc y) (Roll.Place Y)):= Day.prob _ _ (sq_pos_of_pos (sq_pos_of_pos (coin_pos ..)))
    exact wet (fun _:Y.Col=>Roll.Place Y → ℝ) (hide Y g) (fun _=> Day.mark (hot.trunc y) (Roll.Place Y))
abbrev PadDust : B→Type:= Pad (fun _:Bond s=>SU.E) (fun x:Bond s=> addr Y g x.1)
abbrev lawDust : (b:B)→Measure (PadDust Y g b) := pool (fun _:Bond s=>SU.E) (fun x:Bond s=> addr Y g x.1) (fun _=> cloud G (xi y))
def fieldDust : ((b:B)→PadDust Y g b)≃ᵐ Config G s:=Pods.tape (fun _:Bond s=> SU.E) (fun x:Bond s=> addr Y g x.1)
include h
lemma probDust(b:B) : IsProbabilityMeasure (lawDust Y g y b):= by
    haveI P0 : IsProbabilityMeasure (cloud G (xi y)) := cloud_unit G (xi y) (coin_pos ..) h
    unfold lawDust pool; infer_instance
lemma wetDust : MeasurePreserving (fieldDust Y g) (Measure.pi (lawDust Y g y)) (Cloud s y):=by
    haveI P0 : IsProbabilityMeasure (cloud G (xi y)) := cloud_unit G (xi y) (coin_pos ..) h
    exact wet (fun _:Bond s=>SU.E) (fun x:Bond s=> addr Y g x.1) (fun _=> cloud G (xi y))
omit h
abbrev PadIds : B→Type:= Pad (fun _:Site s=>Bone N) (addr Y g)
abbrev lawIds : (b:B)→Measure (PadIds Y g b) := pool (fun _:Site s=>Bone N) (addr Y g) (fun _=> parcel N)
def fieldIds : ((b:B)→PadIds Y g b)≃ᵐ Skye.Ids N:=Pods.tape (fun _:Site s=> Bone N) (addr Y g)
instance probIds(b:B) : IsProbabilityMeasure (lawIds Y g b):= by
    unfold lawIds pool; infer_instance
lemma wetIds : MeasurePreserving (fieldIds Y g) (Measure.pi (lawIds Y g)) (depot N):=by
    exact wet (fun _:Site s=>Bone N) (addr Y g) (fun _=> parcel N)
abbrev PadY : B→Type:= Pad (fun _:Site s=>Garden.YPhase) (addr Y g)
abbrev lawY : (b:B)→Measure (PadY Y g b) := pool (fun _:Site s=>Garden.YPhase) (addr Y g) (fun _=> AddCircle.haarAddCircle)
def fieldY : ((b:B)→PadY Y g b)≃ᵐ Pollen (Site s):=Pods.tape (fun _:Site s=> Garden.YPhase) (addr Y g)
instance probY(b:B) : IsProbabilityMeasure (lawY Y g b):= by
    unfold lawY pool; infer_instance
lemma wetY : MeasurePreserving (fieldY Y g) (Measure.pi (lawY Y g)) (gold (Site s)):=by
    exact wet (fun _:Site s=>Garden.YPhase) (addr Y g) (fun _=> AddCircle.haarAddCircle)
abbrev PadZ : B→Type:= Pad (fun _:Site N=>Garden.YPhase) (addr Y g ∘ Cube.node)
abbrev lawZ : (b:B)→Measure (PadZ Y g b) := pool (fun _:Site N=>Garden.YPhase) (addr Y g ∘ Cube.node) (fun _=> AddCircle.haarAddCircle)
def fieldZ : ((b:B)→PadZ Y g b)≃ᵐ Pollen (Site N):=Pods.tape (fun _:Site N=> Garden.YPhase) (addr Y g ∘ Cube.node)
instance probZ(b:B) : IsProbabilityMeasure (lawZ Y g b):= by
    unfold lawZ pool; infer_instance
lemma wetZ : MeasurePreserving (fieldZ Y g) (Measure.pi (lawZ Y g)) (gold (Site N)):=by
    exact wet (fun _:Site N=>Garden.YPhase) (addr Y g ∘ Cube.node) (fun _=> AddCircle.haarAddCircle)
abbrev PadYZ := meet (PadY Y g) (PadZ Y g)
abbrev lawYZ := milk _ _ (lawY Y g) (lawZ Y g)
def fieldYZ : ((b:B)→PadYZ Y g b)≃ᵐ Fields N:= (divide (PadY Y g) (PadZ Y g)).trans ((fieldY Y g).prodCongr (fieldZ Y g))
instance probYZ(b:B) : IsProbabilityMeasure (lawYZ Y g b):= by
    unfold lawYZ milk; infer_instance
lemma wetYZ : MeasurePreserving (fieldYZ Y g) (Measure.pi (lawYZ Y g)) (gardenF N):=by
    exact ((wetY Y g).prod (wetZ Y g)).comp (mp_div _ _ (lawY Y g) (lawZ Y g))
abbrev PadTags := meet (PadIds Y g) (PadYZ Y g)
abbrev lawTags := milk _ _ (lawIds Y g) (lawYZ Y g)
def fieldTags : ((b:B)→PadTags Y g b)≃ᵐ Extras N:= (divide (PadIds Y g) (PadYZ Y g)).trans ((fieldIds Y g).prodCongr (fieldYZ Y g))
instance probTags(b:B) : IsProbabilityMeasure (lawTags Y g b):= by
    unfold lawTags milk; infer_instance
lemma wetTags : MeasurePreserving (fieldTags Y g) (Measure.pi (lawTags Y g)) (petals N):=by
    exact ((wetIds Y g).prod (wetYZ Y g)).comp (mp_div _ _ (lawIds Y g) (lawYZ Y g))
abbrev PadBook := meet (PadDust Y g) (PadTags Y g)
abbrev lawBook := milk _ _ (lawDust Y g y) (lawTags Y g)
def fieldBook : ((b:B)→PadBook Y g b)≃ᵐ Config G s × Extras N:= (divide (PadDust Y g) (PadTags Y g)).trans ((fieldDust Y g).prodCongr (fieldTags Y g))
include h
lemma probBook(b:B) : IsProbabilityMeasure (lawBook Y g y b):= by
    haveI pb:=probDust Y g y h
    unfold lawBook milk; infer_instance
lemma wetBook : MeasurePreserving (fieldBook Y g) (Measure.pi (lawBook Y g y)) ((Cloud s y).prod (petals N)):=by
    haveI pb:=probDust Y g y h
    exact ((wetDust Y g y h).prod (wetTags Y g)).comp (mp_div _ _ (lawDust Y g y) (lawTags Y g))
omit h
abbrev PadStream := meet (PadTube Y g) (PadBook Y g)
abbrev lawStream := milk _ _ (lawTube Y g y) (lawBook Y g y)
def fieldStream : ((b:B)→PadStream Y g b)≃ᵐ hot.Field Y × Config G s × Extras N:= (divide (PadTube Y g) (PadBook Y g)).trans ((fieldTube Y g).prodCongr (fieldBook Y g))
include h
lemma probStream(b:B) : IsProbabilityMeasure (lawStream Y g y b):= by
    haveI pb:=probBook Y g y h
    unfold lawStream milk; infer_instance
lemma wetStream : MeasurePreserving (fieldStream Y g) (Measure.pi (lawStream Y g y)) ((pixels Y y).prod ((Cloud s y).prod (petals N))):=by
    haveI pb:=probBook Y g y h
    exact ((wetTube Y g y).prod (wetBook Y g y h)).comp (mp_div _ _ (lawTube Y g y) (lawBook Y g y))
omit h
abbrev PadBits := meet (PadKey Y g) (PadBit Y g)
abbrev lawBits := milk _ _ (lawKey Y g) (lawBit Y g)
def fieldBits : ((b:B)→PadBits Y g b)≃ᵐ Manual.Marbles Y:= (divide (PadKey Y g) (PadBit Y g)).trans ((fieldKey Y g).prodCongr (fieldBit Y g))
instance probBits(b:B) : IsFiniteMeasure (lawBits Y g b):= by
    unfold lawBits milk; infer_instance
lemma wetBits : MeasurePreserving (fieldBits Y g) (Measure.pi (lawBits Y g)) ((Measure.count.prod Measure.count)):=by
    exact ((wetKey Y g).prod (wetBit Y g)).comp (mp_div _ _ (lawKey Y g) (lawBit Y g))
abbrev PadHall := meet (PadMile Y g) (PadStream Y g)
abbrev lawHall := milk _ _ (lawMile Y g) (lawStream Y g y)
def fieldHall : ((b:B)→PadHall Y g b)≃ᵐ Dish Y:= (divide (PadMile Y g) (PadStream Y g)).trans ((fieldMile Y g).prodCongr (fieldStream Y g))
include h
lemma probHall(b:B) : IsProbabilityMeasure (lawHall Y g y b):= by
    haveI pb:=probStream Y g y h
    unfold lawHall milk; infer_instance
lemma wetHall : MeasurePreserving (fieldHall Y g) (Measure.pi (lawHall Y g y)) (chase Y y):=by
    haveI pb:=probStream Y g y h
    exact ((wetMile Y g).prod (wetStream Y g y h)).comp (mp_div _ _ (lawMile Y g) (lawStream Y g y))
omit h
abbrev PadTotal := meet (PadBits Y g) (PadHall Y g)
abbrev lawTotal := milk _ _ (lawBits Y g) (lawHall Y g y)
def fieldTotal : ((b:B)→PadTotal Y g b)≃ᵐ Manual.Disney Y:= (divide (PadBits Y g) (PadHall Y g)).trans ((fieldBits Y g).prodCongr (fieldHall Y g))
include h
lemma probTotal(b:B) : IsFiniteMeasure (lawTotal Y g y b):= by
    haveI pb:=probHall Y g y h
    haveI pv(i:B): IsFiniteMeasure (lawHall Y g y i):= IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
    unfold lawTotal milk; infer_instance
lemma wetTotal : MeasurePreserving (fieldTotal Y g) (Measure.pi (lawTotal Y g y)) (Manual.name Y y):=by
    haveI pb:=probHall Y g y h
    haveI pv(i:B): IsFiniteMeasure (lawHall Y g y i):= IsZeroOrProbabilityMeasure.toIsFiniteMeasure _
    haveI ph(i:B): SigmaFinite (lawHall Y g y i) := IsFiniteMeasure.toSigmaFinite _
    exact ((wetBits Y g).prod (wetHall Y g y h)).comp (mp_div _ _ (lawBits Y g) (lawHall Y g y))
omit h
-- flatten on whole. Later use for projecting Rich frames.
def flats (x:(b:B)→PadTotal Y g b) : Sphere Y:= Manual.box Y (fieldTotal Y g x)
@[fun_prop] lemma flats_m : Measurable (flats Y g):=(Manual.box_m Y).comp (fieldTotal Y g).measurable
include h
lemma house(F:Sphere Y→ℂ)(p:Envelope F)(t:∀ x:Sphere Y,¬Manual.Marked Y x.1.mood → F x=0): (∫ x,F x ∂globe Y y) =∫ x,F (flats Y g x) ∂Measure.pi (lawTotal Y g y):= (Manual.power Y y F h p t).trans (Law.apply_pres (wetTotal Y g y h) (p.meas.comp (Manual.box_m Y))).symm
end YM.CF.BProof.Pods.Brick

