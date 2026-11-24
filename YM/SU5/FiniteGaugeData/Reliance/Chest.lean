import YM.SU5.FiniteGaugeData.Reliance.RoofLight
/-! # Actual local high-level curvature/rarity estimate

Weights detect any failure on ">= f Θ", even on the shrunk fraction of `cap` paid threshold,
or absent ≥ with complementary strict. Uniform in supplied mixed chiral insertion at
this native observing level; no claim of independence from other levels. Deliver showing as BRANE
on the proposed Cen. Not a ratio comparison postulating a regularized witness. -/
set_option autoImplicit false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Reliance
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal Classical
attribute [local instance] opCStarAlgebra
open Concord
open Py Py.Rate LocalLimit Preparation
open Afterglow Afterglow.Sound Afterglow.Satin Afterglow.Journey
namespace ShortWave
section probes
variable {K: Calibration}(s:Finset (Face ℤ))(t:ℝ) {n : Side}

def restsOn (S: Finset Cover) :=∀ x∈s,(visits x.1 (square x.2.val.1 x.2.val.2)).toFinset⊆ S
lemma restsC {S:Finset Cover}(p:restsOn s S)(x:Face ℤ)(v:x∈s) : x.1∈S:=by apply p x v; simp [visits,square]
-- cost if offending event at actual Fields, test function includes indicators by scalar

def crowded (V:LinksC) :=∃ f∈ s,t ≤ SU.group.chord (faceValue V f)

def suspend (x:PairsC):ℂ:= if crowded s t x.1 then 1 else 0

lemma toll {S:Finset Cover}(p:restsOn s S) : Coeff true S (suspend s t):=by
 let Y(x:Face ℤ)(z:PairsC) := SU.group.chord (faceValue z.1 x); have he : MeasurableSet {x:PairsC| crowded s t x.1}:=by
   have h:{x:PairsC| crowded s t x.1}= ⋃ i∈ (s:Set (Face ℤ)), Y i ⁻¹' Set.Ici t:=by ext x; simp [Y,crowded]; -- t
   rw [h]; apply MeasurableSet.biUnion s.countable_toSet; intro i k; exact (SU.group.continuous_chord.comp ((continuous_travel _ _).comp continuous_fst)).measurable measurableSet_Ici
 refine ⟨by simp, ⟨measurable_const.piecewise he measurable_const,1,fun i=>?_⟩,?_⟩
 · unfold suspend; split_ifs <;> simp
 rintro x y a _; suffices h:crowded s t x.1 ↔ crowded s t y.1 by simp only [suspend,h]
 apply exists_congr; intro i; by_cases h:i∈s; swap; · simp [h]
 simp only [h, true_and]; rw [show faceValue x.1 i=faceValue y.1 i from ?_]; apply travel_local i.1 (square i.2.val.1 i.2.val.2) x.1 y.1
 exact fun k v t=> a k (p i h (List.mem_toFinset.mpr v)) (p i h (List.mem_toFinset.mpr t))
-- wrap actual face, can assert equality all periods, no need nonwrapping for inequality.
lemma tile_face (V:Pane n)(p:Face ℤ) : faceValue (onC n V) p=faceValue V (wrap (More n) p.1,p.2) :=by unfold onC faceValue; rw [travel_at]; simp
lemma toll_clamp {S:Finset Cover}(p:restsOn s S) : scalar K (suspend s t)∈ junior K:= also K (InTest.seed (toll s t p))
def ablate (K:Calibration){S:Finset Cover}(p:restsOn s S):junior K:=⟨scalar K (suspend s t), toll_clamp s t p⟩
lemma clamp_pay {S:Finset Cover}(p:restsOn s S): ablate s t K p∈ club K S:= InTest.seed (toll s t p)
lemma cast_toll {S:Finset Cover}(p:restsOn s S)(x:Fields (K.c n)) : (ablate s t K p).val n x= if crowded s t (onC _ x.1) then 1 else 0:=by change (if crowded s t (onC _ x.1) then (1:ℂ) else 0) • (1:Fock.FC _)=_; split_ifs <;> simp
lemma toll_sing {S:Finset Cover}(p:restsOn s S): ablate s t K p∈ singlets K:=by
 intro m g x; have he : (simultaneous g x).1= Lattice.gauge g x.1:=rfl
 change (ablate s t K p).val m _=twist _ ((ablate s t K p).val m _); simp_rw [cast_toll,crowded,he,tile_face, face_gauge, Gauge.chord_conj]; split_ifs <;> simp

def extinguish (r t c:ℝ):= c*Real.exp (-(signs⁻¹*(r*t)))

lemma reimbursed {r c:ℝ}{S:Finset Cover}(p:restsOn s S){x:junior K}(e:0 ≤ r)(h:0 ≤ c)(q:∀ i, ‖x.val n i‖ ≤ c): Apt r (extinguish r t c) (region S (K.c n)) ((ablate s t K p*x).val n):=by
 intro i; change ‖(ablate s t K p).val n i * x.val n i‖≤_; rw [cast_toll s t p]; split_ifs with u; swap; · rw [zero_mul,norm_zero]; exact mul_nonneg (mul_nonneg h (Real.exp_pos _).le) (Real.exp_pos _).le
 rw [one_mul]; obtain ⟨v,a,b⟩:=u; rw [tile_face] at b; let M:= K.c n; let z:Face (Per (More M)):= (wrap (More M) v.1,v.2); have hz: z.1∈ region S M:= mem_image_of_mem _ (restsC s p v a)
 let L:=glow r (region S M) i.1; have ht: signs⁻¹*(r*t) ≤ L:=(lobe_paid r z i.1 (region S M) e hz).trans' (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left b e) (inv_nonneg.mpr signs_pos.le))
 unfold extinguish; rw [mul_assoc c,←Real.exp_add]; apply (q i).trans; exact le_mul_of_one_le_right h (Real.one_le_exp (by linarith only [ht])) -- t ellipse
end probes

variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ P.x)(PQ:Cashbox P)(m:ℕ){s n d:ℕ} {i k:ℕ→ℕ}
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{A:Playhouse P l} -- mistake A P
local notation "Q"=> tent Y H
local notation "Xs" s:max=> hat P.R.L P.x s
local notation "Z"=>magnified (tent Y H) (grossC Y PQ) m
local notation "U" s:max=>Universum.slope P s
variable (W: Traced Y H i k F E A)
include PQ W
-- arbitrarily many faces for unit-height input; `m` is width
lemma soot {c t:ℝ} (v:0 ≤ c) (s:ℕ)(T:Finset (Face ℤ))(S:Finset Cover)(p:restsOn T S)(h:occupy S m) (x:junior Q)(u : x∈club Q S)(w:∀ᶠ n:Side in atTop,∀ i, ‖x.val n i‖ ≤ c):
    ‖E s (ablate T t Q p*x).val‖ ≤ extinguish (Universum.slope P s) t c * Z :=
 stamped Y H PQ s m W S ((club Q S).mul_mem (clamp_pay T t p) u) h (w.mono (fun n i=> reimbursed T t p (Universum.slope_n P s PQ).le v i))

omit PQ W
end ShortWave
end YM.CF.Buffered.Reliance
#print axioms YM.CF.Buffered.Reliance.ShortWave.soot
#print axioms YM.CF.Buffered.Reliance.ShortWave.toll_sing
