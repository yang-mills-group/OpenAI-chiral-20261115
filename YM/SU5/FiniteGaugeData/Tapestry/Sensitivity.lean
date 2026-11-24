import YM.SU5.FiniteGaugeData.Tapestry.Thinnings
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra

/-!
# Joint sensitivity at one level, operator norm statements and unit price

`tapReader` on the indicated paid entries (kick, observing level reached) is a
continuous *linear* functional on the local test space. We don't need positivity
of it even for scalar squared input words, let alone for the output of full
product transport. All other values of tapReader (as with `coupon`) are clipped
to zero. We state the participation hypotheses where needed and also give the
claims directly in terms of sharp.
-/
set_option quotPrecheck false
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill

section
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable (S:Finset Cover)(s i k:ℕ)
local notation "K"=> tent Y H
local notation "Ω"=> side Y i s
local notation "E'"=> Journey.compass Y i k s
local notation "τ"=> (Y.voyage i).CapeT s
local notation "ν"=> ((Y.voyage i).X (Y.uv k)).gram s

abbrev Pay := ((Y.voyage i).kick ≤ k ∧ s≤Y.uv k)
variable {f g:Mark Ω}(p:Pay Y s i k)
local notation "Z"=> Y.each_level i k s p.1 p.2

lemma plusReader {f g: Mark (side Y i s)} (x:Envelope f) (y:Envelope g) (h:Pay Y s i k) : Journey.compass Y i k s (f+g) = Journey.compass Y i k s f + Journey.compass Y i k s g := by
  unfold Journey.compass; rw [mark_add ((Y.voyage i).ownership s).paid.bill x y (Marks.can_read _ _ ν τ (Y.each_level i k s h.1 h.2)), add_div]
lemma scaleReader (x:ℂ)(f:Mark Ω) : E' (x • f)=x • E' f:=by unfold Journey.compass; rw [mark_smul,mul_div_assoc]; rfl
lemma oneReader (p:Pay Y s i k) : E' 1=1:=by unfold Journey.compass; rw [markvac]; exact div_self ((Y.each_level i k s p.1 p.2)).valid

lemma actualize (f:Swatch S): E' (present Y H s i S f)= Journey.sharp Y H s i k (render S K f) := by rw [actualRead,present_exhibit]
def tapLine : Swatch S →ₗ[ℂ] ℂ where
  toFun x:= Journey.compass Y i k s (present Y H s i S x)
  map_add' x y:= by rw [map_add]; exact plusReader Y s i k (presented Y H s i S _).env (presented Y H s i S _).env p
  map_smul' z x:= by rw [map_smul,scaleReader]; rfl

include p
lemma tapLine_rate (x:Swatch S): ‖tapLine Y H S s i k p x‖≤ (spread S*Real.exp (Y.debt s*sites Ω))*‖x‖:=by
  let U:= present Y H s i S x; let D:= spread S; let g:= denZ ν Λ.U τ
  have he': E' U= markedRead U τ (ratioField Λ.V ν τ Λ.U) := Marks.normalized Λ.V Λ.U _ _ (U ∘ drawn τ)
  change ‖E' U‖ ≤ _; rw [he']; unfold markedRead
  let C:= Real.exp (Y.debt s*sites Ω)
  apply (norm_integral_le_of_norm_le_const (C:=D*C*‖x‖) (μ:=city Ω) ?_).trans_eq
  · simp [C,D]
  refine Filter.Eventually.of_forall fun i'=>?_ ; change ‖letterRead (U (drawn τ i')) ((ratioField Λ.V ν τ Λ.U) _)‖ ≤ _ -- tune
  apply (mark_bound ..).trans
  refine (mul_le_mul (present_bound Y H s i S x _) ((Z).rate i') (norm_nonneg _) (mul_nonneg (by unfold spread; positivity) (norm_nonneg _))).trans_eq ?_
  unfold Course.debt Course.charge C D; ring -- he for β notation tune

omit p
def tapReader : Swatch S →L[ℂ] ℂ := if p:Pay Y s i k then (tapLine Y H S s i k p).mkContinuous _ (tapLine_rate Y H S s i k p) else 0
lemma tapReader_compass(f: Swatch S)(p:Pay Y s i k): tapReader Y H S s i k f= E' (present Y H s i S f):=by unfold tapReader; rw [dif_pos p]; rfl
lemma tapReader_sharp(f:Swatch S)(p:Pay Y s i k): tapReader Y H S s i k f=Journey.sharp Y H s i k (render S K f):=(tapReader_compass Y H S s i k f p).trans (actualize ..)

lemma late_bound : ∃ C:ℝ,0≤C∧ ∀ᶠ k in atTop, ∀ i:ℕ,∀ f:Swatch S, ‖tapReader Y H S s i k f‖ ≤ C*‖f‖:=by
  obtain ⟨D,p,T⟩:= library Y H S s; refine ⟨D*spread S,by unfold spread; positivity,T.mono fun k v i f=>?_⟩
  by_cases h:Pay Y s i k
  · rw [tapReader_compass Y H S s i k f h,mul_assoc]; exact v i h.1 _ (presented Y H s i S _) _ (present_bound Y H s i S f)
  unfold tapReader; rw [dif_neg h]; simp; unfold spread; positivity

variable {a b:ℕ→ℕ} {I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}
variable {L:Rack Λ l}{B:Clay Λ l} (X:Exhibition Y H a b I E L B)

-- give prices for any `Universal`? only Exhibition. Use Universe limits.
namespace Exhibition
lemma Pay.ge {s t:ℕ} (h:Pay Y t i k)(p:s≤t): Pay Y s i k:=⟨h.1,p.trans h.2⟩
include X
lemma sharper : ∀ᶠ k in atTop, Pay Y s i (b k):=(X.univ_.pick.grow_k.tendsto_atTop.eventually (eventualPairIdx Y s i)).mono fun i t=> ⟨t.1,t.2.le⟩
lemma pointRow (f:Swatch S): Tendsto (fun k=>tapReader Y H S s i (b k) f) atTop (𝓝 (I s (render S K f) i)) := by
  let h:= X.univ_.together s _ (show TestFamily K true (render S K f) from ⟨⟨S, texture ..⟩,by simp⟩)
  exact (h.inner i).congr' ((X.sharper Y H s i).mono fun k p=> (tapReader_sharp Y H S s i (b k) f p).symm) -- tune

def rowₗ : Swatch S →ₗ[ℂ] ℂ where
  toFun x:= I s (render S K x) i
  map_add' x y:= tendsto_nhds_unique (pointRow Y H S s i X (x+y)) (((pointRow Y H S s i X x).add (pointRow Y H S s i X y)).congr fun k=> (map_add (tapReader Y H S s i (b k)) x y).symm)
  map_smul' z x:= tendsto_nhds_unique (pointRow Y H S s i X (z • x)) (((pointRow Y H S s i X x).const_smul z).congr fun k=> (map_smul (tapReader Y H S s i (b k)) z x).symm) -- arguments
lemma row_rate (x:Swatch S) : ‖rowₗ Y H S s i X x‖ ≤ (late_bound Y H S s).choose * ‖x‖ := le_of_tendsto (pointRow Y H S s i X x).norm ((X.univ_.pick.grow_k.tendsto_atTop.eventually (late_bound Y H S s).choose_spec.2).mono fun k h=> h i x)
def rowsRead : Swatch S →L[ℂ] ℂ := (rowₗ Y H S s i X).mkContinuous _ (row_rate Y H S s i X)
lemma pointIR (x:Swatch S): Tendsto (fun i : ℕ => rowsRead Y H S s (a i) X x) atTop (𝓝 (E s (render S K x))) := (X.univ_.together s _ (show TestFamily K true (render S K x) from ⟨⟨S,texture ..⟩,by simp⟩)).periods

def lobeₗ : Swatch S →ₗ[ℂ] ℂ where
  toFun x:= E s (render S K x)
  map_add' x y:= tendsto_nhds_unique (pointIR Y H S s X (x+y)) (((pointIR Y H S s X x).add (pointIR Y H S s X y)).congr fun k=> (map_add (rowsRead Y H S s (a k) X) x y).symm)
  map_smul' z x:=tendsto_nhds_unique (pointIR Y H S s X (z • x)) (((pointIR Y H S s X x).const_smul z).congr fun k=> (map_smul (rowsRead Y H S s (a k) X) z x).symm)
def thermodynamic : Swatch S →L[ℂ] ℂ := (lobeₗ Y H S s X).mkContinuous ((late_bound Y H S s).choose) (fun x=> le_of_tendsto (pointIR Y H S s X x).norm (Eventually.of_forall fun i : ℕ=> row_rate Y H S s (a i) X x))
@[simp] lemma rowsRead_spec (x:Swatch S): rowsRead Y H S s i X x= I s (render S K x) i:=rfl
@[simp] lemma thermo_spec (x:Swatch S): thermodynamic Y H S s X x=E s (render S K x):=rfl
end Exhibition
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.Exhibition.thermodynamic
