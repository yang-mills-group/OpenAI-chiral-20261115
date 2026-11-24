import YM.SU5.FiniteGaugeData.Tapestry.Pinnacles
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 520000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
open Nacre Mir Phase RP
open Altitude
open PiTensorProduct (tprod)

/-!
# Physical locations for the resolution-indexed Euclidean algebra

Use the gauge lattice as in the scaffold. Choose physical unit so the gauge
spacing at level 0 is one (the terminal level and x, fixed once for the whole
construction); this means one fermion grid step there is two; `nodeC` includes
the offset. NO cutoff-partner price is changing the test's spacing underneath
our state. Comparing locations across j is by physical scale. Need the buffer
of `reserve` for the positivity applications (work with this whole-buffer
algebra at each participating resolution). NOT claiming additivity from arbitrarily
small subregions at fixed resolution, continuity in the mesh, or that changing
the buffer is immaterial at fixed resolution. Supplying one genuine cross-level
local net of test algebras. B sends each site's data to data which fit in the
scaled shield. This is compatible with the uniform statements, including source
& target supports *fixed* in Cover. For `keep V`, where V is any marked region,
every point/bond in the supported argument has its buffer included as here.
(Support read by tail+head, hence bond can be between two such sites, included
in these neighborhoods; not adding another full bond to the stencil.)
-/
set_option quotPrecheck false
abbrev RSpace := Axis → ℝ
-- provide separate coord dimension lemma and units.
theorem fourCoordinates : Fintype.card Axis=4:=by simp [Axis]
section
open Heat
variable (Λ:Preparation) (l:ℕ)(s:ℕ)
abbrev precisionAt : ℝ := (Λ.R.L.val:ℝ)^s
abbrev markZ (s:ℕ)(x:ℤ) :ℝ:= x/precisionAt Λ s
lemma positiveScale : 0<precisionAt Λ s:=by unfold precisionAt; positivity
lemma markUp (x:ℤ) : markZ Λ (s+1) (Scaled Λ x)=markZ Λ s x:= by
  have he : 0 < (Λ.R.L.val:ℝ):= by positivity
  unfold markZ precisionAt Scaled; push_cast; rw [pow_succ']; field_simp

def shield (x:Cover) : Set RSpace:= {u | ∀ i:Axis, |(precisionAt Λ s)*u i - x i| ≤ (reserve Λ l:ℝ)}
abbrev printedHere (S: Finset Cover) (V: Set RSpace) : Prop:=∀ x∈ S, shield Λ l s x ⊆ V
lemma treads (x:Cover) : (fun i=> markZ Λ s (x i))∈ shield Λ l s x:= by
  intro i; dsimp only; rw [markZ,mul_comm (precisionAt Λ s),div_mul_cancel₀ _ (positiveScale Λ s).ne',sub_self,abs_zero]; positivity -- order tune
lemma nodePrint (x:Cover) (i:Axis): markZ Λ s (nodeC x i)=(2*(x i:ℝ)+1)/precisionAt Λ s:=by unfold markZ nodeC; push_cast; simp

lemma unionPrinted (S T:Finset Cover) (V:Set RSpace)(p:printedHere Λ l s S V)(q:printedHere Λ l s T V): printedHere Λ l s (S∪T) V:=fun x h=>(mem_union.mp h).elim (p x) (q x)
variable (K:Calibration)(wide:Bool) (V: Set RSpace)
-- support at gauge points affine basis scaled, cartesian frames.
def keep : Subalgebra ℂ (Dome K) where
 carrier:={f|∃ S:Finset Cover, f∈ bay K S wide ∧ printedHere Λ l s S V }
 mul_mem' {x y} p q:= by obtain ⟨S,p,q'⟩:=p; obtain ⟨T,a,b⟩:=q; exact ⟨S∪T, (bay K _ wide).mul_mem (tallerBay K S wide subset_union_left p) (tallerBay K T wide subset_union_right a),unionPrinted Λ l s S T V q' b⟩
 add_mem' {x y} p q:= by obtain ⟨S,p,q'⟩:=p; obtain ⟨T,a,b⟩:=q; exact ⟨S∪T, (bay K _ wide).add_mem (tallerBay K S wide subset_union_left p) (tallerBay K T wide subset_union_right a),unionPrinted Λ l s S T V q' b⟩
 zero_mem':= ⟨∅,(bay K ∅ wide).zero_mem,by simp [printedHere]⟩
 one_mem':= ⟨∅,(bay K ∅ wide).one_mem,by simp [printedHere]⟩
 algebraMap_mem':= fun z => ⟨∅,(bay K ∅ wide).algebraMap_mem z,by simp [printedHere]⟩
lemma keeps {x:Dome K}: x∈keep Λ l s K wide V ↔ ∃ S:Finset Cover,x∈bay K S wide∧ printedHere Λ l s S V := Iff.rfl
lemma rooms {W:Set RSpace}(h:V⊆W): keep Λ l s K wide V≤ keep Λ l s K wide W:= fun f ⟨S,p,q⟩=> ⟨S,p,fun x hx=>Set.Subset.trans (q x hx) h⟩
lemma access : keep Λ l s K wide V ≤ keep Λ l s K true V:= fun f ⟨S,p,q⟩=> ⟨S,widerBay K S wide p,q⟩
lemma keepsScreen : keep Λ l s K wide V ≤ vestibule K wide:= fun x ⟨S,t,p⟩=> ⟨S,t⟩
lemma fullKeep : keep Λ l s K wide Set.univ = vestibule K wide:= le_antisymm (keepsScreen ..) (fun f ⟨S,h⟩=> ⟨S,h,fun x hx=> Set.subset_univ _⟩)

-- explicitly Euclidean physical cube
abbrev cabin (Z:ℝ) : Set RSpace:= {v|∀ i,|v i|≤ Z}
lemma fundCabin(S:Finset Cover): ∀ᶠ n:ℕ in atTop, printedHere Λ l s S (cabin n):= by
 refine (eventually_all_finset S).mpr (fun x p=>?_)
 let z:= precisionAt Λ s; let r:ℝ:= reserve Λ l; have he : 0<z:=positiveScale Λ s
 let c (i:Axis):ℝ:=(r+|(x i:ℝ)|)/z; have h:∀ᶠ n:ℕ in atTop,∀ i:Axis,c i≤(n:ℝ):= Filter.eventually_all.mpr fun i=>tendsto_natCast_atTop_atTop.eventually_ge_atTop (c i)
 refine h.mono fun i v y q j=> le_trans ?_ (v j)
 rw [show c j=(r+|(x j:ℝ)|)/z from rfl, le_div_iff₀ he, mul_comm,← abs_of_pos he, ← abs_mul]; exact ((abs_add_le (z*y j-(x j:ℝ)) (x j:ℝ))) |> fun h=> by rw [sub_add_cancel] at h; exact h.trans (add_le_add_left (q j) _)
lemma eventuallyShelters {x: Dome K}(p:x∈vestibule K wide): ∀ᶠ n:ℕ in atTop,x∈ keep Λ l s K wide (cabin n):=by obtain ⟨S,p⟩:=p; exact (fundCabin Λ l s S).mono fun n h=> ⟨S,p,h⟩
-- Physical locality of transfer.
lemma shielding (S : Finset Cover)(p:printedHere Λ l s S V) : printedHere Λ l (s+1) (followBox (Λ:=Λ) (l:=l) S) V:=by
 intro x v; let L:= Λ.R.L.val; let r:= Λ.R.L.val*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J; let R:= reserve Λ l
 have he:R+r≤L*R:=margin_step (prepared Λ l) Λ.R.coarse
 obtain ⟨a,u,V'⟩:= mem_biUnion.mp v; obtain ⟨y,t,rfl⟩:=mem_image.mp V'; obtain ⟨b,h,rfl⟩:=mem_image.mp u
 refine Set.Subset.trans (fun c w=>?_ : shield Λ l (s+1) _ ⊆ shield Λ l s b) (p b h)
 intro i
 have W:= (show ∀ i:Axis,_ from w) i -- tune
 change |_| ≤ (R:ℝ) at W
 simp only [Pi.add_apply,nsmul_eq_mul,Pi.mul_apply, Pi.natCast_apply] at W
 replace W: |((Λ.R.L.val:ℝ)*precisionAt Λ s)*c i-((Λ.R.L.val:ℝ)*(b i:ℝ)+(y i:ℝ))| ≤R:=by unfold precisionAt; push_cast [precisionAt,pow_succ'] at W; simpa only [add_comm] using W -- tune order
 have h₀:-(r:ℝ) ≤ (y i:ℝ):= by exact_mod_cast (box_test.mp t).1 i
 have h₁:(y i:ℝ) ≤ (r:ℝ):= by exact_mod_cast (box_test.mp t).2 i
 have g:(R:ℝ)+r≤ (Λ.R.L.val:ℝ)*R:= by exact_mod_cast he
 obtain ⟨u,v⟩:= abs_le.mp W
 have hl:0 < (Λ.R.L.val:ℝ):=by positivity
 change |_| ≤ (R:ℝ); rw [abs_le]; constructor <;> nlinarith

variable (i:Axis)(z:ℤ)
lemma brought (S:Finset Cover) (p: Ledge Λ l S i z) : printedHere Λ l s S ({u:RSpace| markZ Λ s z ≤ u i}) := by -- i z vars
 intro x h a v; have hp: (z:ℝ)+reserve Λ l ≤ (x i:ℝ):=by exact_mod_cast p x h
 change markZ Λ s z ≤ _; rw [markZ,div_le_iff₀ (positiveScale ..),mul_comm]; have hx:= (abs_le.mp (v i)).1; linarith -- function v i
lemma returns (S:Finset Cover)(p:printedHere Λ l s S ({u:RSpace| markZ Λ s z≤ u i})) : Ledge Λ l S i z:=by
  intro x u; let W:RSpace:=fun j=> if j=i then markZ Λ s (x i-(reserve Λ l:ℤ)) else markZ Λ s (x j)
  have v:= treads Λ l s x; have h(i):=v i
  have hx : markZ Λ s z ≤ W i:= p x u (show W∈ shield Λ l s x from fun j=>by
    change |precisionAt Λ s* W j-_| ≤ _; by_cases he:j=i
    · subst j; unfold W; rw [if_pos rfl,markZ,mul_comm (precisionAt Λ s),div_mul_cancel₀ _ (positiveScale Λ s).ne']; change |↑(x i - (Journey.reserve Λ l:ℤ)) - (x i:ℝ)| ≤ (Journey.reserve Λ l:ℝ); rw [Int.cast_sub, Int.cast_natCast, abs_le]; constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) (reserve Λ l)]
    unfold W; rw [if_neg he]; exact v j )
  unfold W markZ at hx; rw [if_pos rfl,div_le_div_iff_of_pos_right (positiveScale Λ s)] at hx
  exact le_sub_iff_add_le.mp (by exact_mod_cast hx)

-- coarser arbitrary width; actual LiftD only on whole wide algebras `true`.
lemma roofline {Y:Course Λ (VolumeCape.Dream.Nimbus l)} {H:Real.exp 1≤Λ.x}
  {a b:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ} {L:Rack Λ l}{B:Clay Λ l}(p:Exhibition Y H a b I E L B){x:Dome (tent Y H)}(u:x∈keep Λ l s (tent Y H) wide V):
   Exhibition.liftD Y H s p x∈keep Λ l (s+1) (tent Y H) true V:=by
  obtain ⟨S,t,g⟩:= u; exact ⟨_, Exhibition.risePay Y H s S p (widerBay (tent Y H) S wide t),shielding Λ l s V S g⟩
end
end YM.CF.Buffered.Afterglow.Tapestry
#print axioms YM.CF.Buffered.Afterglow.Tapestry.roofline
#print axioms YM.CF.Buffered.Afterglow.Tapestry.nodePrint
#print axioms YM.CF.Buffered.Afterglow.Tapestry.returns
#print axioms YM.CF.Buffered.Afterglow.Tapestry.eventuallyShelters
