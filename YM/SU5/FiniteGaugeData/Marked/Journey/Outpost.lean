import YM.SU5.FiniteGaugeData.Marked.Journey.Praise

/-!
# Direct FiniteGaugeData dictionary. One sequence of actual cutoffs, after each of the
actual period-specific finance gates, then one sequence of periods. Works
simultaneously on all j, without requiring *any* cross-torus equality of
couplings, `takes/Allowed`, pressure broadcasts or Gluing hypotheses;
works on the released `Audit1102` data. Includes diagonal readings along
legacy period^5 cone on these selected sequences (not every sufficiently
large period and cutoff), at each fixed level. Doesn't rule out multiple
subsequential values.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Journey
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py.Rate Py.Rate.LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1 ≤ Λ.x) (s i k:ℕ)
local notation "K"=>tent Y h

structure Universal (j k:ℕ→ℕ)(I:ℕ→Family (tent Y h)→ℕ→ℂ)(E:ℕ→Family (tent Y h)→ℂ): Prop where
  pick : Cabinet Y h j k
  together (s f)(p:TestFamily (tent Y h) true f):
    Couplet j k (fun m n=>sharp Y h s m n f) (I s f) (E s f) (fun p=>∀ᶠ n in atTop,legacy Y (j n) (k (p n)))
  gaugeMatter (s:ℕ): E s 1=1 ∧ ∀ n:ℕ,∀ F:Fin n→eligible (tent Y h) true,
    (Matrix.of fun i j=> E s (thetaK (tent Y h) (F i).val*(F j).val)).PosSemidef
lemma canvassed {j k:ℕ→ℕ}(p:Cabinet Y h j k): Universal Y h j k (fun s=>p.field Y h s) (fun s=> p.audience Y h s):=⟨p,fun s _ x=> (p.booked Y h s x).2,fun s=> ⟨p.unitA Y h s,fun _ F=> p.matrix Y h s F⟩⟩

/-- Same thinned course sequences for all tests, all levels s.
`prepared`/`Usable` grants preserved. No use of any `Printed`. -/
theorem daybreak (ε:ℝ) :
    ∃ (Λ:Preparation)(l:ℕ), ε < Λ.x ∧ Λ.nominated (VolumeCape.Dream.Nimbus l) ∧
      ∃ (h:Real.exp 1 ≤ Λ.x),∃ (Y : Course Λ (VolumeCape.Dream.Nimbus l)),
        (∃ z, Usable (D:=Λ.δ) Λ.V Λ.W Λ.J Λ.N0 z Λ.delay Y.meter) ∧
        (∀ i k, ((Y.voyage i).X k).Prepared Λ.P Λ.delay) ∧
        (∀ i j:ℕ, Advance.LoomLaw ((Y.voyage i).CapeT j) (YM.SU5.FiniteGaugeData.Audit1102.lawRadius (VolumeCape.Dream.plot l).C)) ∧
        ∃ u π:ℕ→ℕ, StrictMono u ∧ StrictMono π ∧ Nonempty (Y.Query u π) ∧
          ∃ i k I E, StrictMono i ∧ StrictMono k ∧ Universal Y h (u∘i) (π∘k) I E:= by
  obtain ⟨Λ,l,v,H',Y,m,p,c,u,π,g,h,x⟩:=Py.Rate.Audit1102.same_physical_history (max ε (Real.exp 1))
  have ht:= lt_of_le_of_lt (le_max_left ..) v; have hx:Real.exp 1 ≤ Λ.x:= le_trans (le_max_right ..) v.le
  refine ⟨Λ,l,ht,H',hx,Y,m,p,c,u,π,g,h,x,?_⟩
  obtain ⟨i,k,G,c',w,v'⟩:= exist_excerpt Y hx u π g h (fun _ _=>True) (fun _=>Filter.Eventually.of_forall fun _=> trivial)
  let P:Cabinet Y hx (u ∘ i) (π ∘ k):=⟨g.comp G,h.comp c',fun a b p=> (w a b p).1,v'⟩
  exact ⟨i,k,_,_,G,c',canvassed Y hx P⟩

-- recording reading-preserving resolution embedding of cover marks, reflection and AP conventions. `Family (tent ..)`
-- is only a way of talking about the cover expression used at observing s;
-- transported to actual scale by `send`. Check equality also in primitives.
private lemma relay{n m:Side}(p:n=m)(f g:Mark n)(b:ℂ)(x:PairsC→ℂ)(y:Cover)(i:SpinIdx)(k:SU.Slot)(a:Axis)(z:ℤ):
    let V(F:Mark n):Mark m:= p ▸ F
    V (f+g)=V f+V g ∧ V (b • g)=b • V g ∧ V (f*g)=V f*V g ∧ V 1=1 ∧ V (reflMark a z g)=reflMark a z (V g) ∧
    V (fun w=>x (Prod.map (onC n) (onC n) w) • 1)=(fun w=> x (Prod.map (onC m) (onC m) w) • 1) ∧
    V (fun _=>Fock.create (basisC n y i k))=(fun _=>Fock.create (basisC m y i k)) ∧
    V (fun _=>Fock.remove (basisC n y i k))=(fun _=>Fock.remove (basisC m y i k)):=by subst n; tauto

lemma transformed (f g:Family K)(b:ℂ)(x:PairsC→ℂ)(y:Cover)(a:SpinIdx)(k:SU.Slot):
    let n:=momentm Y i s; let t:=side Y i s; let V(F:Family (tent Y h)):= send Y h i s (F n)
    V (f+g)=V f+V g ∧ V (b • g)=b • V g ∧ V (f*g)=V f*V g ∧ V 1=1 ∧ V (thetaK (tent Y h) g)=reflMark 3 ((tent Y h).plane0) (V g) ∧
    V (scalar (tent Y h) x)=(fun w=> x (Prod.map (onC t) (onC t) w) • 1) ∧
    V (creation (tent Y h) y a k)=(fun _=>Fock.create (basisC t y a k)) ∧ V (removal (tent Y h) y a k)=(fun _=> Fock.remove (basisC t y a k)) := by intro n t V; exact relay (terrain Y h (Y.ir i) s) (f n) (g n) b x y a k 3 _

end YM.CF.Buffered.Afterglow.Journey
#print axioms YM.CF.Buffered.Afterglow.Journey.daybreak
